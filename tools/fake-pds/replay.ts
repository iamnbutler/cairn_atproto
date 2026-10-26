// Replays random sequences of calls against the Bun server (server.ts, over HTTP) and the Lean
// model (`lake exe fake-pds-model`, over JSON lines) and compares every answer: status, error,
// body (cursor and page items included), rate-limit headers, delays, timeouts and image sizes.
//
//   bun tools/fake-pds/replay.ts [--runs 4] [--steps 150] [--seed 1] [--model lean/.lake/build/bin/fake-pds-model]
//
// Each run starts its own server on a free port and its own model, and stops both (by the pids it
// started). Both sides play the same host: it keeps the `access` and `refresh` tokens a session
// reply carries, sends them back, and remembers the cursors it was given. Exit 0 iff they agreed.

import { spawn, type Subprocess } from "bun";
import { identifier, password, did, defaults, type Config } from "./model.ts";

const argv = Bun.argv;
const arg = (n: string, d: string) => { const i = argv.indexOf(`--${n}`); return i >= 0 ? argv[i + 1] : d; };
const runs = Number(arg("runs", "4"));
const steps = Number(arg("steps", "150"));
const seed0 = Number(arg("seed", "1"));
const here = import.meta.dir;
const modelExe = arg("model", `${here}/../../lean/.lake/build/bin/fake-pds-model`);
const TIMEOUT_MS = 400;

// A seeded generator for the script's choices (SplitMix64).
class Rng {
  s: bigint;
  constructor(seed: number) { this.s = BigInt(seed) & ((1n << 64n) - 1n); }
  next(): bigint {
    const M = (1n << 64n) - 1n;
    this.s = (this.s + 0x9e3779b97f4a7c15n) & M;
    let z = this.s;
    z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & M;
    z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & M;
    return z ^ (z >> 31n);
  }
  below(n: number) { return Number(this.next() % BigInt(n)); }
  elem<T>(xs: T[]): T { return xs[this.below(xs.length)]; }
  chance(a: number, b: number) { return this.below(b) < a; }
}

interface Req { method: string; path: string; authorization?: string; body?: string }
type Answer =
  | { kind: "json"; status: number; headers: Record<string, string>; body: unknown; delayMs: number }
  | { kind: "png"; w: number; h: number }
  | { kind: "hang" };

// ---- The two sides ----

class LeanSide {
  proc: Subprocess<"pipe", "pipe", "inherit">;
  reader: ReadableStreamDefaultReader<Uint8Array>;
  buf = "";
  constructor(cfg: Config) {
    this.proc = spawn([modelExe], { stdin: "pipe", stdout: "pipe", stderr: "inherit" });
    this.reader = this.proc.stdout.getReader();
    this.proc.stdin.write(JSON.stringify(cfg) + "\n");
  }
  async line(): Promise<string> {
    for (;;) {
      const i = this.buf.indexOf("\n");
      if (i >= 0) { const l = this.buf.slice(0, i); this.buf = this.buf.slice(i + 1); return l; }
      const { value, done } = await this.reader.read();
      if (done) throw new Error("the model stopped");
      this.buf += new TextDecoder().decode(value);
    }
  }
  async send(r: Req): Promise<Answer> {
    this.proc.stdin.write(JSON.stringify(r) + "\n");
    this.proc.stdin.flush();
    const j = JSON.parse(await this.line());
    if (j.hang) return { kind: "hang" };
    if (j.png) return { kind: "png", w: j.png[0], h: j.png[1] };
    return { kind: "json", status: j.status, headers: j.headers, body: j.body, delayMs: j.delayMs };
  }
  stop() { this.proc.stdin.end(); this.proc.kill(); }
}

class BunSide {
  proc: Subprocess<"ignore", "pipe", "inherit">;
  origin = "";
  constructor(readonly cfg: Omit<Config, "service">) {
    this.proc = spawn(["bun", `${here}/server.ts`, "--port", "0", "--quiet", "--seed", String(cfg.seed),
                       "--base", String(cfg.base), "--arrival", String(cfg.arrival), "--life", String(cfg.life),
                       "--act", String(cfg.act), "--lag", String(cfg.lag)],
                      { stdout: "pipe", stderr: "inherit" });
  }
  async start(): Promise<string> {
    const reader = this.proc.stdout.getReader();
    let text = "";
    while (!text.includes("app password")) {
      const { value, done } = await reader.read();
      if (done) throw new Error("the server stopped");
      text += new TextDecoder().decode(value);
    }
    reader.releaseLock();
    this.origin = /listening on (\S+)/.exec(text)![1];
    return this.origin;
  }
  async send(r: Req, timeoutMs: number): Promise<Answer> {
    const headers: Record<string, string> = {};
    if (r.authorization !== undefined) headers.authorization = r.authorization;
    if (r.method === "POST") headers["content-type"] = "application/json";
    const t0 = performance.now();
    let res: globalThis.Response;
    try {
      res = await fetch(this.origin + r.path, { method: r.method, headers, body: r.method === "POST" ? (r.body ?? "") : undefined,
                                                signal: AbortSignal.timeout(timeoutMs) });
    } catch (e) {
      if ((e as Error).name === "TimeoutError") return { kind: "hang" };
      throw e;
    }
    const elapsed = performance.now() - t0;
    if (res.headers.get("content-type") === "image/png") {
      const b = new Uint8Array(await res.arrayBuffer());
      const v = new DataView(b.buffer);
      return { kind: "png", w: v.getUint32(16), h: v.getUint32(20) };
    }
    const hs: Record<string, string> = {};
    for (const [k, v] of res.headers) if (k.startsWith("ratelimit-")) hs[k] = v;
    return { kind: "json", status: res.status, headers: hs, body: await res.json(), delayMs: Math.floor(elapsed) };
  }
  stop() { this.proc.kill(); }
}

// ---- The host each side's requests go through ----

class Host {
  items: Record<string, string> = {};
  cursors: string[] = [];
  /** listNotifications cursors. */
  notices: string[] = [];
  /** Posts seen in answers: their uri and cid. */
  posts: { uri: string; cid: string }[] = [];
  /** Record URIs putRecord answered with. */
  records: string[] = [];
  capture(path: string, a: Answer) {
    if (a.kind !== "json" || a.status < 200 || a.status >= 300) return;
    const b = a.body as Record<string, unknown>;
    if (typeof b?.accessJwt === "string" && typeof b?.refreshJwt === "string") {
      this.items.access = b.accessJwt;
      this.items.refresh = b.refreshJwt;
    }
    if (path.includes("putRecord") && typeof b?.uri === "string") this.records.push(b.uri);
    const notices = path.includes("listNotifications");
    if (typeof b?.cursor === "string") (notices ? this.notices : this.cursors).push(b.cursor);
    const add = (p: unknown) => {
      const q = p as { uri?: unknown; cid?: unknown };
      if (typeof q?.uri === "string" && typeof q?.cid === "string" && !this.posts.some((x) => x.uri === q.uri))
        this.posts.push({ uri: q.uri, cid: q.cid });
    };
    if (Array.isArray(b?.feed)) for (const it of b.feed as { post?: unknown }[]) add(it?.post);
    if (Array.isArray(b?.posts)) for (const p of b.posts) add(p);
  }
}

// ---- One random step ----

type Step = { req: Req; auth?: "access" | "refresh" | "garbage" | "none"; cursor?: number; notice?: number; slow?: number;
               /** Fills the request from what the host has seen (both hosts have seen the same). */
               fill?: (h: Host, r: Req) => void;
               /** Sign in first (so the new endpoints are reached with a live token). */
               signIn?: boolean };

const AUTHOR_HANDLES = ["ada", "zoe", "lei", "sam", "noor", "kit"];
// A few record keys, so writes repeat (and some are not valid keys).
const RKEYS = ["3l2aaaaaaaa2a", "3l2aaaaaaaa3b", "3l2aaaaaaaa4c", "3l2bbbbbbbb2a", "self", "a.b:c~d-e_f", ".", "..", "has/slash", "", "x".repeat(513)];

function writeStep(g: Rng, cfg: Config): Step {
  const x = "/xrpc/";
  const me = did(cfg);
  const repo = g.chance(9, 10) ? me : g.elem(["did:plc:fakeauthorada", identifier(cfg)]);
  const rkey = g.chance(9, 10) ? g.elem(RKEYS.slice(0, 4)) : g.elem(RKEYS);
  const at = g.elem(["2026-10-02T00:00:00.000Z", "2026-10-03T12:00:00.000Z"]);
  const kind = g.elem(["like", "like", "repost", "follow", "other"]);
  const collection = { like: "app.bsky.feed.like", repost: "app.bsky.feed.repost", follow: "app.bsky.graph.follow", other: "app.bsky.feed.post" }[kind]!;
  const pi = g.below(1000);
  const target = g.elem(AUTHOR_HANDLES);
  const auth = g.chance(19, 20) ? "access" : g.elem(["none", "garbage", "refresh"]) as Step["auth"];
  switch (g.below(4)) {
    case 0: case 1: {
      const broken = g.chance(1, 20);
      const step: Step = { req: { method: "POST", path: x + "com.atproto.repo.putRecord" }, auth };
      step.fill = (h, r) => {
        const p = h.posts.length > 0 ? h.posts[pi % h.posts.length] : { uri: "at://did:plc:nobody/app.bsky.feed.post/3fk00000000", cid: "bafynone" };
        const record = kind === "follow" ? { $type: collection, subject: `did:plc:fakeauthor${target}`, createdAt: at }
          : kind === "other" ? { $type: collection, text: "hi", createdAt: at }
          : { $type: collection, subject: p, createdAt: at };
        r.body = broken ? "{\"repo\": 1}" : JSON.stringify({ repo, collection, rkey, record });
      };
      return step;
    }
    case 2: {
      const col = g.elem(["app.bsky.feed.like", "app.bsky.feed.repost", "app.bsky.graph.follow"]);
      return { req: { method: "POST", path: x + "com.atproto.repo.deleteRecord", body: g.chance(1, 20) ? "[]" : JSON.stringify({ repo, collection: col, rkey }) }, auth };
    }
    default: {
      const col = g.elem(["app.bsky.feed.like", "app.bsky.feed.repost", "app.bsky.graph.follow", "app.bsky.feed.post"]);
      const ps = g.chance(1, 15) ? `repo=${encodeURIComponent(repo)}` : `repo=${encodeURIComponent(repo)}&collection=${col}&rkey=${encodeURIComponent(rkey)}`;
      const step: Step = { req: { method: "GET", path: x + "com.atproto.repo.getRecord?" + ps }, auth };
      if (g.chance(1, 2)) step.fill = (h, r) => {
        const u = h.records.at(-1);
        if (u === undefined) return;
        const [, , repo, col, rkey] = u.split("/");
        r.path = x + `com.atproto.repo.getRecord?repo=${encodeURIComponent(repo)}&collection=${col}&rkey=${encodeURIComponent(rkey)}`;
      };
      return step;
    }
  }
}

function readStep(g: Rng, cfg: Config): Step {
  const x = "/xrpc/";
  const auth = g.chance(19, 20) ? "access" : g.elem(["none", "garbage"]) as Step["auth"];
  const actor = () => {
    const a = g.elem(AUTHOR_HANDLES);
    return g.elem([`${a}.fake.test`, `did:plc:fakeauthor${a}`, `${a}.fake.test`, identifier(cfg), did(cfg), "nobody.test"]);
  };
  switch (g.below(8)) {
    case 0: case 1:
      return { req: { method: "POST", path: x + g.elem(["app.bsky.graph.muteActor", "app.bsky.graph.muteActor", "app.bsky.graph.unmuteActor"]),
                      body: g.chance(1, 20) ? "{}" : JSON.stringify({ actor: actor() }) }, auth };
    case 2:
      return { req: { method: "GET", path: x + "app.bsky.actor.getProfile?" + (g.chance(1, 15) ? "" : "actor=" + encodeURIComponent(actor())) }, auth };
    case 3: {
      const n = g.elem([1, 2, 3, 26]);
      const idx = Array.from({ length: n }, () => g.below(1000));
      const junk = g.chance(1, 10);
      const step: Step = { req: { method: "GET", path: x + "app.bsky.feed.getPosts?" }, auth };
      step.fill = (h, r) => {
        const uris = idx.map((i) => h.posts.length > 0 ? h.posts[i % h.posts.length].uri : "at://did:plc:nobody/app.bsky.feed.post/3fk00000000");
        if (junk) uris.push("at://did:plc:fakeauthorada/app.bsky.feed.post/3fk99999999", "garbage");
        r.path += uris.map((u) => "uris=" + encodeURIComponent(u)).join("&");
      };
      return step;
    }
    case 4: case 5: {
      const ps: string[] = [];
      const l = g.below(10);
      if (l < 6) ps.push(`limit=${g.elem(["1", "2", "3", "5", "10", "50"])}`);
      else if (l === 6) ps.push(`limit=${g.elem(["0", "101", "abc"])}`);
      const step: Step = { req: { method: "GET", path: x + "app.bsky.notification.listNotifications?" + ps.join("&") }, auth };
      const c = g.below(10);
      if (c < 4) step.notice = -1;
      else if (c < 6) step.notice = g.below(1000);
      else if (c === 6) step.req.path += (ps.length ? "&" : "") + "cursor=" + g.elem(["0", "garbage", "999999999", "1x"]);
      return step;
    }
    case 6:
      return { req: { method: "GET", path: x + "app.bsky.notification.getUnreadCount" }, auth };
    default: {
      const seen = g.elem(["2026-10-01T00:00:00.000Z", "2026-10-01T00:30:00Z", "2026-10-02T00:00:00.000Z", "2030-01-01T00:00:00.000+02:00",
                           "2026-09-30T23:59:59.999Z", "yesterday", "2026-13-01T00:00:00Z"]);
      const body = g.chance(1, 15) ? "{}" : JSON.stringify({ seenAt: seen });
      return { req: { method: "POST", path: x + "app.bsky.notification.updateSeen", body }, auth };
    }
  }
}

function randomStep(g: Rng, cfg: Config): Step {
  const x = "/xrpc/";
  const pageParams = () => {
    const ps: string[] = [];
    const l = g.below(10);
    if (l < 6) ps.push(`limit=${g.elem(["1", "2", "3", "5", "10", "25", "50", "100"])}`);
    else if (l === 6) ps.push(`limit=${g.elem(["0", "101", "abc", "", "007", "1e2", "-1"])}`);
    return ps;
  };
  switch (g.below(30)) {
    case 20: case 21: case 22: case 23: return { ...writeStep(g, cfg), signIn: g.chance(1, 2) };
    case 24: case 25: case 26: return { ...readStep(g, cfg), signIn: g.chance(1, 2) };
    case 27: {
      const ps = [`kind=${g.elem(["like", "repost", "follow", "like", "bogus"])}`, `actor=${g.elem([0, 1, 2, 3, 4, 5, 6])}`];
      if (g.chance(1, 2)) ps.push(`post=${g.elem([String(g.below(80)), "abc", "99999"])}`);
      return { req: { method: "POST", path: "/control/act?" + ps.join("&") } };
    }
    case 28:
      return { req: { method: "POST", path: g.elem([`/control/lag?n=${g.elem([0, 1, 3, 8])}`, "/control/catchup", "/control/lag?n=x"]) } };
    case 29: {
      const kind = g.elem(["400", "lost-after", "lost-after"]);
      return { req: { method: "POST", path: `/control/fail?n=${1 + g.below(2)}&kind=${kind}` } };
    }
    case 0: case 1: {
      const ok = g.chance(3, 4);
      const body = g.chance(1, 10) ? "not json"
        : JSON.stringify({ identifier: g.chance(1, 5) ? "nobody.test" : identifier(cfg), password: ok ? password(cfg) : "wrong-pass-word-0000" });
      return { req: { method: "POST", path: x + "com.atproto.server.createSession", body } };
    }
    case 2: case 3:
      return { req: { method: "POST", path: x + "com.atproto.server.refreshSession" }, auth: g.elem(["refresh", "refresh", "refresh", "access", "garbage", "none"]) };
    case 4:
      return { req: { method: "GET", path: x + "com.atproto.server.getSession" }, auth: g.elem(["access", "access", "refresh", "none"]) };
    case 5: case 6: case 7: case 8: case 9: {
      const ps = pageParams();
      const c = g.below(10);
      const step: Step = { req: { method: "GET", path: "" }, auth: g.chance(9, 10) ? "access" : g.elem(["none", "garbage", "refresh"]) };
      if (c < 5) step.cursor = -1; // the latest cursor
      else if (c < 7) step.cursor = g.below(1000); // an older one
      else if (c === 7) ps.push("cursor=" + g.elem(["garbage", "2026-10-01T00:00:00.000Z::bafy", "%3A%3A", ""]));
      step.req.path = x + "app.bsky.feed.getTimeline" + "?" + ps.join("&");
      return step;
    }
    case 10:
      return { req: { method: g.elem(["GET", "POST"]), path: x + g.elem(["app.bsky.feed.getAuthorFeed?actor=ada.fake.test", "com.atproto.server.createSession", "app.bsky.feed.getTimeline"]) }, auth: "access" };
    case 11:
      return { req: { method: "POST", path: `/control/post?n=${g.below(60)}` } };
    case 12:
      return { req: { method: "POST", path: "/control/" + g.elem(["expire", "revoke", "expire", "nonsense"]) } };
    case 13: {
      const kind = g.elem(["500", "503", "429", "429", "timeout", "bogus"]);
      return { req: { method: "POST", path: `/control/fail?n=${1 + g.below(3)}&kind=${kind}` } };
    }
    case 14:
      return { req: { method: "POST", path: `/control/slow?ms=${g.elem([0, 0, 5, 20, 40])}` } };
    case 15:
      return { req: { method: "GET", path: g.elem(["/img/96x96/avatar-ada.png", `/img/${1 + g.below(300)}x${1 + g.below(300)}/p.png`, "/img/0x5/p.png", "/img/5000x5/p.png", "/img/12x12/p.jpg", "/nowhere"]) } };
    case 16:
      return { req: { method: "GET", path: "/control/state" } };
    default: {
      const step: Step = { req: { method: "GET", path: x + "app.bsky.feed.getTimeline?" + pageParams().join("&") }, auth: "access", cursor: -1 };
      return step;
    }
  }
}

/** The request as this side's host sends it: its own tokens and cursors. */
function realize(s: Step, h: Host): Req {
  const r: Req = { ...s.req };
  if (s.auth && s.auth !== "none") {
    const t = s.auth === "garbage" ? "not-a-token" : h.items[s.auth];
    if (t !== undefined) r.authorization = "Bearer " + t;
  }
  if (s.cursor !== undefined && h.cursors.length > 0) {
    const c = s.cursor < 0 ? h.cursors[h.cursors.length - 1] : h.cursors[s.cursor % h.cursors.length];
    r.path += (r.path.endsWith("?") ? "" : "&") + "cursor=" + encodeURIComponent(c);
  }
  if (s.notice !== undefined && h.notices.length > 0) {
    const c = s.notice < 0 ? h.notices[h.notices.length - 1] : h.notices[s.notice % h.notices.length];
    r.path += (r.path.endsWith("?") ? "" : "&") + "cursor=" + encodeURIComponent(c);
  }
  s.fill?.(h, r);
  return r;
}

function same(lean: Answer, bun: Answer): string | undefined {
  if (lean.kind !== bun.kind) return `kind ${lean.kind} vs ${bun.kind}`;
  if (lean.kind === "png" && bun.kind === "png") return lean.w === bun.w && lean.h === bun.h ? undefined : `png ${lean.w}x${lean.h} vs ${bun.w}x${bun.h}`;
  if (lean.kind === "json" && bun.kind === "json") {
    if (lean.status !== bun.status) return `status ${lean.status} vs ${bun.status}`;
    const a = JSON.stringify(lean.body), b = JSON.stringify(bun.body);
    if (a !== b) return `body\n  lean ${a.slice(0, 400)}\n  bun  ${b.slice(0, 400)}`;
    const sorted = (h: Record<string, string>) => JSON.stringify(Object.entries(h).sort());
    if (sorted(lean.headers) !== sorted(bun.headers)) return `headers ${JSON.stringify(lean.headers)} vs ${JSON.stringify(bun.headers)}`;
    if (bun.delayMs + 2 < lean.delayMs) return `answered after ${bun.delayMs} ms, the model says ${lean.delayMs}`;
  }
  return undefined;
}

// ---- Runs ----

const tally: Record<string, number> = {};
const count = (k: string) => { tally[k] = (tally[k] ?? 0) + 1; };
let failures = 0;

for (let run = 0; run < runs; run++) {
  const seed = seed0 * 1000 + run;
  const g = new Rng(seed);
  const base = { ...defaults, seed, base: 10 + g.below(50), arrival: g.elem([0, 2, 3, 5]), life: 1 + g.below(8),
                 act: g.elem([0, 2, 4, 8]), lag: g.elem([0, 1, 2, 5]) };
  const bun = new BunSide(base);
  let lean: LeanSide | undefined;
  try {
    const origin = await bun.start();
    const cfg: Config = { ...base, service: origin };
    lean = new LeanSide(cfg);
    const hl = new Host(), hb = new Host();
    let agreed = true;
    for (let i = 0; i < steps; i++) {
      const step = randomStep(g, cfg);
      if (step.signIn) {
        const r: Req = { method: "POST", path: "/xrpc/com.atproto.server.createSession",
                         body: JSON.stringify({ identifier: identifier(cfg), password: password(cfg) }) };
        const al = await lean.send(r), ab = await bun.send(r, TIMEOUT_MS);
        const diff = same(al, ab);
        if (diff) { failures++; agreed = false; console.log(`run ${run} (seed ${seed}) step ${i}: sign-in: ${diff}`); break; }
        hl.capture(r.path, al);
        hb.capture(r.path, ab);
      }
      const rl = realize(step, hl), rb = realize(step, hb);
      if (JSON.stringify(rl) !== JSON.stringify(rb)) throw new Error(`step ${i}: the hosts diverged: ${JSON.stringify(rl)} vs ${JSON.stringify(rb)}`);
      const al = await lean.send(rl);
      const ab = await bun.send(rb, TIMEOUT_MS);
      const diff = same(al, ab);
      count(al.kind === "json" ? `${rl.path.split("?")[0].replace(/^\/(xrpc|control)\//, "")} ${al.status}${(al.body as { error?: string })?.error ? " " + (al.body as { error: string }).error : ""}` : `${rl.path.split("/")[1]} ${al.kind}`);
      if (diff) {
        failures++;
        agreed = false;
        console.log(`run ${run} (seed ${seed}) step ${i}: ${rl.method} ${rl.path}: ${diff}`);
        break;
      }
      hl.capture(rl.path, al);
      hb.capture(rb.path, ab);
    }
    const sl = await lean.send({ method: "GET", path: "/control/state" });
    const sb = await bun.send({ method: "GET", path: "/control/state" }, 2000);
    const d = same(sl, sb);
    if (!agreed) {}
    else if (d) { failures++; console.log(`run ${run}: final state: ${d}`); }
    else console.log(`run ${run} (seed ${seed}): ${steps} steps agree; final state ${JSON.stringify((sl as { body: unknown }).body)}`);
  } finally {
    lean?.stop();
    bun.stop();
  }
}

const keys = Object.keys(tally).sort();
console.log("answers: " + keys.map((k) => `${k} ×${tally[k]}`).join(", "));
console.log(failures === 0 ? `fake-pds replay: ${runs} runs × ${steps} steps, the Lean model and the server agree` : `fake-pds replay: ${failures} disagreement(s)`);
process.exit(failures === 0 ? 0 : 1);
