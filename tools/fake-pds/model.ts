// The fake PDS's behaviour, a line-for-line port of lean/CairnAtproto/Fake.lean (the Lean model
// is the reference; replay.ts checks that the two agree). Pure: no I/O, no clock, no network.
// server.ts serves it over HTTP.

const M64 = (1n << 64n) - 1n;
const GOLDEN = 0x9e3779b97f4a7c15n;

function mix(z: bigint): bigint {
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & M64;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & M64;
  return z ^ (z >> 31n);
}

export function hash(seed: number, tag: number, i: number): bigint {
  const a = (BigInt(seed) + BigInt(tag) * GOLDEN) & M64;
  return mix((mix(a) + BigInt(i) * GOLDEN) & M64);
}

export function pick(seed: number, tag: number, i: number, n: number): number {
  return Number(hash(seed, tag, i) % BigInt(n));
}

const pad = (w: number, s: string) => s.padStart(w, "0");
const hex16 = (x: bigint) => pad(16, x.toString(16));
const ALPHABET = "abcdefghijklmnopqrstuvwxyz234567";

export function code(seed: number, tag: number, n: number): string {
  let s = "";
  for (let i = 0; i < n; i++) s += ALPHABET[pick(seed, tag, i, 32)];
  return s;
}

/** A decimal number: digits only, at most `max` of them. */
export function digits(max: number, s: string): number | undefined {
  if (s.length === 0 || [...s].length > max || !/^[0-9]+$/.test(s)) return undefined;
  return Number(s);
}

export interface Config {
  seed: number;
  service: string;
  base: number;
  arrival: number;
  life: number;
}

export const defaults: Config = { seed: 0, service: "http://127.0.0.1:2583", base: 40, arrival: 3, life: 6 };

export const identifier = (c: Config) => `tester-${code(c.seed, 40, 4)}.fake.test`;
export const password = (c: Config) => [41, 42, 43, 44].map((t) => code(c.seed, t, 4)).join("-");
export const nonce = (c: Config) => code(c.seed, 45, 8);
export const did = (c: Config) => `did:plc:${code(c.seed, 46, 24)}`;
export const email = (c: Config) => `tester-${code(c.seed, 40, 4)}@example.test`;
export const lifeOf = (c: Config, gen: number) => 1 + pick(c.seed, 20, gen, Math.max(c.life, 1));

export function arrivals(c: Config, n: number): number {
  if (c.arrival === 0) return 0;
  return pick(c.seed, 30, n, c.arrival) === 0 ? 1 + pick(c.seed, 31, n, 3) : 0;
}

export const EPOCH = 1790812800000; // 2026-10-01T00:00:00Z

export const iso = (ms: number) => new Date(ms).toISOString();

export const trimService = (s: string) => s.replace(/\/+$/, "");

const AUTHORS: [string, string][] = [
  ["ada", "Ada Lovelace"], ["zoe", "Zoë Ångström"], ["lei", "李雷"], ["sam", "Sam 🌊"],
  ["noor", "Noor"], ["kit", "Kit O'Hara \"KO\""],
];

const WORDS = [
  "the", "sea", "is", "calm", "tonight", "café", "naïve", "日本語", "テスト", "🌊", "🦋", "✨",
  "résumé", "über", "fjord", "lantern", "quiet", "river", "stone", "cairn", "path", "north",
  "light", "paper", "ink", "bread", "tea", "window", "rain", "→", "“quoted”", "a\\b", "tab\tsep",
  "new\nline", "<tag>", "&amp;", "100%", "#hash", "@ada.fake.test", "https://example.com/x?y=1&z=2",
];

export const imgUrl = (c: Config, w: number, h: number, name: string) =>
  `${trimService(c.service)}/img/${w}x${h}/${name}.png`;

function author(c: Config, i: number) {
  const [h, d] = AUTHORS[i];
  return { did: `did:plc:fakeauthor${h}`, handle: `${h}.fake.test`, displayName: d,
           avatar: imgUrl(c, 96, 96, `avatar-${h}`) };
}

const authorOf = (c: Config, k: number) => pick(c.seed, 1, k, AUTHORS.length);
export const createdMs = (c: Config, k: number) => EPOCH + k * 60000 + pick(c.seed, 5, k, 59000);
const rkey = (k: number) => "3fk" + pad(8, String(k));
const postUri = (c: Config, k: number) => `at://${author(c, authorOf(c, k)).did}/app.bsky.feed.post/${rkey(k)}`;
const postCid = (c: Config, k: number) => "bafyreifake" + hex16(hash(c.seed, 2, k));

function textOf(c: Config, k: number): string {
  const n = 1 + pick(c.seed, 3, k, 12);
  const ws: string[] = [];
  for (let j = 0; j < n; j++) ws.push(WORDS[pick(c.seed, 4, k * 16 + j, WORDS.length)]);
  return `#${k} ` + ws.join(" ");
}

function embedOf(c: Config, k: number): object | undefined {
  const e = pick(c.seed, 10, k, 8);
  if (e === 0 || e === 1) {
    const images = [];
    for (let i = 0; i < 1 + pick(c.seed, 11, k, 4); i++) {
      const w = 64 + pick(c.seed, 12, k * 4 + i, 1200);
      const h = 64 + pick(c.seed, 13, k * 4 + i, 1200);
      images.push({ thumb: imgUrl(c, w, h, `${k}-${i}`), fullsize: imgUrl(c, w, h, `${k}-${i}`),
                    alt: `Image ${i + 1} of post ${k}`, aspectRatio: { width: w, height: h } });
    }
    return { $type: "app.bsky.embed.images#view", images };
  }
  if (e === 2) {
    return { $type: "app.bsky.embed.external#view",
             external: { uri: `https://example.com/fake/${k}`, title: `Link ${k}`, description: textOf(c, k + 1000000) } };
  }
  return undefined;
}

/** Post `k`, counted from the oldest, as `FeedItem.toJson` writes it. */
export function postAt(c: Config, k: number): object {
  const at = iso(createdMs(c, k));
  const post: Record<string, unknown> = {
    uri: postUri(c, k), cid: postCid(c, k), author: author(c, authorOf(c, k)),
    record: { $type: "app.bsky.feed.post", text: textOf(c, k), createdAt: at },
  };
  const embed = embedOf(c, k);
  if (embed) post.embed = embed;
  Object.assign(post, { replyCount: pick(c.seed, 6, k, 5), repostCount: pick(c.seed, 7, k, 20),
    likeCount: pick(c.seed, 8, k, 100), quoteCount: pick(c.seed, 9, k, 3), indexedAt: at });
  const item: Record<string, unknown> = { post };
  if (pick(c.seed, 14, k, 8) === 0) {
    item.reason = { $type: "app.bsky.feed.defs#reasonRepost",
                    by: author(c, pick(c.seed, 15, k, AUTHORS.length)), indexedAt: at };
  }
  return item;
}

export const cursorOf = (c: Config, k: number) => `${iso(createdMs(c, k))}::${postCid(c, k)}`;

export function cursorPos(c: Config, length: number, cur: string): number | undefined {
  const parts = cur.split("::");
  if (parts.length !== 2) return undefined;
  const ms = Date.parse(parts[0]);
  if (Number.isNaN(ms) || ms < EPOCH) return undefined;
  const k = Math.floor((ms - EPOCH) / 60000);
  return 0 < k && k < length && cursorOf(c, k) === cur ? k : undefined;
}

export function page(c: Config, length: number, limit: number, before: number | undefined) {
  const hi = before ?? length;
  const lo = hi - Math.min(limit, hi);
  const feed = [];
  for (let j = 0; j < hi - lo; j++) feed.push(postAt(c, hi - 1 - j));
  return lo === 0 ? { feed } : { feed, cursor: cursorOf(c, lo) };
}

// Requests and responses

export interface Req { method: string; path: string; authorization?: string; body?: string }

export type Response =
  | { kind: "json"; status: number; headers: [string, string][]; body: unknown; delayMs: number }
  | { kind: "png"; w: number; h: number }
  | { kind: "hang" };

function formDecode(s: string): string {
  const bytes: number[] = [];
  const cs = [...s];
  const enc = new TextEncoder();
  for (let i = 0; i < cs.length; i++) {
    const ch = cs[i];
    if (ch === "+") bytes.push(32);
    else if (ch === "%" && i + 2 < cs.length + 0 && /^[0-9a-fA-F]$/.test(cs[i + 1] ?? "") && /^[0-9a-fA-F]$/.test(cs[i + 2] ?? "")) {
      bytes.push(parseInt(cs[i + 1] + cs[i + 2], 16));
      i += 2;
    } else bytes.push(...enc.encode(ch));
  }
  try {
    return new TextDecoder("utf-8", { fatal: true, ignoreBOM: true }).decode(new Uint8Array(bytes));
  } catch {
    return "";
  }
}

function splitFirst(s: string, sep: string): [string, string | undefined] {
  const i = s.indexOf(sep);
  return i < 0 ? [s, undefined] : [s.slice(0, i), s.slice(i + sep.length)];
}

export function splitPath(p: string): [string, [string, string][]] {
  const [path, q] = splitFirst(p, "?");
  if (q === undefined) return [path, []];
  const params: [string, string][] = [];
  for (const kv of q.split("&")) {
    if (kv === "") continue;
    const [k, v] = splitFirst(kv, "=");
    params.push([formDecode(k), formDecode(v ?? "")]);
  }
  return [path, params];
}

const lookup = (ps: [string, string][], k: string) => ps.find((p) => p[0] === k)?.[1];
const errJson = (error: string, message: string) => ({ error, message });

type Fault = "500" | "503" | "429" | "timeout";
const FAULTS = ["500", "503", "429", "timeout"];

interface Live { gen: number; life: number; uses: number; expired: boolean }

export class Server {
  length: number;
  count = 0;
  issued = 0;
  live: Live | undefined = undefined;
  faults: Fault[] = [];
  delayMs = 0;

  constructor(readonly cfg: Config) {
    this.length = cfg.base;
  }

  private fail(status: number, name: string, msg: string): Response {
    return { kind: "json", status, headers: [], body: errJson(name, msg), delayMs: this.delayMs };
  }

  private ok(body: unknown): Response {
    return { kind: "json", status: 200, headers: [], body, delayMs: this.delayMs };
  }

  token(kind: string, gen: number) {
    return `fakepds-token.${kind}.${gen}.${nonce(this.cfg)}`;
  }

  parseToken(t: string): [string, number] | undefined {
    const ps = t.split(".");
    if (ps.length !== 4) return undefined;
    const [m, kind, g, n] = ps;
    if (m !== "fakepds-token" || n !== nonce(this.cfg) || (kind !== "access" && kind !== "refresh")) return undefined;
    const gen = digits(9, g);
    return gen === undefined ? undefined : [kind, gen];
  }

  private account() {
    const d = did(this.cfg);
    return { did: d, handle: identifier(this.cfg), email: email(this.cfg), active: true,
             didDoc: { id: d, service: [{ id: "#atproto_pds", type: "AtprotoPersonalDataServer",
                                          serviceEndpoint: trimService(this.cfg.service) }] } };
  }

  private issue(): Response {
    const g = this.issued + 1;
    this.issued = g;
    this.live = { gen: g, life: lifeOf(this.cfg, g), uses: 0, expired: false };
    return this.ok({ accessJwt: this.token("access", g), refreshJwt: this.token("refresh", g), ...this.account() });
  }

  /** The token checked for `kind`; an access token also counts the call. */
  private check(kind: string, auth: string | undefined): Response | undefined {
    const t = auth?.startsWith("Bearer ") ? auth.slice(7) : undefined;
    if (t === undefined) return this.fail(401, "AuthRequired", "Authentication Required");
    const p = this.parseToken(t);
    if (!p) return this.fail(400, "InvalidToken", "Token could not be verified");
    const [k, g] = p;
    if (k !== kind) return this.fail(400, "InvalidToken", "Bad token scope");
    const l = this.live;
    if (!l) return this.fail(400, "InvalidToken", "Token has been revoked");
    if (kind === "refresh") return g === l.gen ? undefined : this.fail(400, "InvalidToken", "Token has been revoked");
    if (g < l.gen) return this.fail(400, "ExpiredToken", "Token has expired");
    if (g > l.gen) return this.fail(400, "InvalidToken", "Token could not be verified");
    if (l.expired || l.uses >= l.life) return this.fail(400, "ExpiredToken", "Token has expired");
    l.uses += 1;
    return undefined;
  }

  private createSession(body: string): Response {
    let j: unknown;
    try {
      j = JSON.parse(body);
    } catch {
      return this.fail(400, "InvalidRequest", "Request body is not JSON");
    }
    const o = j !== null && typeof j === "object" && !Array.isArray(j) ? (j as Record<string, unknown>) : {};
    const i = o.identifier, p = o.password;
    if (typeof i !== "string" || typeof p !== "string")
      return this.fail(400, "InvalidRequest", "Input must have the properties identifier and password");
    if ((i === identifier(this.cfg) || i === did(this.cfg)) && p === password(this.cfg)) return this.issue();
    return this.fail(401, "AuthenticationRequired", "Invalid identifier or password");
  }

  private getTimeline(params: [string, string][]): Response {
    const lv = lookup(params, "limit");
    let limit: number | undefined = 50;
    if (lv !== undefined) {
      const n = digits(3, lv);
      limit = n !== undefined && 1 <= n && n <= 100 ? n : undefined;
    }
    if (limit === undefined) return this.fail(400, "InvalidRequest", "limit must be an integer from 1 to 100");
    const cur = lookup(params, "cursor");
    if (cur === undefined) return this.ok(page(this.cfg, this.length, limit, undefined));
    const k = cursorPos(this.cfg, this.length, cur);
    if (k === undefined) return this.fail(400, "InvalidRequest", "Malformed cursor");
    return this.ok(page(this.cfg, this.length, limit, k));
  }

  private xrpc(r: Req, nsid: string, params: [string, string][]): Response {
    const post = r.method === "POST", get = r.method === "GET";
    const wrong = () => this.fail(400, "InvalidRequest", "Incorrect HTTP method");
    switch (nsid) {
      case "com.atproto.server.createSession":
        return post ? this.createSession(r.body ?? "") : wrong();
      case "com.atproto.server.refreshSession":
        if (!post) return wrong();
        return this.check("refresh", r.authorization) ?? this.issue();
      case "com.atproto.server.getSession":
        if (!get) return wrong();
        return this.check("access", r.authorization) ?? this.ok(this.account());
      case "app.bsky.feed.getTimeline":
        if (!get) return wrong();
        return this.check("access", r.authorization) ?? this.getTimeline(params);
      default:
        return this.fail(501, "MethodNotImplemented", "Method Not Implemented");
    }
  }

  private faultResponse(f: Fault): Response {
    switch (f) {
      case "500": return this.fail(500, "InternalServerError", "Internal Server Error");
      case "503": return this.fail(503, "ServiceUnavailable", "Service Unavailable");
      case "429":
        return { kind: "json", status: 429, delayMs: this.delayMs, body: errJson("RateLimitExceeded", "Rate Limit Exceeded"),
                 headers: [["ratelimit-limit", "3000"], ["ratelimit-remaining", "0"],
                           ["ratelimit-reset", String(Math.floor(EPOCH / 1000) + 300 + this.count)],
                           ["ratelimit-policy", "3000;w=300"]] };
      case "timeout": return { kind: "hang" };
    }
  }

  stateJson() {
    const s: Record<string, unknown> = { length: this.length, count: this.count, issued: this.issued };
    if (this.live) s.live = { gen: this.live.gen, life: this.live.life, uses: this.live.uses, expired: this.live.expired };
    s.faults = [...this.faults];
    s.delayMs = this.delayMs;
    return s;
  }

  private control(name: string, params: [string, string][]): boolean {
    const num = (k: string, d: number) => {
      const v = lookup(params, k);
      return v === undefined ? d : digits(6, v);
    };
    switch (name) {
      case "post": {
        const n = num("n", 1);
        if (n === undefined) return false;
        this.length += n;
        return true;
      }
      case "expire":
        if (this.live) this.live.expired = true;
        return true;
      case "revoke":
        this.live = undefined;
        return true;
      case "fail": {
        const n = num("n", 1);
        const f = lookup(params, "kind") ?? "500";
        if (n === undefined || !FAULTS.includes(f)) return false;
        for (let i = 0; i < n; i++) this.faults.push(f as Fault);
        return true;
      }
      case "slow": {
        const ms = num("ms", 0);
        if (ms === undefined) return false;
        this.delayMs = ms;
        return true;
      }
      default:
        return false;
    }
  }

  handle(r: Req): Response {
    const [path, params] = splitPath(r.path);
    const json = (status: number, body: unknown): Response => ({ kind: "json", status, headers: [], body, delayMs: 0 });
    if (path.startsWith("/xrpc/")) {
      this.length += arrivals(this.cfg, this.count);
      this.count += 1;
      const f = this.faults.shift();
      if (f !== undefined) return this.faultResponse(f);
      return this.xrpc(r, path.slice(6), params);
    }
    if (path.startsWith("/control/")) {
      const name = path.slice(9);
      if (name === "state") return r.method === "GET" ? json(200, this.stateJson()) : json(400, errJson("InvalidRequest", "Incorrect HTTP method"));
      if (r.method !== "POST") return json(400, errJson("InvalidRequest", "Incorrect HTTP method"));
      return this.control(name, params) ? json(200, this.stateJson()) : json(400, errJson("InvalidRequest", "Unknown control or bad parameter"));
    }
    if (path.startsWith("/img/") && r.method === "GET") {
      const size = imageSize(path);
      return size ? { kind: "png", w: size[0], h: size[1] } : json(404, errJson("NotFound", "Not Found"));
    }
    return json(404, errJson("NotFound", "Not Found"));
  }
}

/** `/img/<w>x<h>/<name>.png`, each side 1 to 4096. */
export function imageSize(path: string): [number, number] | undefined {
  const ps = path.split("/");
  if (ps.length !== 4 || ps[0] !== "" || ps[1] !== "img" || !ps[3].endsWith(".png")) return undefined;
  const wh = ps[2].split("x");
  if (wh.length !== 2) return undefined;
  const w = digits(4, wh[0]), h = digits(4, wh[1]);
  if (w === undefined || h === undefined || w < 1 || w > 4096 || h < 1 || h > 4096) return undefined;
  return [w, h];
}
