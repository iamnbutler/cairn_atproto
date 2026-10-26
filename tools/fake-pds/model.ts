// The fake PDS's behaviour, a line-for-line port of lean/CairnAtproto/Fake.lean (the Lean model
// is the reference; replay.ts checks that the two agree). Pure: no I/O, no clock, no network.
// server.ts serves it over HTTP. The lexicon types below mirror CairnAtproto's, and their
// `...Json` functions write members in the order its `toJson`s do, so the two sides' answers are
// the same text.

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
  act: number;
  lag: number;
}

export const defaults: Config = { seed: 0, service: "http://127.0.0.1:2583", base: 40, arrival: 3, life: 6, act: 4, lag: 2 };

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

// ---- Dates: parseDatetime (CairnAtproto.Datetime) ----

const isLeap = (y: number) => (y % 4 === 0 && y % 100 !== 0) || y % 400 === 0;
function daysInMonth(y: number, m: number): number {
  if ([1, 3, 5, 7, 8, 10, 12].includes(m)) return 31;
  if ([4, 6, 9, 11].includes(m)) return 30;
  if (m === 2) return isLeap(y) ? 29 : 28;
  return 0;
}
const ediv = (a: number, b: number) => Math.floor(a / b);
function daysFromCivil(y0: number, m: number, d: number): number {
  const y = m <= 2 ? y0 - 1 : y0;
  const era = ediv(y >= 0 ? y : y - 399, 400);
  const yoe = y - era * 400;
  const mp = m > 2 ? m - 3 : m + 9;
  const doy = ediv(153 * mp + 2, 5) + d - 1;
  const doe = yoe * 365 + ediv(yoe, 4) - ediv(yoe, 100) + doy;
  return era * 146097 + doe - 719468;
}

/** An RFC 3339 timestamp as UTC milliseconds since the epoch, as Lean's `parseDatetime` reads it. */
export function parseDatetime(s: string): number | undefined {
  const m = /^([0-9]{4})-([0-9]{2})-([0-9]{2})[Tt]([0-9]{2}):([0-9]{2}):([0-9]{2})(\.[0-9]+)?(.*)$/s.exec(s);
  if (!m) return undefined;
  const [y, mo, d, h, mi, sec] = m.slice(1, 7).map(Number);
  const ms = m[7] ? Number((m[7].slice(1) + "000").slice(0, 3)) : 0;
  const rest = m[8];
  let off: number;
  if (rest === "Z" || rest === "z") off = 0;
  else {
    const o = /^([+-])([0-9]{2}):([0-9]{2})$/.exec(rest);
    if (!o) return undefined;
    const oh = Number(o[2]), om = Number(o[3]);
    if (oh > 23 || om > 59) return undefined;
    off = (o[1] === "+" ? 1 : -1) * (oh * 60 + om);
  }
  if (!(1 <= mo && mo <= 12 && 1 <= d && d <= daysInMonth(y, mo) && h <= 23 && mi <= 59 && sec <= 60)) return undefined;
  const secs = daysFromCivil(y, mo, d) * 86400 + h * 3600 + mi * 60 + sec - off * 60;
  return secs * 1000 + ms;
}

// ---- Lexicon types, as CairnAtproto's, and their JSON ----

const NSID = {
  like: "app.bsky.feed.like", repost: "app.bsky.feed.repost", follow: "app.bsky.graph.follow",
  post: "app.bsky.feed.post",
};

interface ProfileViewer { muted: boolean; blockedBy: boolean; blocking?: string; following?: string; followedBy?: string }
interface Profile { did: string; handle: string; displayName?: string; avatar?: string; viewer: ProfileViewer }
interface StrongRef { uri: string; cid: string }
interface QuotedPost { uri: string; cid: string; author: Profile; text: string; createdAt: string; indexedAt: string }
type Embed =
  | { kind: "images"; images: { thumb: string; fullsize: string; alt: string; aspect?: [number, number] }[] }
  | { kind: "external"; uri: string; title: string; description: string }
  | { kind: "quote"; q: QuotedPost };
interface Post {
  uri: string; cid: string; author: Profile; text: string; createdAt: string; embed?: Embed;
  replyCount: number; repostCount: number; likeCount: number; quoteCount: number; indexedAt: string;
  reply?: { root: StrongRef; parent: StrongRef }; viewer: { like?: string; repost?: string };
}
type ReplyRef = { kind: "post"; post: Post } | { kind: "notFound"; uri: string } | { kind: "blocked"; uri: string };
interface FeedItem {
  post: Post;
  reply?: { root: ReplyRef; parent: ReplyRef; grandparentAuthor?: Profile };
  reason?: { by: Profile; indexedAt: string };
}
export type Rec =
  | { kind: "like" | "repost"; subject: StrongRef; createdAt: string }
  | { kind: "follow"; subject: string; createdAt: string }
  | { kind: "other"; type: string };
interface Notification {
  uri: string; cid: string; author: Profile; reason: string; reasonSubject?: string; text?: string;
  isRead: boolean; indexedAt: string;
}

const noViewer = (): ProfileViewer => ({ muted: false, blockedBy: false });
const isDefaultViewer = (v: ProfileViewer) =>
  !v.muted && !v.blockedBy && v.blocking === undefined && v.following === undefined && v.followedBy === undefined;

function profileJson(p: Profile): Record<string, unknown> {
  const o: Record<string, unknown> = { did: p.did, handle: p.handle };
  if (p.displayName !== undefined) o.displayName = p.displayName;
  if (p.avatar !== undefined) o.avatar = p.avatar;
  if (!isDefaultViewer(p.viewer)) {
    const v: Record<string, unknown> = { muted: p.viewer.muted, blockedBy: p.viewer.blockedBy };
    if (p.viewer.blocking !== undefined) v.blocking = p.viewer.blocking;
    if (p.viewer.following !== undefined) v.following = p.viewer.following;
    if (p.viewer.followedBy !== undefined) v.followedBy = p.viewer.followedBy;
    o.viewer = v;
  }
  return o;
}

function embedJson(e: Embed): object {
  switch (e.kind) {
    case "images":
      return { $type: "app.bsky.embed.images#view", images: e.images.map((i) => {
        const o: Record<string, unknown> = { thumb: i.thumb, fullsize: i.fullsize, alt: i.alt };
        if (i.aspect) o.aspectRatio = { width: i.aspect[0], height: i.aspect[1] };
        return o;
      }) };
    case "external":
      return { $type: "app.bsky.embed.external#view", external: { uri: e.uri, title: e.title, description: e.description } };
    case "quote":
      return { $type: "app.bsky.embed.record#view", record: {
        $type: "app.bsky.embed.record#viewRecord", uri: e.q.uri, cid: e.q.cid, author: profileJson(e.q.author),
        value: { $type: NSID.post, text: e.q.text, createdAt: e.q.createdAt }, indexedAt: e.q.indexedAt } };
  }
}

function postJson(p: Post): Record<string, unknown> {
  const record: Record<string, unknown> = { $type: NSID.post, text: p.text, createdAt: p.createdAt };
  if (p.reply) record.reply = { root: p.reply.root, parent: p.reply.parent };
  const o: Record<string, unknown> = { uri: p.uri, cid: p.cid, author: profileJson(p.author), record };
  if (p.embed) o.embed = embedJson(p.embed);
  Object.assign(o, { replyCount: p.replyCount, repostCount: p.repostCount, likeCount: p.likeCount,
                     quoteCount: p.quoteCount, indexedAt: p.indexedAt });
  if (p.viewer.like !== undefined || p.viewer.repost !== undefined) {
    const v: Record<string, unknown> = {};
    if (p.viewer.like !== undefined) v.like = p.viewer.like;
    if (p.viewer.repost !== undefined) v.repost = p.viewer.repost;
    o.viewer = v;
  }
  return o;
}

function refJson(r: ReplyRef): object {
  if (r.kind === "notFound") return { $type: "app.bsky.feed.defs#notFoundPost", uri: r.uri, notFound: true };
  if (r.kind === "blocked") return { $type: "app.bsky.feed.defs#blockedPost", uri: r.uri, blocked: true };
  return { $type: "app.bsky.feed.defs#postView", ...postJson(r.post) };
}

function itemJson(i: FeedItem): object {
  const o: Record<string, unknown> = { post: postJson(i.post) };
  if (i.reply) {
    const r: Record<string, unknown> = { root: refJson(i.reply.root), parent: refJson(i.reply.parent) };
    if (i.reply.grandparentAuthor) r.grandparentAuthor = profileJson(i.reply.grandparentAuthor);
    o.reply = r;
  }
  if (i.reason) o.reason = { $type: "app.bsky.feed.defs#reasonRepost", by: profileJson(i.reason.by), indexedAt: i.reason.indexedAt };
  return o;
}

const recCollection = (r: Rec) => (r.kind === "other" ? r.type : NSID[r.kind]);

export function recJson(r: Rec): object {
  if (r.kind === "other") return { $type: r.type };
  if (r.kind === "follow") return { $type: NSID.follow, subject: r.subject, createdAt: r.createdAt };
  return { $type: NSID[r.kind], subject: { uri: r.subject.uri, cid: r.subject.cid }, createdAt: r.createdAt };
}

const isObj = (j: unknown): j is Record<string, unknown> => j !== null && typeof j === "object" && !Array.isArray(j);
const str = (j: unknown, k: string): string | undefined => (isObj(j) && typeof j[k] === "string" ? (j[k] as string) : undefined);

/** `Record.ofJson`: total. */
function recOf(j: Record<string, unknown>): Rec {
  const t = str(j, "$type") ?? "";
  const at = str(j, "createdAt") ?? "";
  if (t === NSID.like || t === NSID.repost) {
    const s = j.subject;
    const uri = str(s, "uri"), cid = str(s, "cid");
    if (isObj(s) && uri !== undefined && cid !== undefined) return { kind: t === NSID.like ? "like" : "repost", subject: { uri, cid }, createdAt: at };
    return { kind: "other", type: t };
  }
  if (t === NSID.follow) {
    const s = str(j, "subject");
    return s !== undefined ? { kind: "follow", subject: s, createdAt: at } : { kind: "other", type: t };
  }
  return { kind: "other", type: t };
}

/** `PutRecord.ofJson`. */
function putRecordOf(j: unknown): { repo: string; rkey: string; record: Rec } | undefined {
  const repo = str(j, "repo"), collection = str(j, "collection"), rkey = str(j, "rkey");
  if (repo === undefined || collection === undefined || rkey === undefined) return undefined;
  const r = (j as Record<string, unknown>).record;
  if (!isObj(r)) return undefined;
  const record = recOf(r);
  return collection === recCollection(record) ? { repo, rkey, record } : undefined;
}

function notificationJson(n: Notification): object {
  const recordType = n.reason === "like" ? NSID.like : n.reason === "repost" ? NSID.repost : n.reason === "follow" ? NSID.follow : NSID.post;
  const o: Record<string, unknown> = { uri: n.uri, cid: n.cid, author: profileJson(n.author), reason: n.reason };
  if (n.reasonSubject !== undefined) o.reasonSubject = n.reasonSubject;
  const record: Record<string, unknown> = { $type: recordType };
  if (n.text !== undefined) record.text = n.text;
  record.createdAt = n.indexedAt;
  Object.assign(o, { record, isRead: n.isRead, indexedAt: n.indexedAt });
  return o;
}

// ---- The timeline ----

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

function author(c: Config, i: number): Profile {
  const [h, d] = AUTHORS[i];
  return { did: `did:plc:fakeauthor${h}`, handle: `${h}.fake.test`, displayName: d,
           avatar: imgUrl(c, 96, 96, `avatar-${h}`), viewer: noViewer() };
}

const me = (c: Config): Profile => ({ did: did(c), handle: identifier(c), displayName: "Tester",
                                      avatar: imgUrl(c, 96, 96, "avatar-tester"), viewer: noViewer() });

const authorOf = (c: Config, k: number) => pick(c.seed, 1, k, AUTHORS.length);
export const isMine = (c: Config, k: number) => k !== 0 && pick(c.seed, 22, k, 4) === 0;
const poster = (c: Config, k: number) => (isMine(c, k) ? me(c) : author(c, authorOf(c, k)));
export const createdMs = (c: Config, k: number) => EPOCH + k * 60000 + pick(c.seed, 5, k, 59000);
const rkey = (k: number) => "3fk" + pad(8, String(k));
export const postUri = (c: Config, k: number) => `at://${poster(c, k).did}/app.bsky.feed.post/${rkey(k)}`;
const postCid = (c: Config, k: number) => "bafyreifake" + hex16(hash(c.seed, 2, k));

function textOf(c: Config, k: number): string {
  const n = 1 + pick(c.seed, 3, k, 12);
  const ws: string[] = [];
  for (let j = 0; j < n; j++) ws.push(WORDS[pick(c.seed, 4, k * 16 + j, WORDS.length)]);
  return `#${k} ` + ws.join(" ");
}

const mentions = (c: Config, k: number) => !isMine(c, k) && pick(c.seed, 24, k, 10) === 0;
const postText = (c: Config, k: number) => textOf(c, k) + (mentions(c, k) ? ` @${identifier(c)}` : "");
const quotesOf = (c: Config, k: number) => (k !== 0 && pick(c.seed, 10, k, 8) === 3 ? pick(c.seed, 23, k, k) : undefined);

function quoted(c: Config, j: number): QuotedPost {
  return { uri: postUri(c, j), cid: postCid(c, j), author: poster(c, j), text: postText(c, j),
           createdAt: iso(createdMs(c, j)), indexedAt: iso(createdMs(c, j)) };
}

function embedOf(c: Config, k: number): Embed | undefined {
  const e = pick(c.seed, 10, k, 8);
  if (e === 0 || e === 1) {
    const images = [];
    for (let i = 0; i < 1 + pick(c.seed, 11, k, 4); i++) {
      const w = 64 + pick(c.seed, 12, k * 4 + i, 1200);
      const h = 64 + pick(c.seed, 13, k * 4 + i, 1200);
      images.push({ thumb: imgUrl(c, w, h, `${k}-${i}`), fullsize: imgUrl(c, w, h, `${k}-${i}`),
                    alt: `Image ${i + 1} of post ${k}`, aspect: [w, h] as [number, number] });
    }
    return { kind: "images", images };
  }
  if (e === 2) return { kind: "external", uri: `https://example.com/fake/${k}`, title: `Link ${k}`, description: textOf(c, k + 1000000) };
  const j = quotesOf(c, k);
  return j === undefined ? undefined : { kind: "quote", q: quoted(c, j) };
}

// Replies (cairn#236): replyTarget, rootFrom, threadRoot, postView and replyCtx in Fake.lean.

type Parent = { post: number } | "notFound" | "blocked";

export function replyTarget(c: Config, k: number): Parent | undefined {
  if (k === 0 || pick(c.seed, 16, k, 4) !== 0) return undefined;
  const r = pick(c.seed, 18, k, 8);
  if (r === 0) return "notFound";
  if (r === 1) return "blocked";
  return { post: pick(c.seed, 17, k, k) };
}

function rootFrom(c: Config, fuel: number, j: number): Parent {
  for (let n = fuel; n > 0; n--) {
    const t = replyTarget(c, j);
    if (t === undefined) return { post: j };
    if (typeof t === "string") return t;
    j = t.post;
  }
  return { post: j };
}

function threadRoot(c: Config, k: number): Parent {
  const t = replyTarget(c, k);
  if (t === undefined) return { post: k };
  if (typeof t === "string") return t;
  return rootFrom(c, t.post, t.post);
}

const goneUri = (k: number) => `at://did:plc:fakeauthorgone/app.bsky.feed.post/3fkgone${pad(8, String(k))}`;
const goneCid = (c: Config, k: number) => "bafyreigone" + hex16(hash(c.seed, 19, k));
const blockedUri = (k: number) => `at://did:plc:fakeauthorblocker/app.bsky.feed.post/3fkblock${pad(8, String(k))}`;
const blockedCid = (c: Config, k: number) => "bafyreiblock" + hex16(hash(c.seed, 21, k));

function parentRef(c: Config, k: number, p: Parent): StrongRef {
  if (p === "notFound") return { uri: goneUri(k), cid: goneCid(c, k) };
  if (p === "blocked") return { uri: blockedUri(k), cid: blockedCid(c, k) };
  return { uri: postUri(c, p.post), cid: postCid(c, p.post) };
}

/** Post `k`'s view: a function of the seed and `k`. */
function postView(c: Config, k: number): Post {
  const at = iso(createdMs(c, k));
  const t = replyTarget(c, k);
  return {
    uri: postUri(c, k), cid: postCid(c, k), author: poster(c, k), text: postText(c, k), createdAt: at,
    embed: embedOf(c, k), replyCount: pick(c.seed, 6, k, 5), repostCount: pick(c.seed, 7, k, 20),
    likeCount: pick(c.seed, 8, k, 100), quoteCount: pick(c.seed, 9, k, 3), indexedAt: at,
    reply: t === undefined ? undefined : { root: parentRef(c, k, threadRoot(c, k)), parent: parentRef(c, k, t) },
    viewer: {},
  };
}

function parentView(c: Config, k: number, p: Parent): ReplyRef {
  if (p === "notFound") return { kind: "notFound", uri: goneUri(k) };
  if (p === "blocked") return { kind: "blocked", uri: blockedUri(k) };
  return { kind: "post", post: postView(c, p.post) };
}

const reposter = (c: Config, k: number) => (pick(c.seed, 14, k, 8) === 0 ? pick(c.seed, 15, k, AUTHORS.length) : undefined);

/** Post `k`, counted from the oldest. */
function postAt(c: Config, k: number): FeedItem {
  const at = iso(createdMs(c, k));
  const item: FeedItem = { post: postView(c, k) };
  const t = replyTarget(c, k);
  if (t !== undefined) {
    let grandparentAuthor: Profile | undefined;
    if (typeof t !== "string") {
      const g = replyTarget(c, t.post);
      if (g !== undefined && typeof g !== "string") grandparentAuthor = poster(c, g.post);
    }
    item.reply = { root: parentView(c, k, threadRoot(c, k)), parent: parentView(c, k, t), grandparentAuthor };
  }
  const r = reposter(c, k);
  if (r !== undefined) item.reason = { by: author(c, r), indexedAt: at };
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

/** `pageWhere`: the post indices of a page of the posts `keep` keeps, and its cursor. */
function pageWhere(c: Config, keep: (k: number) => boolean, length: number, limit: number, before: number | undefined): [number[], string | undefined] {
  const ks: number[] = [];
  for (let k = (before ?? length) - 1; k >= 0; k--) if (keep(k)) ks.push(k);
  const taken = ks.slice(0, limit);
  return [taken, limit < ks.length && taken.length > 0 ? cursorOf(c, taken[taken.length - 1]) : undefined];
}

// ---- What the server holds ----

type ActKind = "like" | "repost" | "follow";
const ACT_KINDS: ActKind[] = ["like", "repost", "follow"];
interface Act { kind: ActKind; actor: number; post: number; undo: boolean }
type Change =
  | { kind: "put"; collection: string; rkey: string; record: Rec; cid: string }
  | { kind: "delete"; collection: string; rkey: string }
  | { kind: "mute" | "unmute"; did: string }
  | { kind: "act"; act: Act }
  | { kind: "post"; k: number };
interface Entry { change: Change; seq: number; vis: number; ms: number }
interface RepoRec { collection: string; rkey: string; record: Rec; cid: string }

class Facts {
  repo: RepoRec[] = [];
  muted: string[] = [];
  likes: [number, string][] = [];
  reposts: [number, string][] = [];
  follows: number[] = [];

  find(col: string, rk: string) { return this.repo.find((r) => r.collection === col && r.rkey === rk); }
  without(col: string, rk: string) { return this.repo.filter((r) => !(r.collection === col && r.rkey === rk)); }

  apply(c: Config, ch: Change) {
    switch (ch.kind) {
      case "put": this.repo = [{ collection: ch.collection, rkey: ch.rkey, record: ch.record, cid: ch.cid }, ...this.without(ch.collection, ch.rkey)]; break;
      case "delete": this.repo = this.without(ch.collection, ch.rkey); break;
      case "mute": this.muted = [ch.did, ...this.muted.filter((d) => d !== ch.did)]; break;
      case "unmute": this.muted = this.muted.filter((d) => d !== ch.did); break;
      case "act": {
        const a = ch.act, u = postUri(c, a.post);
        const same = (p: [number, string]) => p[0] === a.actor && p[1] === u;
        if (a.kind === "like") this.likes = a.undo ? this.likes.filter((p) => !same(p)) : [[a.actor, u], ...this.likes];
        else if (a.kind === "repost") this.reposts = a.undo ? this.reposts.filter((p) => !same(p)) : [[a.actor, u], ...this.reposts];
        else this.follows = a.undo ? this.follows.filter((x) => x !== a.actor) : [a.actor, ...this.follows];
        break;
      }
      case "post": break;
    }
  }

  static of(c: Config, es: Entry[]): Facts {
    const f = new Facts();
    for (const e of es) f.apply(c, e.change);
    return f;
  }

  myLikes(uri: string) { return this.repo.filter((r) => r.record.kind === "like" && r.record.subject.uri === uri); }
  myReposts(uri: string) { return this.repo.filter((r) => r.record.kind === "repost" && r.record.subject.uri === uri); }
  myFollow(d: string) { return this.repo.find((r) => r.record.kind === "follow" && r.record.subject === d); }
  likeCount(uri: string) { return this.likes.filter((p) => p[1] === uri).length + this.myLikes(uri).length; }
  repostCount(uri: string) { return this.reposts.filter((p) => p[1] === uri).length + this.myReposts(uri).length; }
}

const recUri = (c: Config, r: RepoRec) => `at://${did(c)}/${r.collection}/${r.rkey}`;

// ---- Views ----

function viewProfile(c: Config, f: Facts, p: Profile): Profile {
  if (p.did === did(c)) return p;
  const fo = f.myFollow(p.did);
  const viewer: ProfileViewer = { muted: f.muted.includes(p.did), blockedBy: false };
  if (fo) viewer.following = recUri(c, fo);
  return { ...p, viewer };
}

function viewPost(c: Config, f: Facts, p: Post): Post {
  const likes = f.myLikes(p.uri), reposts = f.myReposts(p.uri);
  const embed = p.embed?.kind === "quote" ? { kind: "quote" as const, q: { ...p.embed.q, author: viewProfile(c, f, p.embed.q.author) } } : p.embed;
  return { ...p, author: viewProfile(c, f, p.author), embed,
           likeCount: p.likeCount + f.likeCount(p.uri), repostCount: p.repostCount + f.repostCount(p.uri),
           viewer: { like: likes[0] && recUri(c, likes[0]), repost: reposts[0] && recUri(c, reposts[0]) } };
}

const viewRef = (c: Config, f: Facts, r: ReplyRef): ReplyRef => (r.kind === "post" ? { kind: "post", post: viewPost(c, f, r.post) } : r);

function viewItem(c: Config, f: Facts, i: FeedItem): FeedItem {
  const o: FeedItem = { post: viewPost(c, f, i.post) };
  if (i.reply) o.reply = { root: viewRef(c, f, i.reply.root), parent: viewRef(c, f, i.reply.parent),
                           grandparentAuthor: i.reply.grandparentAuthor && viewProfile(c, f, i.reply.grandparentAuthor) };
  if (i.reason) o.reason = { by: viewProfile(c, f, i.reason.by), indexedAt: i.reason.indexedAt };
  return o;
}

function shown(c: Config, f: Facts, k: number): boolean {
  if (f.muted.includes(poster(c, k).did)) return false;
  const r = reposter(c, k);
  return r === undefined || !f.muted.includes(author(c, r).did);
}

// ---- Notifications ----

function notice(c: Config, k: number): [string, string | undefined] | undefined {
  const t = replyTarget(c, k);
  const replyTo = t !== undefined && typeof t !== "string" && isMine(c, t.post) ? t.post : undefined;
  const q = quotesOf(c, k);
  const quoteOf = q !== undefined && isMine(c, q) ? q : undefined;
  if (isMine(c, k)) return undefined;
  if (replyTo !== undefined) return ["reply", postUri(c, replyTo)];
  if (quoteOf !== undefined) return ["quote", postUri(c, quoteOf)];
  return mentions(c, k) ? ["mention", undefined] : undefined;
}

const actRkey = (seq: number) => "3fa" + pad(10, String(seq));

function noticeOf(c: Config, f: Facts, seenAt: number | undefined, e: Entry): Notification | undefined {
  const isRead = seenAt !== undefined && e.ms <= seenAt;
  const at = iso(e.ms);
  const ch = e.change;
  if (ch.kind === "post") {
    const n = notice(c, ch.k);
    if (!n) return undefined;
    return { uri: postUri(c, ch.k), cid: postCid(c, ch.k), author: viewProfile(c, f, poster(c, ch.k)), reason: n[0],
             reasonSubject: n[1], text: postText(c, ch.k), isRead, indexedAt: at };
  }
  if (ch.kind === "act") {
    const a = ch.act;
    if (a.undo || (a.kind !== "follow" && !isMine(c, a.post))) return undefined;
    const who = author(c, a.actor);
    return { uri: `at://${who.did}/${NSID[a.kind]}/${actRkey(e.seq)}`, cid: "bafyreiact" + hex16(hash(c.seed, 38, e.seq)),
             author: viewProfile(c, f, who), reason: a.kind,
             reasonSubject: a.kind === "follow" ? undefined : postUri(c, a.post), isRead, indexedAt: at };
  }
  return undefined;
}

function runPage<T>(xs: T[], limit: number, before: number | undefined): [T[], number | undefined] {
  const hi = before ?? xs.length;
  const lo = hi - Math.min(limit, hi);
  return [xs.slice(lo, hi).reverse(), lo === 0 ? undefined : lo];
}

// ---- Requests and responses ----

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
const parseJson = (s: string): unknown => { try { return JSON.parse(s); } catch { return undefined; } };

type Fault = "500" | "503" | "429" | "timeout" | "400" | "lost-after";
const FAULTS = ["500", "503", "429", "timeout", "400", "lost-after"];

interface Live { gen: number; life: number; uses: number; expired: boolean }

const QUERIES = ["com.atproto.server.getSession", "app.bsky.feed.getTimeline", "com.atproto.repo.getRecord",
  "app.bsky.actor.getProfile", "app.bsky.feed.getPosts", "app.bsky.notification.listNotifications",
  "app.bsky.notification.getUnreadCount"];
const PROCEDURES = ["com.atproto.repo.putRecord", "com.atproto.repo.deleteRecord", "app.bsky.graph.muteActor",
  "app.bsky.graph.unmuteActor", "app.bsky.notification.updateSeen"];

/** `limit`: 1 to 100, 50 when absent. */
function limitOf(params: [string, string][]): number | undefined {
  const lv = lookup(params, "limit");
  if (lv === undefined) return 50;
  const n = digits(3, lv);
  return n !== undefined && 1 <= n && n <= 100 ? n : undefined;
}

const validRkey = (k: string) => k.length > 0 && [...k].length <= 512 && k !== "." && k !== ".." && /^[A-Za-z0-9._:~-]+$/.test(k);

export class Server {
  length: number;
  count = 0;
  issued = 0;
  live: Live | undefined = undefined;
  faults: Fault[] = [];
  delayMs = 0;
  log: Entry[] = [];
  now = new Facts();
  lag: number;
  lastVis = 0;
  lastMs = EPOCH;
  seenAt: number | undefined = undefined;

  constructor(readonly cfg: Config) {
    this.length = cfg.base;
    this.lag = cfg.lag;
    this.noticePosts(0, false);
  }

  private fail(status: number, name: string, msg: string): Response {
    return { kind: "json", status, headers: [], body: errJson(name, msg), delayMs: this.delayMs };
  }

  private ok(body: unknown): Response {
    return { kind: "json", status: 200, headers: [], body, delayMs: this.delayMs };
  }

  // ---- The log ----

  append(ch: Change, delay = true) {
    const seq = this.log.length;
    const d = delay ? pick(this.cfg.seed, 36, seq, this.lag + 1) : 0;
    const vis = Math.max(this.lastVis, this.count + d);
    const ms = Math.max(this.lastMs + 1, ch.kind === "post" ? createdMs(this.cfg, ch.k) : this.lastMs + 1000);
    this.log.push({ change: ch, seq, vis, ms });
    this.now.apply(this.cfg, ch);
    this.lastVis = vis;
    this.lastMs = ms;
  }

  noticePosts(from: number, delay = true) {
    for (let k = from; k < this.length; k++) if (notice(this.cfg, k)) this.append({ kind: "post", k }, delay);
  }

  seenLog(): Entry[] {
    const out: Entry[] = [];
    for (const e of this.log) { if (e.vis > this.count) break; out.push(e); }
    return out;
  }

  seen(): Facts { return Facts.of(this.cfg, this.seenLog()); }

  notices(): Notification[] {
    const es = this.seenLog();
    const f = Facts.of(this.cfg, es);
    return es.map((e) => noticeOf(this.cfg, f, this.seenAt, e)).filter((n): n is Notification => n !== undefined);
  }

  act(kind: ActKind, actor: number, k: number) {
    if (kind !== "follow" && k >= this.length) return;
    const u = postUri(this.cfg, k);
    const undo = kind === "like" ? this.now.likes.some((p) => p[0] === actor && p[1] === u)
      : kind === "repost" ? this.now.reposts.some((p) => p[0] === actor && p[1] === u)
      : this.now.follows.includes(actor);
    this.append({ kind: "act", act: { kind, actor, post: kind === "follow" ? 0 : k, undo } });
  }

  othersAct(n: number) {
    const c = this.cfg;
    if (c.act === 0 || pick(c.seed, 32, n, c.act) !== 0) return;
    this.act(ACT_KINDS[Math.min(pick(c.seed, 33, n, 3), 2)], pick(c.seed, 34, n, AUTHORS.length), pick(c.seed, 35, n, Math.max(this.length, 1)));
  }

  newestMine(): number | undefined {
    for (let k = this.length - 1; k >= 0; k--) if (isMine(this.cfg, k)) return k;
    return undefined;
  }

  // ---- Sessions ----

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
    const j = parseJson(body);
    if (j === undefined) return this.fail(400, "InvalidRequest", "Request body is not JSON");
    const i = str(j, "identifier"), p = str(j, "password");
    if (i === undefined || p === undefined)
      return this.fail(400, "InvalidRequest", "Input must have the properties identifier and password");
    if ((i === identifier(this.cfg) || i === did(this.cfg)) && p === password(this.cfg)) return this.issue();
    return this.fail(401, "AuthenticationRequired", "Invalid identifier or password");
  }

  // ---- Methods ----

  private getTimeline(params: [string, string][]): Response {
    const limit = limitOf(params);
    if (limit === undefined) return this.fail(400, "InvalidRequest", "limit must be an integer from 1 to 100");
    const f = this.seen();
    const answer = (before: number | undefined) => {
      const [ks, cursor] = pageWhere(this.cfg, (k) => shown(this.cfg, f, k), this.length, limit, before);
      const page: Record<string, unknown> = { feed: ks.map((k) => itemJson(viewItem(this.cfg, f, postAt(this.cfg, k)))) };
      if (cursor !== undefined) page.cursor = cursor;
      return this.ok(page);
    };
    const cur = lookup(params, "cursor");
    if (cur === undefined) return answer(undefined);
    const k = cursorPos(this.cfg, this.length, cur);
    if (k === undefined) return this.fail(400, "InvalidRequest", "Malformed cursor");
    return answer(k);
  }

  private isMe(repo: string) { return repo === did(this.cfg) || repo === identifier(this.cfg); }
  private recRef(r: RepoRec) { return { uri: recUri(this.cfg, r), cid: r.cid }; }

  private writeRec(col: string, rk: string, record: Rec): Response {
    const cid = "bafyreirec" + hex16(hash(this.cfg.seed, 37, this.log.length));
    this.append({ kind: "put", collection: col, rkey: rk, record, cid });
    return this.ok(this.recRef({ collection: col, rkey: rk, record, cid }));
  }

  private putRec(w: { repo: string; rkey: string; record: Rec }): Response {
    if (!this.isMe(w.repo)) return this.fail(400, "InvalidRequest", "Could not find repo");
    if (!validRkey(w.rkey)) return this.fail(400, "InvalidRequest", "Invalid record key");
    if (w.record.kind === "other") return this.fail(400, "InvalidRequest", "Unsupported collection");
    const col = recCollection(w.record);
    const old = this.now.find(col, w.rkey);
    if (old && JSON.stringify(recJson(old.record)) === JSON.stringify(recJson(w.record))) return this.ok(this.recRef(old));
    return this.writeRec(col, w.rkey, w.record);
  }

  private deleteRec(u: { repo: string; collection: string; rkey: string }): Response {
    if (!this.isMe(u.repo)) return this.fail(400, "InvalidRequest", "Could not find repo");
    if (this.now.find(u.collection, u.rkey)) this.append({ kind: "delete", collection: u.collection, rkey: u.rkey });
    return this.ok({});
  }

  private getRec(u: { repo: string; collection: string; rkey: string }): Response {
    const missing = this.fail(400, "RecordNotFound", `Could not locate record: at://${u.repo}/${u.collection}/${u.rkey}`);
    if (!this.isMe(u.repo)) return missing;
    const r = this.now.find(u.collection, u.rkey);
    return r ? this.ok({ uri: recUri(this.cfg, r), cid: r.cid, value: recJson(r.record) }) : missing;
  }

  /** The account `actor` names: `null` for the tester, an author's index, or undefined. */
  private resolve(actor: string): number | null | undefined {
    if (this.isMe(actor)) return null;
    for (let i = 0; i < AUTHORS.length; i++) {
      const a = author(this.cfg, i);
      if (a.did === actor || a.handle === actor) return i;
    }
    return undefined;
  }

  private getProfile(params: [string, string][]): Response {
    const a = lookup(params, "actor");
    const who = a === undefined ? undefined : this.resolve(a);
    if (who === undefined) return this.fail(400, "InvalidRequest", "Profile not found");
    const f = this.seen();
    const posts = (p: (k: number) => boolean) => { let n = 0; for (let k = 0; k < this.length; k++) if (p(k)) n++; return n; };
    let profile: Profile, description: string, followers: number, follows: number, postsCount: number;
    if (who === null) {
      profile = me(this.cfg);
      description = "The tester's account on the fake PDS.";
      followers = f.follows.length;
      follows = f.repo.filter((r) => r.collection === NSID.follow).length;
      postsCount = posts((k) => isMine(this.cfg, k));
    } else {
      const au = author(this.cfg, who);
      profile = viewProfile(this.cfg, f, au);
      description = `${au.handle} on the fake PDS.`;
      followers = pick(this.cfg.seed, 25, who, 1000) + (f.myFollow(au.did) ? 1 : 0);
      follows = pick(this.cfg.seed, 26, who, 500) + (f.follows.includes(who) ? 1 : 0);
      postsCount = posts((k) => !isMine(this.cfg, k) && authorOf(this.cfg, k) === who);
    }
    return this.ok({ ...profileJson(profile), description, followersCount: followers, followsCount: follows, postsCount });
  }

  private setMute(mute: boolean, actor: string): Response {
    const who = this.resolve(actor);
    if (who === undefined) return this.fail(400, "InvalidRequest", "Actor not found");
    if (who === null) return this.fail(400, "InvalidRequest", "Cannot mute oneself");
    const d = author(this.cfg, who).did;
    if (this.now.muted.includes(d) !== mute) this.append({ kind: mute ? "mute" : "unmute", did: d }, false);
    return this.ok({});
  }

  private getPosts(params: [string, string][]): Response {
    const uris = params.filter((p) => p[0] === "uris").map((p) => p[1]);
    if (uris.length > 25) return this.fail(400, "InvalidRequest", "Too many uris");
    const f = this.seen();
    const posts = [];
    for (const u of uris) {
      const ps = u.split("/");
      if (ps.length !== 5 || !ps[4].startsWith("3fk")) continue;
      const k = digits(8, ps[4].slice(3));
      if (k === undefined || k >= this.length || postUri(this.cfg, k) !== u) continue;
      posts.push(postJson(viewPost(this.cfg, f, postView(this.cfg, k))));
    }
    return this.ok({ posts });
  }

  private listNotifications(params: [string, string][]): Response {
    const limit = limitOf(params);
    if (limit === undefined) return this.fail(400, "InvalidRequest", "limit must be an integer from 1 to 100");
    const ns = this.notices();
    const answer = (before: number | undefined) => {
      const [items, lo] = runPage(ns, limit, before);
      const page: Record<string, unknown> = { notifications: items.map(notificationJson) };
      if (lo !== undefined) page.cursor = String(lo);
      if (this.seenAt !== undefined) page.seenAt = iso(this.seenAt);
      return this.ok(page);
    };
    const cur = lookup(params, "cursor");
    if (cur === undefined) return answer(undefined);
    const i = digits(9, cur);
    if (i === undefined || !(0 < i && i < ns.length)) return this.fail(400, "InvalidRequest", "Malformed cursor");
    return answer(i);
  }

  private updateSeen(body: string): Response {
    const t = str(parseJson(body), "seenAt");
    if (t === undefined) return this.fail(400, "InvalidRequest", "Input must have the property seenAt");
    const ms = parseDatetime(t);
    if (ms === undefined || ms < 0) return this.fail(400, "InvalidRequest", "seenAt must be a datetime");
    this.seenAt = ms;
    return this.ok({});
  }

  private authed(nsid: string, body: string, params: [string, string][]): Response {
    const bad = () => this.fail(400, "InvalidRequest", "Input is not valid");
    switch (nsid) {
      case "com.atproto.server.getSession": return this.ok(this.account());
      case "app.bsky.feed.getTimeline": return this.getTimeline(params);
      case "com.atproto.repo.putRecord": {
        const w = putRecordOf(parseJson(body));
        return w ? this.putRec(w) : bad();
      }
      case "com.atproto.repo.deleteRecord": {
        const j = parseJson(body);
        const repo = str(j, "repo"), collection = str(j, "collection"), rk = str(j, "rkey");
        return repo !== undefined && collection !== undefined && rk !== undefined ? this.deleteRec({ repo, collection, rkey: rk }) : bad();
      }
      case "com.atproto.repo.getRecord": {
        const repo = lookup(params, "repo"), collection = lookup(params, "collection"), rk = lookup(params, "rkey");
        return repo !== undefined && collection !== undefined && rk !== undefined ? this.getRec({ repo, collection, rkey: rk }) : bad();
      }
      case "app.bsky.graph.muteActor": case "app.bsky.graph.unmuteActor": {
        const a = str(parseJson(body), "actor");
        return a !== undefined ? this.setMute(nsid === "app.bsky.graph.muteActor", a) : bad();
      }
      case "app.bsky.actor.getProfile": return this.getProfile(params);
      case "app.bsky.feed.getPosts": return this.getPosts(params);
      case "app.bsky.notification.listNotifications": return this.listNotifications(params);
      case "app.bsky.notification.getUnreadCount": return this.ok({ count: this.notices().filter((n) => !n.isRead).length });
      case "app.bsky.notification.updateSeen": return this.updateSeen(body);
      default: return this.fail(501, "MethodNotImplemented", "Method Not Implemented");
    }
  }

  private xrpc(r: Req, nsid: string, params: [string, string][]): Response {
    const post = r.method === "POST", get = r.method === "GET";
    const wrong = () => this.fail(400, "InvalidRequest", "Incorrect HTTP method");
    if (nsid === "com.atproto.server.createSession") return post ? this.createSession(r.body ?? "") : wrong();
    if (nsid === "com.atproto.server.refreshSession") {
      if (!post) return wrong();
      return this.check("refresh", r.authorization) ?? this.issue();
    }
    if (QUERIES.includes(nsid) || PROCEDURES.includes(nsid)) {
      if (PROCEDURES.includes(nsid) ? !post : !get) return wrong();
      return this.check("access", r.authorization) ?? this.authed(nsid, r.body ?? "", params);
    }
    return this.fail(501, "MethodNotImplemented", "Method Not Implemented");
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
      case "400": return this.fail(400, "InvalidRequest", "Refused by the fake PDS");
      case "timeout": case "lost-after": return { kind: "hang" };
    }
  }

  stateJson() {
    const s: Record<string, unknown> = { length: this.length, count: this.count, issued: this.issued };
    if (this.live) s.live = { gen: this.live.gen, life: this.live.life, uses: this.live.uses, expired: this.live.expired };
    Object.assign(s, {
      faults: [...this.faults], delayMs: this.delayMs, lag: this.lag, log: this.log.length, seen: this.seenLog().length,
      records: this.now.repo.map((r) => recUri(this.cfg, r)), muted: [...this.now.muted],
      likes: this.now.likes.length, reposts: this.now.reposts.length, follows: this.now.follows.length,
    });
    if (this.seenAt !== undefined) s.seenAt = iso(this.seenAt);
    return s;
  }

  private grow(n: number) {
    const old = this.length;
    this.length += n;
    this.noticePosts(old);
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
        this.grow(n);
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
      case "act": {
        const kind = lookup(params, "kind") ?? "like";
        if (!ACT_KINDS.includes(kind as ActKind)) return false;
        const actor = num("actor", 0);
        if (actor === undefined || actor >= AUTHORS.length) return false;
        const pv = lookup(params, "post");
        let post: number | undefined;
        if (pv !== undefined) {
          post = digits(9, pv);
          if (post === undefined) return false;
        }
        const k = post ?? this.newestMine();
        if (k !== undefined) this.act(kind as ActKind, actor, k);
        else if (kind === "follow") this.act("follow", actor, 0);
        return true;
      }
      case "lag": {
        const n = num("n", 0);
        if (n === undefined) return false;
        this.lag = n;
        return true;
      }
      case "catchup":
        for (const e of this.log) e.vis = Math.min(e.vis, this.count);
        this.lastVis = Math.min(this.lastVis, this.count);
        return true;
      default:
        return false;
    }
  }

  /** Between requests: posts arrive (with their notifications), another account may act. */
  private between() {
    const n = this.count;
    const old = this.length;
    this.length += arrivals(this.cfg, n);
    this.count = n + 1;
    this.noticePosts(old);
    this.othersAct(n);
  }

  handle(r: Req): Response {
    const [path, params] = splitPath(r.path);
    const json = (status: number, body: unknown): Response => ({ kind: "json", status, headers: [], body, delayMs: 0 });
    if (path.startsWith("/xrpc/")) {
      this.between();
      const f = this.faults.shift();
      if (f === "lost-after") {
        this.xrpc(r, path.slice(6), params);
        return { kind: "hang" };
      }
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
