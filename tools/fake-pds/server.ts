// The fake PDS over HTTP on 127.0.0.1 (cairn#208). Its behaviour is model.ts, a port of the Lean
// model (lean/CairnAtproto/Fake.lean); replay.ts checks that the two agree.
//
//   bun tools/fake-pds/server.ts [--port 2583] [--seed N] [--base 40] [--arrival 3] [--life 6] [--quiet]
//
// It accepts one test identifier and app password, generated from the seed (random unless
// --seed) and printed at start. Tokens are fake markers; nothing here is a real credential, and
// the log never shows a token or the createSession body. Control endpoints:
//   POST /control/post?n=3              n posts arrive at the head
//   POST /control/expire                the access token expires now
//   POST /control/revoke                the session ends: its refresh token is refused too
//   POST /control/fail?n=2&kind=500     the next n calls fail: 500, 503, 429 or timeout
//   POST /control/slow?ms=800           every XRPC reply waits ms (0: no delay)
//   GET  /control/state                 the server's state

import { deflateSync } from "node:zlib";
import { Server, defaults, identifier, password, hash, type Config } from "./model.ts";

function arg(name: string): string | undefined {
  const i = Bun.argv.indexOf(`--${name}`);
  return i >= 0 ? Bun.argv[i + 1] : undefined;
}
const num = (name: string, d: number) => {
  const v = arg(name);
  if (v === undefined) return d;
  if (!/^[0-9]+$/.test(v)) throw new Error(`--${name} takes a number`);
  return Number(v);
};

const quiet = Bun.argv.includes("--quiet");
const seed = num("seed", Math.floor(Math.random() * 2 ** 32));
const port = num("port", 2583);

// ---- PNG (a seeded gradient, any size) ----

const CRC = new Uint32Array(256).map((_, n) => {
  let c = n;
  for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
  return c >>> 0;
});
function crc32(b: Uint8Array): number {
  let c = 0xffffffff;
  for (const x of b) c = CRC[(c ^ x) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function chunk(type: string, data: Uint8Array): Uint8Array {
  const out = new Uint8Array(12 + data.length);
  const v = new DataView(out.buffer);
  v.setUint32(0, data.length);
  out.set(new TextEncoder().encode(type), 4);
  out.set(data, 8);
  v.setUint32(8 + data.length, crc32(out.subarray(4, 8 + data.length)));
  return out;
}
function png(w: number, h: number, name: string): Uint8Array {
  let n = 0;
  for (const ch of name) n = (n * 31 + ch.codePointAt(0)!) % 1_000_003;
  const x = hash(seed, 50, n);
  const [r0, g0, b0] = [Number(x & 0xffn), Number((x >> 8n) & 0xffn), Number((x >> 16n) & 0xffn)];
  const raw = new Uint8Array(h * (1 + 3 * w));
  for (let y = 0; y < h; y++) {
    const row = y * (1 + 3 * w);
    for (let i = 0; i < w; i++) {
      const o = row + 1 + 3 * i;
      raw[o] = (r0 + (i * 128) / w) & 0xff;
      raw[o + 1] = (g0 + (y * 128) / h) & 0xff;
      raw[o + 2] = b0;
    }
  }
  const ihdr = new Uint8Array(13);
  const v = new DataView(ihdr.buffer);
  v.setUint32(0, w);
  v.setUint32(4, h);
  ihdr.set([8, 2, 0, 0, 0], 8);
  const parts = [new Uint8Array([137, 80, 78, 71, 13, 10, 26, 10]), chunk("IHDR", ihdr),
                 chunk("IDAT", deflateSync(raw)), chunk("IEND", new Uint8Array())];
  const out = new Uint8Array(parts.reduce((a, p) => a + p.length, 0));
  let o = 0;
  for (const p of parts) { out.set(p, o); o += p.length; }
  return out;
}

// ---- The server ----

let model: Server;
const http = Bun.serve({
  hostname: "127.0.0.1",
  port,
  idleTimeout: 255,
  async fetch(req) {
    const url = req.url;
    const i = url.indexOf("/", url.indexOf("://") + 3);
    const path = i < 0 ? "/" : url.slice(i);
    const body = req.method === "POST" ? await req.text() : "";
    const r = model.handle({ method: req.method, path, authorization: req.headers.get("authorization") ?? undefined, body });
    const shown = path.startsWith("/xrpc/com.atproto.server.createSession") ? path : path.slice(0, 200);
    if (r.kind === "hang") {
      if (!quiet) console.log(`${req.method} ${shown} -> (no reply)`);
      await new Promise((resolve) => req.signal.addEventListener("abort", resolve));
      return new Response(null, { status: 504 });
    }
    if (r.kind === "png") {
      const name = path.split("/").pop() ?? "";
      return new Response(png(r.w, r.h, name), { headers: { "content-type": "image/png", "cache-control": "max-age=3600" } });
    }
    if (r.delayMs > 0) await Bun.sleep(r.delayMs);
    if (!quiet) console.log(`${req.method} ${shown} -> ${r.status}`);
    return new Response(JSON.stringify(r.body), {
      status: r.status,
      headers: [["content-type", "application/json; charset=utf-8"], ...r.headers],
    });
  },
});

const cfg: Config = { ...defaults, seed, service: `http://127.0.0.1:${http.port}`,
  base: num("base", defaults.base), arrival: num("arrival", defaults.arrival), life: num("life", defaults.life) };
model = new Server(cfg);

console.log(`fake-pds listening on ${cfg.service}`);
console.log(`seed ${seed}`);
console.log(`identifier ${identifier(cfg)}`);
console.log(`app password ${password(cfg)}`);
