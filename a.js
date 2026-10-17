// CF-Workers-TGProxy —— 含管理面板的版本
// 新增：/admin 控制面板（ADMIN 密码保护）、动态配置（env / 可选 KV 持久化）、自动生成连接链接。
// 原有代理逻辑（/、/health、/api/v1/session、/api/v1/ws、KWS 中继）保持不变。

// ===== 配置默认值 =====
const DEFAULTS = {
  dnPack: 32 * 1024,      // 下行聚合上限（字节）
  upPack: 20 * 1024,      // 上行合包目标（字节）
  dnMs: 1,                // 下行静默窗口（毫秒）
  laneLimit: 128,         // 单会话并发 lane 数
  laneMax: 8 * 1024 * 1024,   // 单 lane 字节上限
  laneItems: 1024,        // 单 lane 条数上限
  qMax: 32 * 1024 * 1024,     // 整会话字节上限
  iMax: 16384,            // 整会话条数上限
  bootTTL: 2 * 60 * 1000,     // bootstrap 有效期（毫秒）
  sessTTL: 5 * 60 * 1000,     // session 有效期（毫秒）
};

// 运行期代理参数（每次请求前由 loadConfig 填充）
let CFG = { ...DEFAULTS };
// 运行期密钥
let RT = { secret: '', key: null, boot: '' };
// 无 KV 时的内存临时覆盖（重启/扩缩容会丢失）
let MEM = {};

export default { fetch: (req, env) => route(req, env) };
const txt = new TextEncoder(), dec = new TextDecoder(), nil = new Uint8Array(0), badHead = new Set(['HEAD', 'POST', 'GET ', 'OPTI']);
const CRYPTO = globalThis.crypto, macKeys = new Map(), leases = new Map();
const reply = (body = null, status = 404) => new Response(body, { status });
function u8(v) { if (v instanceof Uint8Array && v.constructor === Uint8Array) return v; if (v instanceof ArrayBuffer) return new Uint8Array(v); if (ArrayBuffer.isView(v)) return new Uint8Array(v.buffer, v.byteOffset, v.byteLength); throw TypeError(); }
const dup = v => u8(v).slice();
function cat(...args) { const parts = args.filter(v => v?.byteLength).map(u8); const out = new Uint8Array(parts.reduce((total, part) => total + part.byteLength, 0)); let o = 0; for (const part of parts) { out.set(part, o); o += part.byteLength; } return out; }
const hex = v => Uint8Array.from({ length: v.length / 2 }, (_, i) => Number.parseInt(v.slice(i * 2, i * 2 + 2), 16));
function b64(v) { const b = v instanceof Uint8Array ? v : new Uint8Array(v); return btoa(String.fromCharCode(...b)).replaceAll('+', '-').replaceAll('/', '_').replace(/=+$/, ''); }
const un64 = v => { const s = v.replaceAll('-', '+').replaceAll('_', '/'); return Uint8Array.from(atob(s + '='.repeat((4 - s.length % 4) % 4)), c => c.charCodeAt(0)); };
const rand = n => CRYPTO.getRandomValues(new Uint8Array(n));
const wake = st => { const { wake: ok } = st; st.wake = null; ok?.(); };
const isType = t => t === 1 || t === 2 || t === 3 || t === 4 || t === 17;
function enc(type, sid, data = nil) { const body = u8(data); if (!isType(type)) throw RangeError(); if (!Number.isInteger(sid) || sid < 0 || sid > 0xffffff) { throw RangeError(); } if (body.byteLength > 1024 * 1024) throw RangeError(); const frame = new Uint8Array(8 + body.byteLength); frame[0] = type; frame[1] = sid >>> 16; frame[2] = sid >>> 8; frame[3] = sid; new DataView(frame.buffer).setUint32(4, body.byteLength, false); frame.set(body, 8); return frame; }
function getFrame(b, o) { if (b.byteLength - o < 8) return null; const type = b[o]; if (!isType(type)) throw Error(); const view = new DataView(b.buffer, b.byteOffset + o, b.byteLength - o); const sid = (b[o + 1] << 16) | (b[o + 2] << 8) | b[o + 3]; const n = view.getUint32(4, false); if (n > 1024 * 1024) throw Error(); const total = 8 + n; if (b.byteLength - o < total) return null; return { frame: { type, sid, payload: b.subarray(o + 8, o + total) }, consumed: total, }; }
function frames(v) { const src = u8(v), out = []; for (let o = 0; o < src.byteLength;) { const part = getFrame(src, o); if (!part) throw Error(); if (out.length >= 4096) throw Error(); out.push(part.frame); o += part.consumed; } return out; }
function win(data) { const body = u8(data); if (body.byteLength !== 4) throw Error(); const n = new DataView(body.buffer, body.byteOffset, 4).getUint32(0, false); if (!n) throw Error(); return n; }
function check(frame) { const { type, payload: data } = frame; if (type === 1 || type === 3) { if (data.byteLength) throw Error(); return 0; } if (type === 2) { if (!data.byteLength) throw Error(); return 0; } if (type === 4) return win(data); throw Error(); }
const i16 = (b, o) => (b[o] | b[o + 1] << 8) << 16 >> 16;
function headOf(head) { const tag = new DataView(head.buffer, head.byteOffset, head.byteLength).getUint32(56, true); const mode = tag === 0xefefefef ? 0xef : tag === 0xeeeeeeee ? 0xee : tag === 0xdddddddd ? 0xdd : 0; if (!mode) throw Error(); const dc = i16(head, 60); const target = Math.abs(dc) - 1; if (target < 0 || target >= 5) throw Error(); return { mode, target, media: dc < 0 }; }
function mkHead(mode, target, media) { const head = new Uint8Array(64); do { CRYPTO.getRandomValues(head); } while ( head[0] === 0xef || badHead.has(dec.decode(head.subarray(0, 4))) || head.subarray(4, 8).every(v => v === 0) ); head.fill(mode, 56, 60); new DataView(head.buffer).setInt16(60, (target + 1) * (media ? -1 : 1), true); return head; }
function getKey(v, keepTag = false) { const str = String(v || '').trim().toLowerCase(); if (!/^(?:[0-9a-f]{32}|(?:dd|ee|ef)[0-9a-f]{32})$/.test(str)) { throw Error(); } return hex(keepTag && str.length === 34 && str.startsWith('dd') ? str : str.slice(-32)); }
function hostOf(v) { const host = String(v || '').trim().toLowerCase().replace(/\.$/, ''); const labels = host.split('.'); if (!host.includes('.') || host.length > 253 || host.includes(':') || labels.some(label => !/^[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?$/.test(label))) { throw Error(); } return host; }
const macKey = (raw, id) => { let key = macKeys.get(id); if (!key) macKeys.set(id, key = CRYPTO.subtle.importKey('raw', u8(raw), { name: 'HMAC', hash: 'SHA-256' }, false, ['sign'])); return key; };
const sign = async (key, v) => new Uint8Array(await CRYPTO.subtle.sign('HMAC', await key, u8(v)));
async function mac(boot, kind, body) { const prefix = txt.encode(`${kind}\n`); const msg = new Uint8Array(prefix.byteLength + body.byteLength); msg.set(prefix); msg.set(body, prefix.byteLength); return (await sign( macKey(txt.encode(boot), `token:${boot}`), msg, )).slice(0, 16); }
async function mkToken(boot, kind, expAt, nonce) { const body = new Uint8Array(4 + 12); const exp = Math.ceil(expAt / 1000); new DataView(body.buffer).setUint32(0, exp, false); body.set(nonce, 4); const token = new Uint8Array(32); token.set(body); token.set(await mac(boot, kind, body), body.byteLength); return b64(token); }
const mkBoot = async () => mkToken(RT.boot, 'bootstrap', Date.now() + CFG.bootTTL, rand(12));
async function verify(v, boot, kind) { if (typeof v !== 'string' || !/^[A-Za-z0-9_-]{43}$/.test(v)) return false; let token; try { token = un64(v); } catch { return false; } if (token.byteLength !== 32 || b64(token) !== v) return false; const body = token.slice(0, 4 + 12); const sig = token.slice(body.byteLength); const exp = new DataView(body.buffer, body.byteOffset, body.byteLength).getUint32(0, false); if (exp <= Math.floor(Date.now() / 1000)) return false; const want = await mac(boot, kind, body); let diff = sig.byteLength ^ want.byteLength; for (let i = 0; i < want.length; i++) diff |= sig[i] ^ want[i]; return diff === 0; }
const mkSess = async () => mkToken(RT.boot, 'session', Date.now() + CFG.sessTTL, rand(12));
const authBoot = async (v, boot) => v === boot || verify(v, boot, 'bootstrap');
const mkLease = token => ({ expires: new DataView(un64(token).buffer).getUint32(0) * 1000, active: new Set(), used: new Set(), deleted: false, });
const bearer = v => /^Bearer ([^\s]+)$/.exec(v || '')?.[1] ?? null;
const binary = req => req.headers.get('Content-Type')?.trim().toLowerCase() === 'application/octet-stream';
function hello(body) { if (body.byteLength !== 9 || body[0] !== 0x10 || body[1] !== 0 || body[2] !== 0 || body[3] !== 0 || new DataView(body.buffer, body.byteOffset, body.byteLength).getUint32(4, false) !== 1 || body[8] !== 1) { throw Error(); } }
const protos = req => (req.headers.get('Sec-WebSocket-Protocol') ?? '').split(',').map(v => v.trim()).filter(Boolean);
const mkCfg = ({ SECRET, BOOT }) => { const secret = String(SECRET || '').trim(), boot = String(BOOT || '').trim(); if (!secret) throw Error(); if (!boot) throw Error(); return { secret, key: getKey(secret), boot }; };
async function mkCap(secret, host) { const key = macKey( getKey(secret, true), `bridge:${String(secret).trim().toLowerCase()}`, ); const sig = await sign( key, txt.encode(`tdesktop-web-proxy-bridge-v1\n${hostOf(host)}`), ); return b64(sig); }
async function bridge(url, secret) { if (url.pathname !== '/' || url.search.length !== 51) return null; const cand = url.search.slice(8); if (url.search !== `?bridge=${cand}` || !/^[A-Za-z0-9_-]{43}$/.test(cand)) return null; const host = hostOf(url.hostname); const want = await mkCap(secret, host); if (cand.length !== want.length) return null; let diff = 0; for (let i = 0; i < want.length; i++) diff |= cand.charCodeAt(i) ^ want.charCodeAt(i); return diff === 0 ? host : null; }
const sha = async v => new Uint8Array(await CRYPTO.subtle.digest('SHA-256', u8(v)));
function step(ctr, n) { let carry = n; for (let i = ctr.length - 1; i >= 0 && carry; i--) { const next = ctr[i] + (carry & 0xff); ctr[i] = next & 0xff; carry = Math.floor(carry / 256) + Math.floor(next / 256); } if (carry) throw Error(); }
const mkCtr = (key, ctr) => { let iv = dup(ctr), tail = nil; const ready = CRYPTO.subtle.importKey('raw', u8(key), { name: 'AES-CTR' }, false, ['encrypt']);
  const crypt = async (v) => { const b = u8(v); if (!b.byteLength) return new Uint8Array(0); const key = await ready; if (!tail.byteLength && !(b.byteLength % 16)) { const raw = new Uint8Array(await CRYPTO.subtle.encrypt( { name: 'AES-CTR', counter: iv.slice(), length: 128 }, key, b, )); step(iv, b.byteLength / 16); return raw; } if (b.byteLength <= tail.byteLength) { const out = new Uint8Array(b.byteLength); for (let i = 0; i < b.byteLength; i++) out[i] = b[i] ^ tail[i]; tail = tail.slice(b.byteLength); return out; } const skip = tail.byteLength ? 16 - tail.byteLength : 0; const ctr = iv.slice(); if (skip) { for (let i = ctr.length - 1; i >= 0; i--) if (ctr[i]--) break; } const end = skip + b.byteLength; const block = new Uint8Array(Math.ceil(end / 16) * 16); block.set(b, skip); const raw = new Uint8Array(await CRYPTO.subtle.encrypt( { name: 'AES-CTR', counter: ctr, length: 128 }, key, block, )); tail = raw.slice(end); step(iv, block.byteLength / 16 - (skip ? 1 : 0)); return raw.subarray(skip, end); }; return { crypt }; };
async function cipher(head, secret, reverse) { const mat = dup(u8(head).subarray(8, 56)); if (reverse) mat.reverse(); const key = secret.byteLength ? await sha(cat(mat.subarray(0, 32), secret)) : mat.subarray(0, 32); return mkCtr(key, mat.subarray(32, 48)); }
async function wireHead(head) { const ctr = await cipher(head, nil, false); const raw = await ctr.crypt(head); raw.set(u8(head).subarray(0, 56)); return { wire: raw, cipher: ctr }; }
const hosts = (dc, media) => [ `kws${dc}${media ? '-1' : ''}.web.telegram.org`, `kws${dc}${media ? '' : '-1'}.web.telegram.org`, ];
async function dial({ target, media, signal }) { for (const host of hosts(target + 1, media)) { if (signal?.aborted) throw Error(); const url = `wss://${host}/apiws`; let kws; try { kws = mkWire(new WebSocket(url, 'binary'), 7500, signal); await kws.ready; if (signal?.aborted) throw Error(); return kws; } catch (err) { kws?.close(); if (signal?.aborted) throw err; } } throw Error(); }
const mkWire = (ws, ms, signal) => { const q = [], wait = []; let h = 0, qBytes = 0, closed = false, dead = false, up = false, fault = null; let pWake = null, pNeed, openTimer, readyOk, readyBad;
  const ready = new Promise((ok, bad) => { readyOk = ok; readyBad = bad; });
  const onAbort = () => { end(Error()); close(); };
  const onOpen = () => { if (closed) return; if (ws.protocol !== 'binary') { end(Error()); close(); return; } up = true; clearTimeout(openTimer); readyOk(api); };
  const onData = (v) => { if (closed) return; const b = v instanceof Uint8Array ? v : new Uint8Array(v); if (!b.byteLength) return; const waiter = wait.shift(); if (waiter) waiter.resolve(b); else { q.push(b); qBytes += b.byteLength; if (pWake && (qBytes >= pNeed || b.byteLength >= CFG.dnPack)) pWake(); } };
  const end = (err = null) => { if (closed) return; closed = true; fault = err; clearTimeout(openTimer); signal?.removeEventListener('abort', onAbort); if (!up) readyBad(err || Error()); pWake?.(); for (const waiter of wait.splice(0)) err ? waiter.reject(err) : waiter.resolve(null); };
  const write = async (v) => { await ready; if (closed) throw fault || Error(); ws.send(u8(v)); };
  const take = async () => { await ready; if (h < q.length) { const msg = q[h]; q[h++] = null; qBytes -= msg.byteLength; trim(); return msg; } if (fault) throw fault; if (closed) return null; return new Promise((ok, bad) => wait.push({ resolve: ok, reject: bad })); };
  const pack = async () => { const first = await take(); if (dead) return null; if (!first || first.byteLength >= CFG.dnPack) return first; if (!closed && qBytes < CFG.dnPack - first.byteLength) { await new Promise(ok => { pNeed = CFG.dnPack - first.byteLength; const timer = setTimeout(() => pWake?.(), CFG.dnMs); pWake = () => { clearTimeout(timer); pWake = null; ok(); }; }); } if (dead) return null; let n = first.byteLength, end = h; while (end < q.length && n + q[end].byteLength <= CFG.dnPack) { n += q[end++].byteLength; } if (end === h) return first; const b = new Uint8Array(n); b.set(first); let o = first.byteLength; while (h < end) { const part = q[h]; q[h++] = null; b.set(part, o); o += part.byteLength; qBytes -= part.byteLength; } trim(); return b; };
  const trim = () => { if (h === q.length) { q.length = 0; h = 0; } else if (h >= 256 && h * 2 >= q.length) { q.splice(0, h); h = 0; } };
  const close = () => { if (dead) return; dead = true; if (!closed) end(); q.length = h = qBytes = 0; try { ws.close(1000); } catch {} };
  const api = { ready, write, readPack: pack, close, get closed() { return closed; } };
  ws.binaryType = 'arraybuffer'; ws.addEventListener('open', onOpen);
  ws.addEventListener('message', e => onData(e.data)); ws.addEventListener('error', () => end(Error()));
  ws.addEventListener('close', e => end( e?.code && e.code !== 1000 ? Error() : null, ));
  openTimer = setTimeout(() => { end(Error()); close(); }, ms);
  signal?.addEventListener('abort', onAbort, { once: true }); if (signal?.aborted) onAbort(); return api; };
const mkPkt = mode => { let tail = nil;
  const push = (v) => { const b = u8(v); if (b.byteLength) tail = tail.byteLength ? cat(tail, b) : b; const pkts = []; let o = 0; for (;;) { const avail = tail.byteLength - o; let hLen; let pLen; if (mode === 0xef) { if (avail < 1) break; let words = tail[o] & 0x7f; if (words === 0x7f) { if (avail < 4) break; words = tail[o + 1] | (tail[o + 2] << 8) | (tail[o + 3] << 16); hLen = 4; } else hLen = 1; pLen = words * 4; } else { if (avail < 4) break; pLen = new DataView( tail.buffer, tail.byteOffset + o, 4, ).getUint32(0, true) & 0x7fffffff; hLen = 4; } if (!pLen || pLen > 8 * 1024 * 1024) throw Error(); const total = hLen + pLen; if (avail < total) break; pkts.push(tail.subarray(o, o + total)); o += total; } if (o) tail = o === tail.byteLength ? nil : tail.slice(o); if (tail.byteLength > 8 * 1024 * 1024 + 4) throw Error(); return pkts; }; const clear = () => { tail = nil; }; return { push, clear }; };
const mkStream = ({ secret, emit, onClose }) => { let hdr = nil, cIn = null, cOut = null, kIn = null, kOut = null, peer = null, pkt = null; let init = false, closed = false, chain = Promise.resolve(); const ac = new AbortController(), uq = new Set();
  const push = (v) => { if (closed) return Promise.reject(Error()); const job = { bytes: u8(v) }; uq.add(job); chain = chain.then(async () => { if (closed) throw Error(); if (!job.bytes) return job.result; const jobs = [job]; let n = job.bytes.byteLength; for (const next of uq) { if (next === job) continue; if (n >= CFG.upPack || n + next.bytes.byteLength > CFG.upPack) break; n += next.bytes.byteLength; jobs.push(next); } const b = jobs.length === 1 ? job.bytes : cat(...jobs.map(x => x.bytes)); for (const item of jobs) { uq.delete(item); item.bytes = null; } const out = await feed(b); for (const item of jobs) item.result = out; return out; }); return chain; };
  const feed = async (b) => { if (closed) throw Error(); if (init && peer.closed) return false; if (!b.byteLength) return; if (!init) { const need = 64 - hdr.byteLength; if (b.byteLength < need) { hdr = cat(hdr, b); return; } hdr = cat(hdr, b.subarray(0, need)); await start(); const rest = b.subarray(need); if (rest.byteLength) return write(rest); return; } return write(b); };
  const start = async () => { const raw = hdr; const cr = await cipher(raw, secret, false); const plain = await cr.crypt(raw); if (closed) return; const info = headOf(plain); const head = mkHead(info.mode, info.target, info.media); const [cw, out, kr] = await Promise.all([ cipher(raw, secret, true), wireHead(head), cipher(head, nil, true), ]); if (closed) return; const kws = await dial({ target: info.target, media: info.media, signal: ac.signal, }); if (closed) { kws.close(); return; } peer = kws; cIn = cr; cOut = cw; kOut = out.cipher; kIn = kr; pkt = mkPkt(info.mode); await kws.write(out.wire); if (closed) return; hdr = nil; init = true; pump().catch(() => close()); };
  const write = async (raw) => { if (closed || peer.closed) return false; const plain = await cIn.crypt(raw); if (closed || peer.closed) return false; const pkts = pkt.push(plain); for (let start = 0; start < pkts.length;) { let end = start + 1, n = pkts[start].byteLength; while (end < pkts.length && n + pkts[end].byteLength <= CFG.upPack) { n += pkts[end++].byteLength; } const first = pkts[start]; const b = end === start + 1 ? first : new Uint8Array(first.buffer, first.byteOffset, n); if (closed || peer.closed) return false; const wire = await kOut.crypt(b); for (let o = 0; start < end; start++) { if (closed || peer.closed) return false; const n = pkts[start].byteLength; try { await peer.write(wire.subarray(o, o + n)); } catch (err) { if (closed || peer.closed) return false; throw err; } o += n; } } };
  const pump = async () => { while (!closed) { const b = await peer.readPack(); if (closed) return; if (!b) return close(); const plain = await kIn.crypt(b); if (closed) return; const raw = await cOut.crypt(plain); if (closed) return; await emit(raw); } };
  const close = () => { if (closed) return; closed = true; ac.abort(); try { peer?.close(); } catch {} for (const job of uq) job.bytes = null; uq.clear(); hdr = nil; pkt?.clear(); cIn = cOut = kIn = kOut = peer = null; try { onClose(); } catch {} }; return { push, close }; };
const mkSession = ({ secret, sid, onClose, lease }) => { let sock = null, closed = false, tx = Promise.resolve(), cur = null;
  const attach = (ws) => { if (sock || closed) throw Error(); sock = ws; ws.accept({ allowHalfOpen: true }); ws.binaryType = 'arraybuffer'; ws.addEventListener('message', e => { if (closed) return; try { onData(e.data); } catch { close(1008); } }); ws.addEventListener('close', () => close()); ws.addEventListener('error', () => close()); };
  const onData = (v) => { if (closed) return; if (lease?.deleted) { return close(1000); } if (typeof v === 'string') throw Error(); const b = v instanceof Uint8Array ? v : new Uint8Array(v); if (!b.byteLength || b.byteLength > 2 * 1024 * 1024) { throw Error(); } for (const frame of frames(b)) { if (closed) return; const delta = check(frame); if (frame.sid !== sid) throw Error(); if (!cur && frame.type !== 1) throw Error(); if (frame.type !== 1 && cur?.closed) continue; if (frame.type === 1) open(); else if (frame.type === 2) write(frame.payload); else if (frame.type === 4) grant(delta); else if (frame.type === 3) end(false); else throw Error(); } };
  const send = (type, data = nil) => { const out = enc(type, sid, data); const st = type === 2 || type === 4 ? cur : null; tx = tx.then(() => { if (closed) throw Error(); if ((type === 2 || type === 4) && (!st || st.closed)) return; sock.send(out); }); return tx; };
  const open = () => { if (closed) return; if (cur) throw Error(); const st = { in: 4 * 1024 * 1024, out: 4 * 1024 * 1024, wake: null, closed: false, proxy: null, pItems: 0, }; st.proxy = mkStream({ secret, emit: b => emitDn(st, b), onClose: () => { if (!closed && !st.closed) end(true); }, }); cur = st; };
  const write = (data) => { if (closed || cur?.closed) return; const st = cur; if (!st || st.closed) throw Error(); const n = data.byteLength; if (n > st.in) throw Error(); if (st.pItems >= 16384) { throw Error(); } st.in -= n; st.pItems++; st.proxy.push(data).then(accepted => { freeUp(st); if (closed || st.closed || accepted === false) return; st.in += n; const delta = new Uint8Array(4); new DataView(delta.buffer).setUint32(0, n); send(4, delta).catch(() => close()); }, () => { freeUp(st); if (!closed && !st.closed) st.proxy.close(); }).catch(() => close()); };
  const freeUp = (st) => { if (st.closed) return; st.pItems--; };
  const emitDn = async (st, b) => { for (let o = 0; o < b.byteLength; ) { while (!closed && !st.closed && st.out === 0) { await new Promise(ok => { st.wake = ok; }); } if (closed || st.closed) throw Error(); const n = Math.min(64 * 1024, b.byteLength - o, st.out); st.out -= n; await send(2, b.subarray(o, o + n)); o += n; } };
  const grant = (n) => { if (closed || cur?.closed) return; const st = cur; if (!st || st.closed) throw Error(); st.out = Math.min(0xffffffff, st.out + n); wake(st); };
  const stop = (st) => { st.closed = true; st.pItems = 0; wake(st); st.proxy.close(); };
  const end = (notify) => { if (closed || cur?.closed) return; const st = cur; if (!st) throw Error(); stop(st); if (notify) send(3).then(() => close(), () => close()); else close(); };
  const close = (code = 1000, reason = '') => { if (closed) return; closed = true; if (cur) stop(cur); cur = null; try { sock?.close(code, reason); } catch {} onClose?.(); onClose = null; }; return { attach, close }; };
function mkPage(host, boot) { const nonce = b64(rand(18));
  const body = `<script nonce="__NONCE__">
(()=>{'use strict'; const origin=__ORIGIN__,boot=__BOOTSTRAP__;
const aNonce=/^#android=([A-Za-z0-9_-]{43})$/.exec(location.hash)?.[1]??''; history.replaceState(null,'',location.pathname);
let init=false,closed=false,port=null,token='',started=false,delSent=false; let qBytes=0,qItems=0;
const lanes=new Map(),used=new Set(),qMax=__Q_MAX__,iMax=__I_MAX__,msgMax=2097152; const laneMax=__LANE_MAX__,laneItems=__LANE_ITEMS__;
const state=st=>port&&!closed&&port.postMessage({t:'status',state:st});
const opts=(method,token,body,keepalive)=>({ method,body,keepalive:!!keepalive,mode:'same-origin',credentials:'omit',cache:'no-store',redirect:'error',referrerPolicy:'no-referrer', headers:{...(token&&{Authorization:'Bearer '+token}),...(body&&{'Content-Type':'application/octet-stream'})} });
function check(v){ if(!(v instanceof ArrayBuffer)||!v.byteLength||v.byteLength>msgMax)throw Error(); const view=new DataView(v);let o=0,frames=0; while(o<v.byteLength){ if(v.byteLength-o<8||frames++>=4096)throw Error(); const type=view.getUint8(o),n=view.getUint32(o+4),end=o+8+n; if(n>1048576||end>v.byteLength||(type===2&&!n))throw Error(); o=end; } return v; }
function split(v){ check(v);const view=new DataView(v),out=[];let o=0; while(o<v.byteLength){ const end=o+8+view.getUint32(o+4); out.push(o===0&&end===v.byteLength?v:v.slice(o,end));o=end; } return out; }
function sid(v){const b=new Uint8Array(v);return (b[1]<<16)|(b[2]<<8)|b[3];}
function hold(lane,v){ let buffered=0;for(const {ws} of lanes.values())buffered+=ws?.bufferedAmount??0; const own=lane.ws?.bufferedAmount??0; if(qBytes+buffered>qMax-v.byteLength||qItems>=iMax ||lane.bytes+own>laneMax-v.byteLength||lane.items>=laneItems)return false; qBytes+=v.byteLength;qItems++;lane.bytes+=v.byteLength;lane.items++;return true; }
function free(lane,v){qBytes-=v.byteLength;qItems--;lane.bytes-=v.byteLength;lane.items--;}
function fail(){ if(closed)return;state('failed');port?.postMessage({t:'close'});close(true); }
function drop(){ if(delSent||!token)return;delSent=true; fetch(origin+'/api/v1/session',opts('DELETE',token,null,true)).catch(()=>{}); }
function pump(lane){ const ws=lane.ws; if(closed||lane.done||!ws||ws.readyState!==WebSocket.OPEN||!lane.pending.length)return; if(ws.bufferedAmount>=msgMax){lane.timer ||= setTimeout(()=>{lane.timer=0;pump(lane);},10);return;} try{ const v=lane.pending.shift();ws.send(v);free(lane,v); port.postMessage({t:'traffic',up:v.byteLength,down:0}); if(lane.pending.length)queueMicrotask(()=>pump(lane)); }catch{fail();} }
function push(v){ try{for(const frame of split(v))pushLane(frame);} catch{fail();} }
function end(lane,notify){ if(lane.done)return;lane.done=true;if(lane.timer)clearTimeout(lane.timer); qBytes-=lane.bytes;qItems-=lane.items;lane.bytes=lane.items=0;lane.pending.length=0;lanes.delete(lane.id); try{lane.ws?.close();}catch{} if(notify&&port&&!closed){const frame=new ArrayBuffer(8),b=new Uint8Array(frame);b[0]=3;b[1]=lane.id>>>16;b[2]=lane.id>>>8;b[3]=lane.id;port.postMessage(frame,[frame]);} }
function open(lane){ const target=origin.replace(/^https:/,'wss:')+'/api/v1/ws'; const ws=lane.ws=new WebSocket(target,'tproxy-lane-v1.'+token+'.'+lane.id);ws.binaryType='arraybuffer'; ws.onopen=()=>{if(closed||lane.done){ws.close();return;}lane.opened=true;state('connected');pump(lane);}; ws.onmessage=e=>{ if(closed||lane.done)return; try{ const frames=split(e.data); if(frames.some(frame=>sid(frame)!==lane.id))throw Error(); const ended=frames.some(frame=>new Uint8Array(frame)[0]===3); if(ended)lane.rClosed=true; port.postMessage({t:'traffic',up:0,down:e.data.byteLength});port.postMessage(e.data,[e.data]);state('connected'); if(ended)end(lane,false); }catch{fail();} }; ws.onerror=()=>{}; ws.onclose=()=>{if(closed||lane.done)return;if(!lane.opened){fail();return;}end(lane,!lane.lClosed&&!lane.rClosed);}; }
function pushLane(v){ const id=sid(v),type=new Uint8Array(v)[0];let lane=lanes.get(id); if(!id)throw Error(); if(!lane&&(type===2||type===3||type===4))return; if(!lane){ if(type!==1||used.has(id)||lanes.size>=__LANE_LIMIT__||used.size>=4096)throw Error(); used.add(id);lane={id,ws:null,pending:[],bytes:0,items:0,timer:0,opened:false,done:false,lClosed:false,rClosed:false};lanes.set(id,lane); } if(lane.lClosed)return; if(type===3&&!lane.opened){end(lane,false);return;} if(!hold(lane,v))throw Error(); lane.pending.push(v);if(type===3)lane.lClosed=true; if(token){if(!lane.ws)open(lane);else pump(lane);} }
async function create(first){ try{ state('connecting'); const res=await fetch(origin+'/api/v1/session',opts('POST',boot,first)); if(res.status!==200||res.headers.get('X-Carrier-Mode')!=='websocket-lanes')throw Error(); token=res.headers.get('X-Session-Token')??''; if(!token)throw Error(); const welcome=await res.arrayBuffer();check(welcome); if(closed){drop();return;} port.postMessage(welcome,[welcome]);state('connected'); for(const lane of lanes.values())if(!lane.ws)open(lane); }catch{fail();} }
function close(notify){ if(closed)return;closed=true; for(const lane of [...lanes.values()])end(lane,false);used.clear(); if(notify)drop(); port?.close(); }
function start(next){ init=true;port=next; port.onmessage=msg=>{ const data=msg.data; if(data instanceof ArrayBuffer){ if(!started){ try{check(data);}catch{fail();return;} started=true;create(data); }else push(data); }else if(data&&data.t==='close')close(true); }; port.start();state('connecting'); }
addEventListener('message',e=>{ if(init||e.source!==parent||e.data===null||typeof e.data!=='object')return; const keys=Object.keys(e.data).sort(); if(keys.length!==2||keys[0]!=='t'||keys[1]!=='v'||e.data.t!=='tproxy-init'||e.data.v!==1||e.ports.length!==1)return; let src;try{src=new URL(e.origin);}catch{return;} if(src.protocol!=='http:'||src.hostname!=='127.0.0.1'||!src.port||src.origin!==e.origin)return; start(e.ports[0]); }); const android=globalThis.TelegramWebProxy;
if(!init&&aNonce&&android&&typeof android.postMessage==='function'){ const aPort={onmessage:null,start(){},close(){android.onmessage=null;},postMessage(v){ if(v instanceof ArrayBuffer){for(const frame of split(v))android.postMessage(frame);} else android.postMessage(JSON.stringify(v)); }}; android.onmessage=e=>{ let data=e.data;if(typeof data==='string'){try{data=JSON.parse(data);}catch{return;}} aPort.onmessage?.({data}); }; start(aPort);android.postMessage(JSON.stringify({t:'tproxy-android-init',v:1,nonce:aNonce})); } addEventListener('pagehide',()=>close(true),{once:true}); })();
</script>`.replaceAll('__NONCE__', nonce).replace('__ORIGIN__', JSON.stringify(`https://${host}`))
    .replace('__BOOTSTRAP__', JSON.stringify(String(boot)))
    .replace('__LANE_MAX__', String(CFG.laneMax))
    .replace('__LANE_ITEMS__', String(CFG.laneItems))
    .replace('__Q_MAX__', String(CFG.qMax))
    .replace('__I_MAX__', String(CFG.iMax))
    .replace('__LANE_LIMIT__', String(CFG.laneLimit));
  const csp = [ "default-src 'none'", "base-uri 'none'", "child-src 'none'", `connect-src 'self' wss://${host}`, "font-src 'none'", "form-action 'none'", 'frame-ancestors http://127.0.0.1:*', "frame-src 'none'", "img-src 'none'", "manifest-src 'none'", "media-src 'none'", "object-src 'none'", `script-src 'nonce-${nonce}'`, "style-src 'none'", "worker-src 'none'", 'sandbox allow-same-origin allow-scripts', ].join('; '); return { body, csp }; }

// ===== 管理面板：配置加载 =====
const ENV_MAP = {
  dnPack: 'DN_PACK', upPack: 'UP_PACK', dnMs: 'DN_MS',
  laneLimit: 'LANE_LIMIT', laneMax: 'LANE_MAX', laneItems: 'LANE_ITEMS',
  qMax: 'Q_MAX', iMax: 'I_MAX', bootTTL: 'BOOT_TTL', sessTTL: 'SESS_TTL',
};
const FIELD_META = [
  ['dnPack', '下行聚合上限（字节）', 'DN_PACK'],
  ['upPack', '上行合包目标（字节）', 'UP_PACK'],
  ['dnMs', '下行静默窗口（毫秒）', 'DN_MS'],
  ['laneLimit', '单会话并发 lane 数', 'LANE_LIMIT'],
  ['laneMax', '单 lane 字节上限', 'LANE_MAX'],
  ['laneItems', '单 lane 条数上限', 'LANE_ITEMS'],
  ['qMax', '整会话字节上限', 'Q_MAX'],
  ['iMax', '整会话条数上限', 'I_MAX'],
  ['bootTTL', 'bootstrap 有效期（毫秒）', 'BOOT_TTL'],
  ['sessTTL', 'session 有效期（毫秒）', 'SESS_TTL'],
];
let KV_CACHE = { ts: 0, data: null };
async function loadConfig(env) {
  const cfg = { ...DEFAULTS };
  for (const [k, ev] of Object.entries(ENV_MAP)) {
    const raw = env[ev];
    if (raw != null && String(raw).trim() !== '') {
      const n = Number(String(raw).trim());
      if (Number.isFinite(n)) cfg[k] = n;
    }
  }
  if (env.CONFIG && env.CONFIG.get) {
    try {
      const now = Date.now();
      if (now - KV_CACHE.ts < 60000 && KV_CACHE.data) {
        Object.assign(cfg, KV_CACHE.data);
      } else {
        const stored = await env.CONFIG.get('proxy', { type: 'json' });
        if (stored && typeof stored === 'object') { Object.assign(cfg, stored); KV_CACHE = { ts: now, data: stored }; }
      }
    } catch {}
  }
  Object.assign(cfg, MEM);
  Object.assign(CFG, cfg);
  return cfg;
}

// ===== 管理面板：鉴权 =====
function json(o, status = 200) { return new Response(JSON.stringify(o), { status, headers: { 'Content-Type': 'application/json; charset=utf-8' } }); }
function safeEq(a, b) { if (typeof a !== 'string' || typeof b !== 'string' || a.length !== b.length) return false; let d = 0; for (let i = 0; i < a.length; i++) d |= a.charCodeAt(i) ^ b.charCodeAt(i); return d === 0; }
async function hmacRaw(keyBytes, msg) { const k = await CRYPTO.subtle.importKey('raw', u8(keyBytes), { name: 'HMAC', hash: 'SHA-256' }, false, ['sign']); return new Uint8Array(await CRYPTO.subtle.sign('HMAC', k, u8(msg))); }
async function adminTok(admin) { return b64(await hmacRaw(txt.encode(String(admin)), txt.encode('tg-admin-v1'))); }
function getCookie(headers, name) { const c = headers.get('Cookie') || ''; for (const part of c.split(';')) { const t = part.trim(); const eq = t.indexOf('='); if (eq === -1) continue; if (t.slice(0, eq) === name) return decodeURIComponent(t.slice(eq + 1)); } return null; }
function sanitizeConfig(body) { const out = {}; for (const [k] of FIELD_META) { const v = body?.[k]; if (typeof v === 'number' && Number.isFinite(v)) out[k] = v; else if (typeof v === 'string' && v.trim() !== '' && Number.isFinite(Number(v))) out[k] = Number(v); } return out; }

// ===== 管理面板：页面渲染 =====
function pageWrap(title, inner) { return `<!doctype html><html lang="zh"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>${title}</title><style>
*{box-sizing:border-box}body{margin:0;font:14px/1.6 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"PingFang SC","Microsoft YaHei",sans-serif;background:#0f1420;color:#e6e9f0}
.wrap{max-width:920px;margin:0 auto;padding:24px}.card{background:#171d2b;border:1px solid #232c40;border-radius:12px;padding:20px;margin-bottom:18px}
h1{font-size:20px;margin:0 0 4px}h2{font-size:15px;margin:18px 0 10px;color:#9fb0d0}.muted{color:#8492ad}.row{display:flex;gap:12px;flex-wrap:wrap;align-items:center}
input,button{font:inherit}input{padding:8px 10px;border-radius:8px;border:1px solid #2c3650;background:#0f1420;color:#e6e9f0;width:220px}
button{cursor:pointer;border:0;border-radius:8px;padding:9px 16px;background:#3b82f6;color:#fff;font-weight:600}
button.ghost{background:#222b40;color:#cdd6ea}.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:12px}
.fld label{display:block;font-weight:600;margin-bottom:4px}.fld .sub{color:#8492ad;font-size:12px;margin-top:3px}
.code{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;background:#0b0f18;border:1px solid #232c40;border-radius:8px;padding:10px;word-break:break-all;color:#9fe6c4}
.copy{margin-left:8px;background:#222b40;color:#cdd6ea;padding:5px 10px;font-size:12px}
.status{display:inline-block;padding:3px 10px;border-radius:999px;font-size:12px;font-weight:600}
.ok{background:#10351f;color:#5ef0a0}.bad{background:#3a1620;color:#ff8aa0}
a{color:#6ea8fe}hr{border:0;border-top:1px solid #232c40;margin:16px 0}
</style></head><body><div class="wrap">${inner}</div></body></html>`; }

function renderLogin(err) {
  const e = err ? `<p class="status bad">${err}</p>` : '';
  return pageWrap('登录 · TGProxy 管理面板', `
    <div class="card"><h1>TGProxy 管理面板</h1><p class="muted">请输入 ADMIN 访问密码。</p>${e}
    <form method="post" action="/admin" style="margin-top:12px" class="row">
      <input type="password" name="password" placeholder="ADMIN 密码" autofocus>
      <button type="submit">登录</button>
    </form></div>`);
}
function renderNoAdmin() {
  return pageWrap('未配置 ADMIN', `
    <div class="card"><h1>未配置 ADMIN 密码</h1>
    <p class="muted">管理面板需要设置 <b>ADMIN</b> 变量（任意非空字符串）才能启用。请在 Worker 变量/密钥中添加：</p>
    <p class="code">ADMIN = 你的密码</p>
    <p class="muted" style="margin-top:10px">代理功能本身不依赖 ADMIN；仅管理面板需要它。</p></div>`);
}
function mask(v) { const s = String(v); if (s.length <= 8) return '••••'; return s.slice(0, 6) + '…' + s.slice(-4); }
function renderPanel({ cfg, host, desktop, android, hasKV, secret, boot }) {
  const cfgRows = FIELD_META.map(([k, label, ev]) => `
    <div class="fld"><label>${label}</label>
      <input name="${k}" value="${cfg[k]}" inputmode="numeric">
      <div class="sub">env: ${ev} · 当前值 ${cfg[k]}</div></div>`).join('');
  const kvNote = hasKV
    ? '<p class="status ok">已绑定 KV，保存的配置将持久化生效。</p>'
    : '<p class="status bad">未绑定 KV（CONFIG）。保存将仅写入内存，Worker 重启/扩容后丢失；建议绑定 KV 命名空间（变量名 CONFIG）以持久化。</p>';
  return pageWrap('TGProxy 管理面板', `
    <div class="card"><div class="row" style="justify-content:space-between">
      <div><h1>TGProxy 管理面板</h1><p class="muted">域名 ${host} · <span id="health" class="status">检测中…</span></p></div>
      <div class="row"><a class="button ghost" href="/admin?logout=1" style="text-decoration:none"><button class="ghost" type="button">退出登录</button></a></div>
    </div></div>

    <div class="card"><h2>连接链接（直接复制使用）</h2>
      ${desktop ? `<p class="muted">Telegram Desktop（带 bridge 签名）：</p>
      <div><span class="code" id="desktop">${desktop}</span><button class="copy" data-copy="desktop">复制</button></div>
      <p class="muted" style="margin-top:12px">Telegram Android（#android 随机串）：</p>
      <div><span class="code" id="android">${android}</span><button class="copy" data-copy="android">复制</button></div>
      <p class="muted" style="margin-top:10px">Desktop 链接签名绑定当前域名，换域名需在面板重新复制。Android 链接每次刷新页面会变化，属正常。</p>`
      : '<p class="status bad">SECRET 未配置，无法生成连接链接。请先在 Worker 变量中设置 SECRET。</p>'}
    </div>

    <div class="card"><h2>密钥（只读）</h2>
      <p class="muted">SECRET：<span class="code">${mask(secret)}</span></p>
      <p class="muted">BOOT：<span class="code">${mask(boot)}</span></p>
      <p class="muted">请勿泄露这两个值。如需更换请到 Worker 变量中修改 SECRET / BOOT。</p>
    </div>

    <div class="card"><h2>配置项</h2>${kvNote}
      <form id="cfgForm"><div class="grid">${cfgRows}</div>
      <div class="row" style="margin-top:16px">
        <button type="submit">保存配置</button>
        <button type="button" class="ghost" id="resetBtn">恢复默认</button>
        <span id="saveMsg" class="muted"></span>
      </div></form>
    </div>

    <script>
    document.querySelectorAll('.copy').forEach(b=>b.onclick=()=>{const t=document.getElementById(b.dataset.copy).textContent;navigator.clipboard.writeText(t).then(()=>{const o=b.textContent;b.textContent='已复制';setTimeout(()=>b.textContent=o,1200);});});
    fetch('/health').then(r=>r.json()).then(j=>{const e=document.getElementById('health');if(j&&j.ok){e.textContent='运行正常';e.className='status ok';}else{throw 0;}}).catch(()=>{const e=document.getElementById('health');e.textContent='异常';e.className='status bad';});
    document.getElementById('cfgForm').onsubmit=async e=>{e.preventDefault();const fd=new FormData(e.target);const body={};fd.forEach((v,k)=>body[k]=v);const r=await fetch('/admin/api/config',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});const j=await r.json().catch(()=>({}));document.getElementById('saveMsg').textContent=r.ok?(j.stored?'已保存并持久化':'已保存（仅内存，建议绑定KV）'):('失败：'+(j.error||r.status));};
    document.getElementById('resetBtn').onclick=async()=>{if(!confirm('确认恢复全部默认配置？'))return;const r=await fetch('/admin/api/config',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({})});if(r.ok)location.reload();};
    </script>`);
}

// ===== 管理面板：路由 =====
async function adminRoute(req, env, url, method, headers) {
  const admin = String(env.ADMIN || '').trim();
  if (!admin) return new Response(renderNoAdmin(), { status: 200, headers: { 'Content-Type': 'text/html; charset=utf-8' } });
  try { RT = mkCfg(env); } catch {}
  await loadConfig(env);
  const cookie = getCookie(headers, 'tg_admin');
  const authed = cookie && safeEq(cookie, await adminTok(admin));

  if (url.pathname === '/admin' && method === 'POST') {
    const form = await req.formData().catch(() => null);
    const pw = form ? String(form.get('password') || '') : '';
    if (safeEq(pw, admin)) {
      const h = new Headers({ 'Content-Type': 'text/html; charset=utf-8' });
      h.append('Set-Cookie', `tg_admin=${await adminTok(admin)}; Path=/; HttpOnly; SameSite=Lax; Max-Age=86400`);
      h.set('Location', '/admin');
      return new Response(null, { status: 302, headers: h });
    }
    return new Response(renderLogin('密码错误'), { status: 401, headers: { 'Content-Type': 'text/html; charset=utf-8' } });
  }
  if (url.pathname === '/admin' && method === 'GET' && url.searchParams.get('logout')) {
    const h = new Headers({ 'Content-Type': 'text/html; charset=utf-8' });
    h.append('Set-Cookie', 'tg_admin=; Path=/; HttpOnly; Max-Age=0');
    h.set('Location', '/admin');
    return new Response(null, { status: 302, headers: h });
  }
  if (url.pathname === '/admin/api/config' && method === 'POST') {
    if (!authed) return json({ error: 'unauthorized' }, 401);
    let body; try { body = await req.json(); } catch { return json({ error: 'bad json' }, 400); }
    const clean = sanitizeConfig(body);
    if (env.CONFIG && env.CONFIG.put) { await env.CONFIG.put('proxy', JSON.stringify(clean)); }
    else { MEM = clean; }
    Object.assign(CFG, clean);
    return json({ ok: true, stored: !!(env.CONFIG && env.CONFIG.put), cfg: { ...CFG } });
  }
  if (url.pathname === '/admin' && method === 'GET') {
    if (!authed) return new Response(renderLogin(), { status: 200, headers: { 'Content-Type': 'text/html; charset=utf-8' } });
    const cfg = { ...CFG };
    const host = url.hostname;
    let desktop = '', android = '';
    if (RT.secret) {
      const bridgeSig = await mkCap(RT.secret, host);
      desktop = `https://${host}/?bridge=${bridgeSig}`;
      android = `https://${host}/#android=${b64(rand(32))}`;
    }
    const html = renderPanel({ cfg, host, desktop, android, hasKV: !!(env.CONFIG && env.CONFIG.put), secret: RT.secret || '', boot: RT.boot || '' });
    return new Response(html, { status: 200, headers: { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' } });
  }
  return reply();
}

// ===== 主路由 =====
const route = async (req, env) => {
  const url = new URL(req.url), { pathname: path, origin } = url, { method, headers } = req;
  // 管理面板优先：即使 SECRET/BOOT 未配也可进入（用于排错/查看配置）
  if (path === '/admin' || path.startsWith('/admin/')) return adminRoute(req, env, url, method, headers);
  let cfg;
  try { cfg = mkCfg(env); } catch { return ['/', '/health', '/api/v1/session', '/api/v1/ws'].includes(path) ? reply(null, 500) : reply(); }
  RT = cfg;
  await loadConfig(env);

  if (path === '/' && (method === 'GET' || method === 'HEAD')) { let host = null; if (method === 'GET') { try { host = await bridge(url, cfg.secret); } catch {} } if (host) { const boot = await mkBoot(); const page = mkPage(host, boot); return new Response(page.body, { status: 200, headers: { 'Content-Type': 'text/html; charset=utf-8', 'Content-Security-Policy': page.csp, 'Cache-Control': 'no-store', 'Referrer-Policy': 'no-referrer', 'X-Content-Type-Options': 'nosniff', 'Permissions-Policy': [ 'accelerometer=()', 'autoplay=()', 'camera=()', 'clipboard-read=()', 'clipboard-write=()', 'display-capture=()', 'encrypted-media=()', 'fullscreen=()', 'geolocation=()', 'gyroscope=()', 'hid=()', 'idle-detection=()', 'magnetometer=()', 'microphone=()', 'midi=()', 'payment=()', 'picture-in-picture=()', 'publickey-credentials-create=()', 'publickey-credentials-get=()', 'screen-wake-lock=()', 'serial=()', 'usb=()', 'web-share=()', 'xr-spatial-tracking=()', ].join(', '), }, }); } return new Response(method === 'HEAD' ? null : '<!doctype html><meta charset="utf-8"><title>Connection</title>', { status: 200, headers: { 'Content-Type': 'text/html; charset=utf-8' }, }); }
  if (path === '/health') { return new Response('{"ok":true}', { headers: { 'content-type': 'application/json; charset=utf-8' }, }); }
  if (path === '/api/v1/session') { const auth = bearer(headers.get('Authorization')); if (method === 'DELETE') { if (!auth || !(await verify(auth, cfg.boot, 'session'))) { return reply(); } let lease = leases.get(auth); if (!lease) leases.set(auth, lease = mkLease(auth)); lease.deleted = true; return reply(null, 204); } if (method !== 'POST' || !auth || !binary(req)) { return reply(); } if (!(await authBoot(auth, cfg.boot))) { return reply(); } try { const body = new Uint8Array(await req.arrayBuffer()); hello(body); const token = await mkSess(); return new Response(enc(0x11, 0), { status: 200, headers: { 'Content-Type': 'application/octet-stream', 'Cache-Control': 'no-store', 'X-Session-Token': token, 'X-Carrier-Mode': 'websocket-lanes', }, }); } catch { return reply(); } }
  if (path !== '/api/v1/ws' || method !== 'GET' || headers.get('Upgrade')?.toLowerCase() !== 'websocket' || (headers.has('Origin') && headers.get('Origin') !== origin)) { return reply(); }
  const offers = protos(req); const proto = offers.length === 1 ? offers[0] : null;
  const parts = proto?.split('.') ?? [], [kind, token = '', id] = parts, sid = Number(id);
  if (parts.length !== 3 || kind !== 'tproxy-lane-v1' || !/^[1-9][0-9]{0,7}$/.test(id) || sid > 0xffffff || !(await verify(token, cfg.boot, 'session'))) { return reply(); } const now = Date.now();
  for (const [key, v] of leases) if (v.expires <= now && !v.active.size) leases.delete(key); let lease = leases.get(token);
  if (!lease) { if (leases.size >= 4096) return reply(null, 503); leases.set(token, lease = mkLease(token)); }
  if (lease.deleted || lease.used.has(sid) || lease.active.size >= CFG.laneLimit || lease.used.size >= 4096) { return reply(null, 409); } lease.used.add(sid); lease.active.add(sid);
  const sess = mkSession({ secret: cfg.key, sid, lease, onClose: () => lease.active.delete(sid), }); const { 0: client, 1: server } = new WebSocketPair();
  try { sess.attach(server); } catch { sess.close(); return reply(null, 409); }
  return new Response(null, { status: 101, webSocket: client, headers: { 'Sec-WebSocket-Protocol': proto, 'Sec-WebSocket-Extensions': '', }, }); };
