'use strict';
/*
  Minhocaos — servidor da partida.

  O servidor roda a simulação inteira (minhocas, bolinhas, esferas de poder, colisões e cortes)
  e manda o estado para todos os jogadores 20 vezes por segundo. Cada jogador só envia a direção
  e se está acelerando. Assim existe uma única verdade: quem bateu, bateu para todo mundo.

  Sem dependências: precisa só de Node 18 ou mais novo.
    node server.js            → abre na porta 8080 (ou na variável PORT)
  A página do jogo fica em public/index.html e é servida em "/".
  O WebSocket do jogo fica em "/ws". "/health" responde "ok" para o provedor de hospedagem.
*/
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');

const PORT = +process.env.PORT || 8080;
const PUBLIC = path.join(__dirname, 'public');
const DEV = !!process.env.MINHOCAOS_DEV;          // libera comandos de teste
const SIM_LAG = +process.env.MINHOCAOS_LAG || 0;  // atraso artificial (ms, ida e volta) para testes

/* ================= regras (iguais às do cliente) ================= */
const PROTO = 5;
const TAU = Math.PI * 2, WORLD_R = 3200;
const BASE_SPEED = 205, BOOST_SPEED = 410, TURBO_SPEED = 480;
const FOOD_N = 1680, ORB_N = 28;
const MIN_BOOST = 20, GELO_R = 620, IMA_R = 240, MAX_SEG = 260, BOOST_DROP_V = 2.25;
const TICK_MS = 25, SEND_EVERY = 2;               // simulação a 40 Hz, envio a 20 Hz
const DROP_TTL = 110, ORB_DELAY = 1.5, MAX_PLAYERS = 40, MAX_DROPS = 2500, MAX_ROOMS = 200;
const POWER_DUR = { ima: 10, turbo: 6, serra: 7, gelo: 6, dobro: 12, fogo: 10, lento: 6, cego: 6, veneno: 6 };
const PBIT = { ima: 1, turbo: 2, fogo: 4, serra: 8, gelo: 16, dobro: 32, lento: 256, cego: 512, veneno: 1024 }, F_BOOST = 64, F_FROZEN = 128;
const ORB_WEIGHTS = [['ima', 30], ['turbo', 30], ['dobro', 7], ['cresce', 7], ['lento', 6], ['gelo', 6], ['fogo', 6], ['cego', 4], ['veneno', 3], ['serra', 1]];
const ORB_TYPES = ORB_WEIGHTS.map(w => w[0]);
const SLOW = .42, GROW = 1.2, POISON_LOSS = .2;                      // Lerdeza: mesma lentidão do gelo · Crescer: +20%
/* bolas de fogo: saem da cabeça de quem pegou o poder, se espalham e ficam paradas queimando */
const FB_N = 6, FB_R = 22, FB_TTL = 10, FB_FLY = .5, FB_MIN = 150, FB_MAX = 330, MAX_FB = 150;
const NECK = 4;                                    // gomos logo atrás da cabeça: contam como cabeça com cabeça
const CELL = 64, GN = Math.ceil(WORLD_R * 2 / CELL) + 5;
const FCELL = 128, FGN = Math.ceil(WORLD_R * 2 / FCELL) + 5;

/* ================= utilidades ================= */
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
function angDiff(a, b) { let d = (a - b) % TAU; if (d > Math.PI) d -= TAU; else if (d < -Math.PI) d += TAU; return d; }
function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
function h32() {
  let h = 0x811c9dc5;
  for (let i = 0; i < arguments.length; i++) { h ^= arguments[i] | 0; h = Math.imul(h, 16777619); h ^= h >>> 15; h = Math.imul(h, 0x2c1b3c6d); h ^= h >>> 12; }
  return h >>> 0;
}
const rng = (...a) => mulberry32(h32(...a));
function orbType(r) { let x = r * 100; for (const [k, w] of ORB_WEIGHTS) { x -= w; if (x < 0) return k; } return 'ima'; }
const segCount = mass => Math.min(MAX_SEG, Math.round(10 + Math.pow(Math.max(1, mass), .82) / 2));
const massForSeg = n => n <= 10 ? 14 : Math.pow((n - 10) * 2, 1 / .82);
const radiusOf = m => 9 + Math.sqrt(Math.max(0, m)) * .42;
const foodRadius = v => Math.min(14, 3.4 + Math.sqrt(v) * 1.9);
const B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_';
const enc2 = n => B64[(n >> 6) & 63] + B64[n & 63];
const NAME_JUNK = new RegExp('[' + [[0, 31], [127, 159], [173, 173], [8203, 8207], [8232, 8238], [8288, 8303], [65279, 65279]].map(r => String.fromCharCode(r[0]) + '-' + String.fromCharCode(r[1])).join('') + ']', 'g');
function cleanName(s) { return typeof s === 'string' ? (s.replace(NAME_JUNK, '').trim().slice(0, 14) || 'Visitante') : 'Visitante'; }
function cleanSkin(s) { return typeof s === 'string' && /^([0-9a-f]{6}){1,3}$/i.test(s) ? s.toLowerCase() : 'ff7a2fffb347'; }
function cleanRoom() { return 'geral'; }   // uma toca só para todo mundo
const num = v => typeof v === 'number' && isFinite(v);

/* mesmas fórmulas do cliente: posição e valor de cada bolinha e de cada esfera saem da semente da sala */
function slotFood(seed, i, g) {
  const R = rng(seed, i, g), a = R() * TAU, rr = Math.sqrt(R()) * WORLD_R * .97, v = 1 + R() * 1.6;
  return { x: Math.cos(a) * rr, y: Math.sin(a) * rr, v, r: foodRadius(v), slot: i, id: 0, eaten: false };
}
function orbFor(seed, i, g, time) {
  const R = rng(seed ^ 0x0b5, i, g), a = R() * TAU, rr = Math.sqrt(R()) * WORLD_R * .9;
  return { x: Math.cos(a) * rr, y: Math.sin(a) * rr, type: orbType(R()), born: time + (g ? ORB_DELAY : 0) };
}
function fbPos(f, age) { const k = age >= FB_FLY ? 1 : 1 - Math.pow(1 - age / FB_FLY, 3); f.x = f.x0 + (f.x1 - f.x0) * k; f.y = f.y0 + (f.y1 - f.y0) * k; }
function encodePoly(w) {
  const pts = w.pts, S = 3, q = Math.max(1, Math.ceil(radiusOf(w.mass) * .55 * S / 30));
  const x0 = Math.round(w.x), y0 = Math.round(w.y);
  let cx = x0, cy = y0, s = '';
  for (let i = S - 1; i < pts.length; i += S) {
    const p = pts[i];
    const dx = clamp(Math.round((p.x - cx) / q), -32, 31), dy = clamp(Math.round((p.y - cy) / q), -32, 31);
    s += B64[dx + 32] + B64[dy + 32]; cx += dx * q; cy += dy * q;
  }
  return [x0, y0, q, s];
}
function flagsOf(w) {
  let f = 0; for (const k in w.powers) if (PBIT[k]) f |= PBIT[k];
  if (w.boosting) f |= F_BOOST; if (w.frozen > 0) f |= F_FROZEN; return f;
}

/* ================= sala ================= */
class Room {
  constructor(name) {
    this.name = name;
    this.seed = crypto.randomInt(1, 2 ** 31 - 1);
    this.time = 0; this.tick = 0;
    this.clients = new Set();
    this.worms = new Map(); this.nextWorm = 1; this.list = [];
    this.gens = new Uint16Array(FOOD_N); this.slots = new Array(FOOD_N);
    for (let i = 0; i < FOOD_N; i++) this.slots[i] = slotFood(this.seed, i, 0);
    this.orbGens = new Uint16Array(ORB_N); this.orbs = new Array(ORB_N);
    for (let i = 0; i < ORB_N; i++) this.orbs[i] = orbFor(this.seed, i, 0, 0);
    this.drops = new Map(); this.nextDrop = 1;
    this.fires = new Map(); this.nextFire = 1;
    this.events = [];
    this.grid = Array.from({ length: GN * GN }, () => []); this.gused = [];
    this.fgrid = Array.from({ length: FGN * FGN }, () => []); this.fused = [];
    this.emptySince = Date.now(); this.rosterT = 0;
  }
  gCell(v) { const c = Math.floor((v + WORLD_R) / CELL) + 2; return c >= 0 ? (c < GN ? c : GN - 1) : 0; }
  fCell(v) { const c = Math.floor((v + WORLD_R) / FCELL) + 2; return c >= 0 ? (c < FGN ? c : FGN - 1) : 0; }

  /* ---------- jogadores ---------- */
  join(c) {
    this.clients.add(c); c.room = this; this.emptySince = 0;
    this.sendWelcome(c);
    this.sendRoster();
  }
  leave(c) {
    if (c.worm && c.worm.alive) this.kill(c.worm, null, 'left');
    c.worm = null;
    this.clients.delete(c); c.room = null;
    if (!this.clients.size) this.emptySince = Date.now();
    this.sendRoster();
  }
  sendWelcome(c) {
    let gs = ''; for (let i = 0; i < FOOD_N; i++) gs += enc2(this.gens[i]);
    let og = ''; for (let i = 0; i < ORB_N; i++) og += enc2(this.orbGens[i]);
    const ob = []; for (let i = 0; i < ORB_N; i++) if (this.orbs[i].born > this.time) ob.push([i, +(this.orbs[i].born - this.time).toFixed(2)]);
    const worms = []; for (const w of this.worms.values()) worms.push([w.id, w.name, w.skin, encodePoly(w)]);
    const drops = []; for (const d of this.drops.values()) drops.push([d.id, Math.round(d.x), Math.round(d.y), d.v, d.col]);
    const fires = []; for (const f of this.fires.values()) fires.push([f.id, Math.round(f.x0), Math.round(f.y0), Math.round(f.x1), Math.round(f.y1), f.owner, +f.age.toFixed(2)]);
    c.send({ t: 'w', v: PROTO, room: this.name, seed: this.seed, me: c.id, k: this.tick, tickMs: TICK_MS, gens: gs, og, ob, worms, drops, fires });
  }
  sendBodies(c) {
    const b = []; for (const w of this.worms.values()) b.push([w.id, encodePoly(w)]);
    c.send({ t: 'b', w: b });
  }
  sendRoster() {
    const p = []; for (const c of this.clients) p.push([c.id, c.name, c.skin.slice(0, 6), c.worm && c.worm.alive ? 1 : 0]);
    const msg = JSON.stringify({ t: 'r', p });
    for (const c of this.clients) c.sendText(msg);
  }
  safeSpot() {
    for (let t = 0; t < 40; t++) {
      const a = Math.random() * TAU, r = Math.sqrt(Math.random()) * WORLD_R * .78, x = Math.cos(a) * r, y = Math.sin(a) * r;
      let ok = true;
      for (const o of this.worms.values()) {
        if ((o.x - x) ** 2 + (o.y - y) ** 2 < 520 * 520) { ok = false; break; }
        for (let i = 0; i < o.pts.length; i += 6) { const q = o.pts[i]; if ((q.x - x) ** 2 + (q.y - y) ** 2 < 260 * 260) { ok = false; break; } }
        if (!ok) break;
      }
      if (ok) return { x, y };
    }
    const a = Math.random() * TAU, r = Math.sqrt(Math.random()) * WORLD_R * .78;
    return { x: Math.cos(a) * r, y: Math.sin(a) * r };
  }
  spawn(c) {
    const p = this.safeSpot(), ang = Math.atan2(-p.y, -p.x);
    const cols = c.skin.match(/.{6}/g).map(h => h);
    const w = { id: this.nextWorm++, name: c.name, skin: c.skin, cols, x: p.x, y: p.y, angle: ang, target: ang,
      wantBoost: false, boosting: false, mass: 30, pts: [], powers: {}, frozen: 0, drop: 0, kills: 0, alive: true, client: c };
    const sp = radiusOf(w.mass) * .55, n = segCount(w.mass);
    for (let i = 1; i <= n; i++) w.pts.push({ x: w.x - Math.cos(ang) * sp * i, y: w.y - Math.sin(ang) * sp * i });
    this.worms.set(w.id, w); c.worm = w;
    this.events.push(['n', w.id, w.name, w.skin]);
    c.send({ t: 'you', w: w.id });
    this.sendRoster();
  }

  /* ---------- comida ---------- */
  addDrop(x, y, v, col) {
    if (this.drops.size >= MAX_DROPS) return;
    const r2 = x * x + y * y, lim = (WORLD_R - 20) ** 2;
    if (r2 > lim) { const k = Math.sqrt(lim / r2); x *= k; y *= k; }
    const d = { id: this.nextDrop++, x, y, v: Math.round(v * 100) / 100, r: foodRadius(v), col, age: 0, slot: -1, eaten: false };
    this.drops.set(d.id, d);
    this.events.push(['d', d.id, Math.round(x), Math.round(y), d.v, col]);
  }
  bodyDrops(w, pts, n, val) {
    const len = pts.length, rr = radiusOf(w.mass);
    for (let k = 0; k < n; k++) {
      const p = len ? pts[Math.floor(k * len / n)] : w;
      this.addDrop(p.x + (Math.random() - .5) * rr, p.y + (Math.random() - .5) * rr, val, w.cols[k % w.cols.length]);
    }
  }

  /* ---------- poderes ---------- */
  applyPower(w, type) {
    if (type === 'cresce') { w.mass *= GROW; return; }
    if (type === 'fogo') this.spawnFire(w);
    if (type === 'veneno') w.poison = w.mass * POISON_LOSS / POWER_DUR.veneno;   // perde 20% aos poucos
    if (POWER_DUR[type]) w.powers[type] = POWER_DUR[type];
  }
  spawnFire(w) {
    const base = Math.random() * TAU, lim = WORLD_R - 70;
    for (let k = 0; k < FB_N && this.fires.size < MAX_FB; k++) {
      const a = base + k * TAU / FB_N + (Math.random() - .5) * .5, d = FB_MIN + Math.random() * (FB_MAX - FB_MIN);
      let x1 = w.x + Math.cos(a) * d, y1 = w.y + Math.sin(a) * d;
      const r2 = x1 * x1 + y1 * y1; if (r2 > lim * lim) { const q = lim / Math.sqrt(r2); x1 *= q; y1 *= q; }
      const f = { id: this.nextFire++, x0: Math.round(w.x), y0: Math.round(w.y), x1: Math.round(x1), y1: Math.round(y1), owner: w.id, age: 0, x: w.x, y: w.y };
      this.fires.set(f.id, f);
      this.events.push(['F', f.id, f.x0, f.y0, f.x1, f.y1, f.owner]);
    }
  }

  /* ---------- simulação ---------- */
  step(dt) {
    this.time += dt; this.tick++;
    const list = this.list; list.length = 0;
    for (const w of this.worms.values()) list.push(w);
    for (const w of list) {
      if (!w.powers.gelo) continue;
      for (const o of list) {
        if (o === w) continue;
        const dx = o.x - w.x, dy = o.y - w.y;
        if (dx * dx + dy * dy < GELO_R * GELO_R) o.frozen = Math.max(o.frozen, .35);
      }
    }
    for (const w of list) this.move(w, dt);
    for (const [id, f] of this.fires) { f.age += dt; if (f.age > FB_TTL) this.fires.delete(id); else fbPos(f, f.age); }
    this.buildGrid(list); this.buildFoodGrid();
    for (const w of list) this.eat(w);
    this.pickOrbs(list);
    this.collide(list);
    for (const [id, d] of this.drops) { d.age += dt; if (d.age > DROP_TTL) { this.drops.delete(id); this.events.push(['X', id]); } }
    let changed = false;
    for (const w of list) if (!w.alive) {
      this.worms.delete(w.id);
      if (w.client && w.client.worm === w) { w.client.worm = null; changed = true; }
    }
    if (changed) this.sendRoster();
    if (this.tick % SEND_EVERY === 0) this.broadcast();
  }
  move(w, dt) {
    const P = w.powers;
    for (const k in P) { P[k] -= dt; if (P[k] <= 0) delete P[k]; }
    if (w.frozen > 0) w.frozen -= dt;
    if (P.veneno && w.poison) w.mass = Math.max(14, w.mass - w.poison * dt);
    const fz = w.frozen > 0 || !!P.lento, turbo = !!P.turbo, r = radiusOf(w.mass);
    w.boosting = turbo || (w.wantBoost && w.mass > MIN_BOOST && !fz);
    let spd = turbo ? TURBO_SPEED : w.boosting ? BOOST_SPEED : BASE_SPEED;
    if (fz) spd *= SLOW;
    let tr = clamp(5.4 - (r - 11) * .09, 2, 5.4); if (fz) tr *= .5;
    const d = angDiff(w.target, w.angle), m = tr * dt;
    w.angle = angDiff(w.angle + (Math.abs(d) < m ? d : Math.sign(d) * m), 0);
    w.x += Math.cos(w.angle) * spd * dt; w.y += Math.sin(w.angle) * spd * dt;
    // corpo: cada gomo segue o caminho da cabeça
    const sp = r * .55;
    let p0 = w.pts[0];
    if (!p0) { p0 = { x: w.x - Math.cos(w.angle) * sp, y: w.y - Math.sin(w.angle) * sp }; w.pts.unshift(p0); }
    let dx = w.x - p0.x, dy = w.y - p0.y, dd = Math.hypot(dx, dy), guard = 0;
    while (dd >= sp && guard++ < 80) {
      const np = { x: p0.x + dx / dd * sp, y: p0.y + dy / dd * sp };
      w.pts.unshift(np); p0 = np;
      dx = w.x - p0.x; dy = w.y - p0.y; dd = Math.hypot(dx, dy);
    }
    const n = segCount(w.mass);
    if (w.pts.length > n) w.pts.length = n;
    if (w.boosting && !turbo) {
      const loss = (4 + w.mass * .012) * dt;
      w.mass -= loss; w.drop += loss;
      if (w.drop >= 3) {
        const t = w.pts[w.pts.length - 1] || w;
        this.addDrop(t.x + (Math.random() - .5) * 8, t.y + (Math.random() - .5) * 8, BOOST_DROP_V, w.cols[0]);
        w.drop -= 3;
      }
    }
  }
  buildGrid(list) {
    const g = this.grid;
    for (const i of this.gused) g[i].length = 0; this.gused.length = 0; this.maxR = 12;
    for (let wi = 0; wi < list.length; wi++) {
      const w = list[wi]; if (!w.alive) continue;
      const r = radiusOf(w.mass); if (r > this.maxR) this.maxR = r;
      const base = wi * 1024;
      this.gAdd(w.x, w.y, base);
      for (let i = 0; i < w.pts.length; i++) this.gAdd(w.pts[i].x, w.pts[i].y, base + i + 1);
    }
  }
  gAdd(x, y, code) { const k = this.gCell(y) * GN + this.gCell(x), c = this.grid[k]; if (!c.length) this.gused.push(k); c.push(code); }
  buildFoodGrid() {
    const g = this.fgrid;
    for (const i of this.fused) g[i].length = 0; this.fused.length = 0;
    const add = f => { const k = this.fCell(f.y) * FGN + this.fCell(f.x), c = g[k]; if (!c.length) this.fused.push(k); c.push(f); };
    for (let i = 0; i < FOOD_N; i++) add(this.slots[i]);
    for (const d of this.drops.values()) add(d);
  }
  eat(w) {
    if (!w.alive) return;
    const r = radiusOf(w.mass), reach = r + 10, mag = w.powers.ima ? IMA_R : 0, dbl = w.powers.dobro ? 2 : 1;
    const R = Math.max(reach + 16, mag + 16);
    const x0 = this.fCell(w.x - R), x1 = this.fCell(w.x + R), y0 = this.fCell(w.y - R), y1 = this.fCell(w.y + R);
    for (let cy = y0; cy <= y1; cy++) for (let cx = x0; cx <= x1; cx++) {
      const c = this.fgrid[cy * FGN + cx];
      for (let j = 0; j < c.length; j++) {
        const f = c[j]; if (f.eaten) continue;
        const dx = f.x - w.x, dy = f.y - w.y, er = Math.max(reach + f.r, mag);
        if (dx * dx + dy * dy >= er * er) continue;
        f.eaten = true; w.mass += f.v * dbl;
        if (f.slot >= 0) {
          const i = f.slot, g = this.gens[i] >= 4095 ? 1 : this.gens[i] + 1;
          this.gens[i] = g; this.slots[i] = slotFood(this.seed, i, g);
          this.events.push(['f', i, g, w.id]);
        } else {
          this.drops.delete(f.id);
          this.events.push(['x', f.id, w.id]);
        }
      }
    }
  }
  pickOrbs(list) {
    for (let i = 0; i < ORB_N; i++) {
      const o = this.orbs[i]; if (this.time < o.born) continue;
      for (const w of list) {
        if (!w.alive) continue;
        const dx = o.x - w.x, dy = o.y - w.y, rr = radiusOf(w.mass) + 24;
        if (dx * dx + dy * dy < rr * rr) {
          this.applyPower(w, o.type);
          const g = this.orbGens[i] >= 4095 ? 1 : this.orbGens[i] + 1;
          this.orbGens[i] = g; this.orbs[i] = orbFor(this.seed, i, g, this.time);
          this.events.push(['o', i, g, w.id, o.type]);
          break;
        }
      }
    }
  }
  collide(list) {
    const ev = [];
    for (let wi = 0; wi < list.length; wi++) {
      const w = list[wi]; if (!w.alive) continue;
      const r = radiusOf(w.mass), lim = WORLD_R - r * .4;
      if (w.x * w.x + w.y * w.y > lim * lim) { ev.push({ k: 'die', v: w, by: null, c: 'wall' }); continue; }
      const saw = !!w.powers.serra, hr = r * .82, R = hr + this.maxR;
      let burnt = null;
      for (const f of this.fires.values()) {
        if (f.owner === w.id) continue;                          // quem soltou o fogo não se queima
        const rr = hr + FB_R, dx = f.x - w.x, dy = f.y - w.y;
        if (dx * dx + dy * dy < rr * rr) { burnt = f; break; }
      }
      if (burnt) { ev.push({ k: 'die', v: w, by: this.worms.get(burnt.owner) || null, c: 'fire' }); continue; }
      const x0 = this.gCell(w.x - R), x1 = this.gCell(w.x + R), y0 = this.gCell(w.y - R), y1 = this.gCell(w.y + R);
      let hits = null;                                             // minhoca tocada → menor índice tocado (0 = cabeça)
      for (let cy = y0; cy <= y1; cy++) for (let cx = x0; cx <= x1; cx++) {
        const c = this.grid[cy * GN + cx];
        for (let j = 0; j < c.length; j++) {
          const code = c[j], o = list[Math.floor(code / 1024)];
          if (!o || o === w || !o.alive) continue;
          const i = code % 1024; let sx, sy;
          if (i === 0) { sx = o.x; sy = o.y; } else { const p = o.pts[i - 1]; if (!p) continue; sx = p.x; sy = p.y; }
          const rr = hr + radiusOf(o.mass) * .82, dx = sx - w.x, dy = sy - w.y;
          if (dx * dx + dy * dy < rr * rr) {
            if (!hits) hits = new Map();
            const h = hits.get(o);
            if (!h) hits.set(o, { min: i, deep: i > NECK ? i : 0 });
            else { if (i < h.min) h.min = i; if (i > NECK && (!h.deep || i < h.deep)) h.deep = i; }
          }
        }
      }
      if (!hits) continue;
      if (saw) { for (const [o, h] of hits) ev.push(h.min <= 2 ? { k: 'die', v: o, by: w, c: 'saw' } : { k: 'cut', v: o, by: w, i: h.min }); continue; }
      for (const [o, h] of hits) {
        // de frente: encostou na cabeça, ou no pescoço de quem vinha na direção contrária
        const front = h.min === 0 || (h.min <= 2 && Math.cos(w.angle - o.angle) < 0);
        if (front) {
          // cabeça com cabeça: perde a menor (a Serra sempre vence; empate derruba as duas)
          if (o.powers.serra) { ev.push({ k: 'die', v: w, by: o, c: 'saw' }); break; }
          if (w.mass <= o.mass) { ev.push({ k: 'die', v: w, by: o, c: 'head' }); break; }
          if (h.deep) { ev.push({ k: 'die', v: w, by: o, c: 'body' }); break; }
        } else { ev.push({ k: 'die', v: w, by: o, c: 'body' }); break; }
      }
    }
    for (const e of ev) {
      if (!e.v.alive) continue;
      if (e.k === 'die') this.kill(e.v, e.by, e.c); else this.cut(e.v, e.i, e.by);
    }
  }
  kill(w, by, cause) {
    if (!w.alive) return;
    w.alive = false;
    const m = Math.round(w.mass), n = clamp(Math.floor(segCount(m) / 1.6), 5, 80);
    this.bodyDrops(w, w.pts, n, Math.max(1, m * .7 / n));
    if (by && by.alive !== undefined && by !== w) by.kills++;
    this.events.push(['k', w.id, by ? by.id : 0, cause]);
  }
  cut(o, i, by) {
    const pts = o.pts; if (i - 1 >= pts.length) return;
    const total = pts.length + 1, removed = pts.splice(i - 1);
    let newMass = o.mass * (1 - removed.length / total);
    if (pts.length < MAX_SEG) newMass = Math.min(newMass, massForSeg(pts.length + 1));
    const lost = Math.max(1, Math.round(o.mass - newMass)); o.mass = newMass;
    const n = clamp(Math.round(lost / 8), 2, 50);
    this.bodyDrops(o, removed, n, Math.max(1, lost * .65 / n));
    this.events.push(['c', o.id, i, by.id]);
    if (o.mass < 14) this.kill(o, by, 'saw');
  }
  broadcast() {
    const w = [];
    for (const x of this.worms.values()) w.push([x.id, Math.round(x.x), Math.round(x.y), Math.round(x.angle * 100), Math.round(x.mass), flagsOf(x), x.kills]);
    const msg = JSON.stringify({ t: 's', k: this.tick, w, e: this.events });
    this.events = [];
    for (const c of this.clients) c.sendText(msg);
  }
}

/* ================= salas ================= */
const rooms = new Map();
function getRoom(name) {
  let r = rooms.get(name);
  if (!r) {
    if (rooms.size >= MAX_ROOMS) return null;
    r = new Room(name); rooms.set(name, r);
  }
  return r;
}

/* ================= WebSocket (RFC 6455, sem bibliotecas) ================= */
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const MAX_MSG = 8 * 1024;
let nextClient = 1;
const clients = new Set();
function frame(op, payload) {
  const n = payload.length; let h;
  if (n < 126) h = Buffer.from([0x80 | op, n]);
  else if (n < 65536) { h = Buffer.alloc(4); h[0] = 0x80 | op; h[1] = 126; h.writeUInt16BE(n, 2); }
  else { h = Buffer.alloc(10); h[0] = 0x80 | op; h[1] = 127; h.writeBigUInt64BE(BigInt(n), 2); }
  return Buffer.concat([h, payload]);
}
class Client {
  constructor(sock) {
    this.id = nextClient++; this.sock = sock; this.buf = Buffer.alloc(0); this.frag = null; this.fragOp = 0; this.fragLen = 0;
    this.open = true; this.lastSeen = Date.now(); this.room = null; this.worm = null;
    this.name = 'Visitante'; this.skin = 'ff7a2fffb347';
    this.rateT = Date.now(); this.rateN = 0;
    clients.add(this);
  }
  rawWrite(buf) {
    if (!this.open) return;
    if (this.sock.writableLength > 2 * 1024 * 1024) { this.destroy(); return; }   // conexão lenta demais
    if (SIM_LAG) setTimeout(() => { if (this.open) this.sock.write(buf); }, SIM_LAG / 2);
    else this.sock.write(buf);
  }
  sendText(str) { this.rawWrite(frame(1, Buffer.from(str))); }
  send(obj) { this.sendText(JSON.stringify(obj)); }
  close(code) {
    if (!this.open) return;
    const p = Buffer.alloc(2); p.writeUInt16BE(code || 1000, 0);
    try { this.sock.write(frame(8, p)); this.sock.end(); } catch (e) {}
    this.cleanup();
  }
  destroy() { try { this.sock.destroy(); } catch (e) {} this.cleanup(); }
  cleanup() {
    if (!this.open) return;
    this.open = false; clients.delete(this);
    if (this.room) this.room.leave(this);
  }
  feed(data) {
    this.lastSeen = Date.now();
    this.buf = this.buf.length ? Buffer.concat([this.buf, data]) : data;
    while (this.open && this.buf.length >= 2) {
      const b0 = this.buf[0], b1 = this.buf[1], fin = b0 & 0x80, op = b0 & 0x0f;
      if (!(b1 & 0x80)) { this.close(1002); return; }
      let len = b1 & 0x7f, off = 2;
      if (len === 126) { if (this.buf.length < 4) return; len = this.buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (this.buf.length < 10) return; if (this.buf.readUInt32BE(2) !== 0) { this.close(1009); return; } len = this.buf.readUInt32BE(6); off = 10; }
      if (len > MAX_MSG) { this.close(1009); return; }
      if (this.buf.length < off + 4 + len) return;
      const mask = this.buf.subarray(off, off + 4), data = Buffer.from(this.buf.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < data.length; i++) data[i] ^= mask[i & 3];
      this.buf = this.buf.subarray(off + 4 + len);
      if (op >= 8) {
        if (!fin || len > 125) { this.close(1002); return; }
        if (op === 8) { this.close(1000); return; }
        if (op === 9) { this.rawWrite(frame(10, data)); }
        continue;
      }
      if (op === 0) {
        if (!this.frag) { this.close(1002); return; }
        this.frag.push(data); this.fragLen += data.length;
        if (this.fragLen > MAX_MSG) { this.close(1009); return; }
        if (fin) { const all = Buffer.concat(this.frag); this.frag = null; this.message(this.fragOp, all); }
      } else if (op === 1 || op === 2) {
        if (this.frag) { this.close(1002); return; }
        if (fin) this.message(op, data); else { this.frag = [data]; this.fragOp = op; this.fragLen = data.length; }
      } else { this.close(1002); return; }
    }
  }
  message(op, data) {
    if (op !== 1) return;
    const now = Date.now();
    if (now - this.rateT > 1000) { this.rateT = now; this.rateN = 0; }
    if (++this.rateN > 80) return;                                   // no máximo 80 mensagens por segundo
    if (SIM_LAG) { const s = data.toString(); setTimeout(() => this.handle(s), SIM_LAG / 2); }
    else this.handle(data.toString());
  }
  handle(text) {
    if (!this.open) return;
    let m; try { m = JSON.parse(text); } catch (e) { return; }
    if (!m || typeof m !== 'object') return;
    switch (m.t) {
      case 'hi': {
        if (this.room) return;
        if (m.v !== PROTO) { this.send({ t: 'old' }); return; }
        this.name = cleanName(m.n); this.skin = cleanSkin(m.k);
        const r = getRoom(cleanRoom(m.r));
        if (!r) { this.send({ t: 'full' }); return; }
        if (r.clients.size >= MAX_PLAYERS) { this.send({ t: 'full' }); return; }
        r.join(this);
        break;
      }
      case 'name':
        this.name = cleanName(m.n); this.skin = cleanSkin(m.k);
        if (this.room) this.room.sendRoster();
        break;
      case 'play':
        if (!this.room || (this.worm && this.worm.alive)) return;
        this.name = cleanName(m.n); this.skin = cleanSkin(m.k);
        this.room.spawn(this);
        break;
      case 'in':
        if (this.worm && this.worm.alive && num(m.a) && Math.abs(m.a) < 2000) { this.worm.target = m.a / 100; this.worm.wantBoost = !!m.b; }
        break;
      case 'sync':
        if (this.room) this.room.sendBodies(this);
        break;
      case 'p':
        if (num(m.c)) this.send({ t: 'p', c: m.c });
        break;
      case 'dbg':
        if (DEV && this.worm && this.room && ORB_TYPES.includes(m.p)) this.room.applyPower(this.worm, m.p);
        if (DEV && this.worm && num(m.x) && num(m.y)) { this.worm.x = m.x; this.worm.y = m.y; this.worm.pts.length = 0; }
        if (DEV && this.worm && num(m.a)) { this.worm.angle = this.worm.target = m.a; }
        if (DEV && this.worm && num(m.mass)) this.worm.mass = clamp(m.mass, 14, 5000);
        break;
    }
  }
}

/* ================= HTTP ================= */
let indexHtml = null;
function loadIndex() { try { indexHtml = fs.readFileSync(path.join(PUBLIC, 'index.html')); } catch (e) { indexHtml = Buffer.from('Minhocaos: falta public/index.html'); } }
loadIndex();
const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (url === '/health') { res.writeHead(200, { 'content-type': 'text/plain' }); res.end('ok'); return; }
  if (url === '/stats') {
    const r = []; for (const x of rooms.values()) r.push({ sala: x.name, conectados: x.clients.size, minhocas: x.worms.size, bolinhasSoltas: x.drops.size });
    res.writeHead(200, { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store' }); res.end(JSON.stringify({ regiao: process.env.FLY_REGION || 'local', maquina: process.env.FLY_MACHINE_ID || '-', salas: r }, null, 1)); return;
  }
  if (url === '/' || url === '/index.html') {
    if (DEV) loadIndex();
    res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-cache' }); res.end(indexHtml); return;
  }
  if (url === '/favicon.ico') { res.writeHead(204); res.end(); return; }
  res.writeHead(404, { 'content-type': 'text/plain' }); res.end('não encontrado');
});
server.on('upgrade', (req, sock, head) => {
  const key = req.headers['sec-websocket-key'];
  if (!(req.url || '').startsWith('/ws') || (req.headers.upgrade || '').toLowerCase() !== 'websocket' || !key) { sock.destroy(); return; }
  const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
  sock.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  sock.setNoDelay(true);
  const c = new Client(sock);
  sock.on('data', d => c.feed(d));
  sock.on('close', () => c.cleanup());
  sock.on('error', () => c.destroy());
  if (head && head.length) c.feed(head);
});

/* ================= laço da simulação ================= */
let last = performance.now(), acc = 0;
setInterval(() => {
  const now = performance.now();
  acc += now - last; last = now;
  if (acc > 250) acc = 250;                       // se o servidor travar, não tenta recuperar tudo de uma vez
  while (acc >= TICK_MS) {
    acc -= TICK_MS;
    for (const r of rooms.values()) if (r.clients.size || r.worms.size || r.fires.size) r.step(TICK_MS / 1000);
  }
}, 5);
setInterval(() => {
  const now = Date.now();
  for (const c of clients) {
    if (now - c.lastSeen > 45000) c.destroy();
    else c.rawWrite(frame(9, Buffer.alloc(0)));
  }
  for (const [name, r] of rooms) if (!r.clients.size && r.emptySince && now - r.emptySince > 60000) rooms.delete(name);
}, 15000);

server.listen(PORT, () => console.log(`Minhocaos rodando na porta ${PORT}`));
