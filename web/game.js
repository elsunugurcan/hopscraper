(() => {
'use strict';
// ===================== utilities (pure) =====================
const W = 640, H = 480, TAU = Math.PI * 2;
const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
const lerp = (a, b, t) => a + (b - a) * t;
const rand = (a, b) => (b === undefined ? Math.random() * (a === undefined ? 1 : a) : a + Math.random() * (b - a));
const randi = (a, b) => a + Math.floor(Math.random() * (b - a + 1));
const pick = arr => arr[Math.floor(Math.random() * arr.length)];
const sign = v => (v > 0 ? 1 : v < 0 ? -1 : 0);
const mod = (a, n) => ((a % n) + n) % n;

function hash32(x) {
  x = x | 0;
  x = Math.imul(x ^ (x >>> 16), 0x7feb352d);
  x = Math.imul(x ^ (x >>> 15), 0x846ca68b);
  return (x ^ (x >>> 16)) >>> 0;
}
function mulberry32(a) {
  a = a >>> 0;
  return function () {
    a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const ease = {
  outCubic: t => 1 - Math.pow(1 - t, 3),
  inCubic: t => t * t * t,
  inOutSine: t => -(Math.cos(Math.PI * t) - 1) / 2,
  outBack: t => { const c1 = 1.70158, c3 = c1 + 1; return 1 + c3 * Math.pow(t - 1, 3) + c1 * Math.pow(t - 1, 2); },
  outElastic: t => (t <= 0 ? 0 : t >= 1 ? 1 : Math.pow(2, -10 * t) * Math.sin((t * 10 - 0.75) * (TAU / 3)) + 1)
};

let NUM_SEP = ',';
const fmt = n => String(Math.floor(n)).replace(/\B(?=(\d{3})+(?!\d))/g, NUM_SEP);
const fmtTime = ticks => { const s = Math.floor(ticks / 60); return Math.floor(s / 60) + ':' + String(s % 60).padStart(2, '0'); };
const fmtDate = ts => { const d = new Date(ts); return String(d.getDate()).padStart(2, '0') + '.' + String(d.getMonth() + 1).padStart(2, '0') + '.' + String(d.getFullYear()).slice(2); };

function hexToRgb(h) { const n = parseInt(h.slice(1), 16); return [(n >> 16) & 255, (n >> 8) & 255, n & 255]; }
function mixHex(a, b, t) {
  const A = hexToRgb(a), B = hexToRgb(b);
  return 'rgb(' + Math.round(lerp(A[0], B[0], t)) + ',' + Math.round(lerp(A[1], B[1], t)) + ',' + Math.round(lerp(A[2], B[2], t)) + ')';
}
// ===================== deterministic simulation =====================
// Everything in this section must stay deterministic: replays re-run it from the seed + recorded inputs.
const SIM_VERSION = 1;
const FLOOR_H = 80, TL = 64, TR = 576, TW = TR - TL;
const P_HALF = 12, P_H = 44, FOOT = 9;
const GRAV = 0.45, MAX_FALL = 15;
const ACC = 0.24, AIR_ACC = 0.24, SKID = 0.6, AIR_TURN = 0.4, FRICT = 0.34, AIR_DRAG = 0.04, MAX_VX = 9;
const JUMP_BASE = 9.4, JUMP_K = 1.18, SPIN_VX = 6.8;
const COYOTE = 5, JBUF = 7, WALL_GRACE = 9;
const COMBO_TIME = 180, REV_TICKS = 1800, START_FLOOR = 5, MAX_REVS = 5;
const SPEEDS = [0, 0.55, 1.0, 1.5, 2.0, 2.55, 3.1];
const FOLLOW_Y = 110, CAM0 = -430;
const TIERS = [
  { n: 4, w: 'GOOD!' }, { n: 7, w: 'SWEET!' }, { n: 15, w: 'GREAT!' }, { n: 25, w: 'SUPER!' }, { n: 35, w: 'WOW!' },
  { n: 50, w: 'AMAZING!' }, { n: 70, w: 'EXTREME!' }, { n: 100, w: 'FANTASTIC!' }, { n: 140, w: 'SPLENDID!' }, { n: 200, w: 'NO WAY!' }
];
function comboTier(f) { let t = -1; for (let i = 0; i < TIERS.length; i++) if (f >= TIERS[i].n) t = i; return t; }
const zoneOf = n => Math.min(10, Math.floor(Math.max(0, n) / 100));

const _floorCaches = new Map();
function floorAt(seed, n) {
  let m = _floorCaches.get(seed);
  if (!m) {
    if (_floorCaches.size >= 4) _floorCaches.delete(_floorCaches.keys().next().value);
    m = new Map();
    _floorCaches.set(seed, m);
  }
  let f = m.get(n);
  if (!f) {
    if (m.size > 6000) m.clear();
    f = genFloor(seed, n);
    m.set(n, f);
  }
  return f;
}
function isFullFloor(n) { return n === 0 || (n % 50 === 0 && n <= 1000) || (n % 500 === 0 && n <= 2000) || n === 10000; }
function genFloor(seed, n) {
  if (isFullFloor(n)) return { n, x: TL, w: TW, full: true };
  const r = mulberry32(hash32((seed ^ Math.imul(n + 1, 0x9E3779B1)) | 0));
  let mid;
  if (n < 241) { const hi = 13 - Math.floor(n / 30), lo = Math.max(5, hi - 4); mid = lo + Math.floor(r() * (hi - lo + 1)); }
  else if (n <= 1000) mid = 5;
  else if (n <= 1500) mid = 4;
  else if (n <= 2000) mid = 3;
  else if (n <= 10000) mid = 2;
  else mid = 1;
  const w = (mid + 2) * 16;
  const slots = Math.floor((TW - w) / 8);
  return { n, x: TL + Math.floor(r() * (slots + 1)) * 8, w, full: false };
}

function newGame(seed, rejump) {
  return {
    v: SIM_VERSION, seed: seed >>> 0, rejump: !!rejump, tick: 0, state: 'play', deadTick: -1,
    p: {
      x: 320, y: 0, px: 320, py: 0, vx: 0, vy: 0, ground: true, floor: 0, last: 0, face: 1, dir: 0,
      spin: 0, jumpTick: -1000, landTick: -1000, coyote: 0, buf: 0, jHeld: false,
      wallT: 0, wallV: 0, wallDir: 0, air: 0, idle: 0, edge: 0, skid: false, run: 0
    },
    cam: { y: CAM0, py: CAM0, level: 0, on: false, clock: 0, revs: 0, broken: false },
    best: 0, cpts: 0,
    combo: { on: false, floors: 0, jumps: 0, timer: 0 },
    st: {
      jumps: 0, bounces: 0, combos: 0, bestCombo: 0, unfinished: 0, nml: 0,
      cc: [0, 0, 0, 0, 0], js: [0, 0, 0, 0, 0], jsD: 0, jsN: 0, maxAir: 0, tiers: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    },
    ev: []
  };
}
const gameScore = g => g.best * 10 + g.cpts;
function emit(g, type, data) { data.type = type; g.ev.push(data); }
function cloneGame(g) { const e = g.ev; g.ev = []; const c = JSON.parse(JSON.stringify(g)); g.ev = e; return c; }

function stepGame(g, bits) {
  const p = g.p, c = g.cam;
  g.tick++;
  p.px = p.x; p.py = p.y; c.py = c.y;

  if (g.state === 'dead') {
    p.vy = Math.min(p.vy + GRAV, MAX_FALL);
    p.y += p.vy;
    p.x += p.vx;
    if (p.x < TL + P_HALF) { p.x = TL + P_HALF; p.vx = -p.vx * 0.5; }
    else if (p.x > TR - P_HALF) { p.x = TR - P_HALF; p.vx = -p.vx * 0.5; }
    return;
  }

  const L = bits & 1, R = (bits >> 1) & 1, J = (bits >> 2) & 1;
  const dir = R - L;
  p.dir = dir;
  if (dir !== 0) { p.face = dir; p.idle = 0; } else p.idle++;
  if (J) p.idle = 0;
  const jPress = J && !p.jHeld;
  p.jHeld = !!J;
  if (jPress) p.buf = JBUF; else if (p.buf > 0) p.buf--;

  // Hitting a wall on the ground and reversing right away keeps the speed.
  if (p.wallT > 0) {
    p.wallT--;
    if (p.ground && dir === -p.wallDir) {
      p.vx = dir * p.wallV;
      p.wallT = 0;
      g.st.bounces++;
      emit(g, 'wall', { side: p.wallDir, speed: p.wallV, air: false });
    }
  }

  // horizontal movement
  const onG = p.ground;
  if (dir !== 0) {
    if (p.vx * dir < 0) p.vx += dir * (onG ? SKID : AIR_TURN);
    else p.vx += dir * (onG ? ACC : AIR_ACC);
  } else {
    const f = onG ? FRICT : AIR_DRAG;
    if (p.vx > f) p.vx -= f; else if (p.vx < -f) p.vx += f; else p.vx = 0;
  }
  if (p.vx > MAX_VX) p.vx = MAX_VX; else if (p.vx < -MAX_VX) p.vx = -MAX_VX;
  p.skid = onG && dir !== 0 && p.vx * dir < 0 && Math.abs(p.vx) > 2;
  p.x += p.vx;
  if (onG) p.run += Math.abs(p.vx);

  // walls
  const minX = TL + P_HALF, maxX = TR - P_HALF;
  if (p.x < minX || p.x > maxX) {
    const side = p.x < minX ? -1 : 1;
    const ex = side < 0 ? minX : maxX;
    const sp = Math.abs(p.vx);
    if (!onG) {
      p.x = ex - (p.x - ex);
      p.vx = -p.vx;
      if (sp > 0.5) {
        p.air++; g.st.bounces++;
        if (p.air > g.st.maxAir) g.st.maxAir = p.air;
        emit(g, 'wall', { side, speed: sp, air: true });
      }
    } else if (dir === side) {
      p.x = ex;
      if (sp > 2) { p.wallT = WALL_GRACE; p.wallV = sp; p.wallDir = side; emit(g, 'bump', { side, speed: sp }); }
      p.vx = 0;
    } else {
      p.x = ex - (p.x - ex);
      p.vx = -p.vx * 0.6;
      if (sp > 2) emit(g, 'wall', { side, speed: sp * 0.6, air: false });
    }
  }

  // jumping
  if (p.ground) p.coyote = COYOTE; else if (p.coyote > 0) p.coyote--;
  if ((p.buf > 0 || (g.rejump && J)) && (p.ground || p.coyote > 0)) {
    const sp = Math.abs(p.vx);
    p.vy = -(JUMP_BASE + JUMP_K * sp);
    p.ground = false; p.coyote = 0; p.buf = 0; p.air = 0; p.edge = 0; p.skid = false;
    p.spin = sp >= SPIN_VX ? (p.vx > 0 ? 1 : -1) : 0;
    p.jumpTick = g.tick;
    g.st.jumps++;
    emit(g, 'jump', { power: sp / MAX_VX, spin: p.spin !== 0 });
  }

  // vertical movement + one-way floors
  if (!p.ground) {
    p.vy += GRAV;
    if (p.vy > MAX_FALL) p.vy = MAX_FALL;
    const y0 = p.y;
    p.y += p.vy;
    if (p.vy > 0) {
      const hi = Math.floor(-y0 / FLOOR_H), lo = Math.ceil(-p.y / FLOOR_H);
      for (let n = hi; n >= lo && n >= 0; n--) {
        const f = floorAt(g.seed, n);
        if (p.x >= f.x - FOOT && p.x <= f.x + f.w + FOOT) { land(g, n); break; }
      }
    }
  } else {
    const f = floorAt(g.seed, p.floor);
    if (p.x < f.x - FOOT || p.x > f.x + f.w + FOOT) { p.ground = false; p.vy = 0.5; p.edge = 0; }
    else p.edge = p.x < f.x ? -1 : p.x > f.x + f.w ? 1 : 0;
  }

  // combo timer
  if (g.combo.on && --g.combo.timer <= 0) endCombo(g);

  // tower scroll + clock
  if (c.on) {
    c.y -= SPEEDS[c.level];
    if (!c.broken && ++c.clock >= REV_TICKS) {
      c.clock = 0;
      c.revs++;
      g.st.cc[c.revs - 1] = g.best;
      if (c.level < SPEEDS.length - 1) c.level++;
      if (c.revs >= MAX_REVS) c.broken = true;
      emit(g, 'hurry', { level: c.level, broken: c.broken });
    }
  }
  const head = p.y - P_H;
  if (head - c.y < FOLLOW_Y) c.y += (head - FOLLOW_Y - c.y) * 0.2;

  // fell off the bottom
  if (p.y - c.y > H + 4) {
    g.state = 'dead';
    g.deadTick = g.tick;
    if (g.combo.on) { g.st.unfinished = g.combo.floors; g.combo.on = false; }
    for (let i = c.revs; i < MAX_REVS; i++) g.st.cc[i] = g.best;
    p.ground = false;
    if (p.vy < 0) p.vy = 0;
    emit(g, 'dead', {});
  }
}

function land(g, n) {
  const p = g.p, st = g.st, cb = g.combo;
  const impact = p.vy;
  p.y = -n * FLOOR_H; p.vy = 0; p.ground = true; p.spin = 0; p.landTick = g.tick; p.floor = n; p.air = 0;
  const d = n - p.last;
  p.last = n;
  if (d >= 2) {
    if (!cb.on) { cb.on = true; cb.floors = 0; cb.jumps = 0; }
    cb.floors += d; cb.jumps++; cb.timer = COMBO_TIME;
    emit(g, 'cstep', { floors: cb.floors, jumps: cb.jumps, d });
  } else if (d !== 0 && cb.on) endCombo(g);
  if (d >= 1 && d <= 5) {
    if (st.jsD === d) st.jsN++; else { st.jsD = d; st.jsN = 1; }
    if (st.jsN > st.js[d - 1]) st.js[d - 1] = st.jsN;
  } else { st.jsD = 0; st.jsN = 0; }
  if (n > g.best) {
    const oz = zoneOf(g.best);
    g.best = n;
    if (st.combos === 0) st.nml = n;
    emit(g, 'floor', { n });
    if (zoneOf(n) !== oz) emit(g, 'zone', { z: zoneOf(n) });
    if (!g.cam.on && n >= START_FLOOR) { g.cam.on = true; g.cam.level = 1; emit(g, 'start', {}); }
  }
  emit(g, 'land', { n, d, impact });
}

function endCombo(g) {
  const cb = g.combo;
  cb.on = false;
  if (cb.jumps >= 2 && cb.floors >= 4) {
    const pts = cb.floors * cb.floors;
    g.cpts += pts;
    g.st.combos++;
    if (cb.floors > g.st.bestCombo) g.st.bestCombo = cb.floors;
    const tier = comboTier(cb.floors);
    if (tier >= 0) g.st.tiers[tier]++;
    emit(g, 'combo', { floors: cb.floors, pts, tier });
  } else emit(g, 'cfail', { floors: cb.floors });
  cb.floors = 0; cb.jumps = 0; cb.timer = 0;
}

// ===================== bot (attract mode + tests) =====================
const Bot = {
  // Simulate an airborne arc with a steering policy; returns the floor it would land on.
  predict(seed, x, y, vx, vy, dir, fromFloor, T) {
    for (let t = 0; t < T; t++) {
      if (dir !== 0) { if (vx * dir < 0) vx += dir * AIR_TURN; else vx += dir * AIR_ACC; }
      else { if (vx > AIR_DRAG) vx -= AIR_DRAG; else if (vx < -AIR_DRAG) vx += AIR_DRAG; else vx = 0; }
      if (vx > MAX_VX) vx = MAX_VX; else if (vx < -MAX_VX) vx = -MAX_VX;
      x += vx;
      if (x < TL + P_HALF) { x = 2 * (TL + P_HALF) - x; vx = -vx; if (dir < 0) dir = 1; }
      else if (x > TR - P_HALF) { x = 2 * (TR - P_HALF) - x; vx = -vx; if (dir > 0) dir = -1; }
      vy += GRAV; if (vy > MAX_FALL) vy = MAX_FALL;
      const y0 = y; y += vy;
      if (vy > 0) {
        const hi = Math.floor(-y0 / FLOOR_H), lo = Math.ceil(-y / FLOOR_H);
        for (let n = hi; n >= lo && n >= 0; n--) {
          const f = floorAt(seed, n);
          if (x >= f.x - FOOT + 3 && x <= f.x + f.w + FOOT - 3) return { n, x, t };
        }
        if (-y / FLOOR_H < fromFloor - 1.2) return null;
      }
    }
    return null;
  },
  think(g, m) {
    const p = g.p;
    if (g.state !== 'play') return 0;
    if (m.dir === undefined) { m.dir = p.x < 320 ? 1 : -1; m.lastJ = 0; m.skill = m.skill === undefined ? 1 : m.skill; m.wait = 0; }
    let dir = m.dir, jump = 0;
    if (m.wait > 0) { m.wait--; m.lastJ = 0; return 0; }
    if (p.ground) {
      const f = floorAt(g.seed, p.floor);
      if (p.wallT > 0) m.dir = dir = -p.wallDir;
      const sp = Math.abs(p.vx);
      let vx = p.vx + dir * (p.vx * dir < 0 ? SKID : ACC);
      vx = clamp(vx, -MAX_VX, MAX_VX);
      const vy = -(JUMP_BASE + JUMP_K * Math.abs(vx));
      const r = Bot.predict(g.seed, p.x + vx, p.y, vx, vy, dir, p.floor, 150);
      const gain = r ? r.n - p.floor : -9;
      const screenY = p.y - g.cam.y;
      const danger = screenY > H - 150;
      const hurry = g.combo.on && g.combo.timer < 60;
      const ahead = dir > 0 ? f.x + f.w - p.x : p.x - f.x;
      let want = sp > 7.6 ? 3 : sp > 5.2 ? 2 : 1;
      if (!danger && m.skill > 0.5 && (f.full || f.w >= 160) && sp < 5 && ahead > 60) want = 2;
      if (danger) want = 1;
      if (g.combo.on) want = 2;
      if (m.cautious) want = 1;
      if (!m.lastJ && (gain >= want || (gain >= 1 && (danger || hurry || ahead < 8 + sp * 1.4)))) jump = 4;
      else if (!f.full && ahead < 6 + sp * 2.4 && gain < 1) m.dir = dir = -dir;
      if (m.skill < 1 && Math.random() < 0.004) m.wait = 10 + Math.floor(Math.random() * 25);
    } else {
      if (p.vx * m.dir < -1) m.dir = sign(p.vx) || m.dir;
      let best = -1e9, bd = m.dir;
      const opts = [m.dir, 0, -m.dir];
      for (let i = 0; i < 3; i++) {
        const d = opts[i];
        const r = Bot.predict(g.seed, p.x, p.y, p.vx, p.vy, d, p.last, 160);
        let s = -1e6;
        if (r) {
          const f = floorAt(g.seed, r.n);
          s = r.n * 100 - Math.abs(r.x - (f.x + f.w / 2)) * 0.05 - (i ? 3 : 0);
          if (g.combo.on && r.n - p.last === 1) s -= 150;
        }
        if (s > best) { best = s; bd = d; }
      }
      dir = bd;
      if (dir !== 0) m.dir = dir;
    }
    m.lastJ = jump;
    return (dir < 0 ? 1 : 0) | (dir > 0 ? 2 : 0) | jump;
  }
};

// ===================== replay codec =====================
const RLE_A = 'ABCDEFGH';
function encodeInputs(a) {
  let s = '', prev = -1, run = 0;
  for (let i = 0; i < a.length; i++) {
    const b = a[i] & 7;
    if (b === prev) run++;
    else { if (run) s += RLE_A[prev] + run.toString(36); prev = b; run = 1; }
  }
  if (run) s += RLE_A[prev] + run.toString(36);
  return s;
}
function decodeInputs(s) {
  let total = 0;
  const runs = [];
  const re = /([A-H])([0-9a-z]+)/g;
  let m;
  while ((m = re.exec(s))) { const b = m[1].charCodeAt(0) - 65, n = parseInt(m[2], 36); runs.push(b, n); total += n; }
  const out = new Uint8Array(total);
  let k = 0;
  for (let i = 0; i < runs.length; i += 2) { out.fill(runs[i], k, k + runs[i + 1]); k += runs[i + 1]; }
  return out;
}
function b64enc(str) {
  const bytes = new TextEncoder().encode(str);
  let bin = '';
  for (let i = 0; i < bytes.length; i += 0x8000) bin += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));
  return btoa(bin);
}
function b64dec(b) {
  const bin = atob(b);
  const bytes = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
  return new TextDecoder().decode(bytes);
}
function validReplay(r) {
  return !!r && typeof r === 'object' && r.v === SIM_VERSION && Number.isFinite(r.seed) && typeof r.input === 'string' &&
    r.input.length < 2e6 && /^([A-H][0-9a-z]+)*$/.test(r.input) && typeof r.name === 'string' && Number.isFinite(r.score);
}
function replayToCode(rep) { return 'HOPR1-' + b64enc(JSON.stringify(rep)); }
function replayFromCode(code) {
  code = String(code || '').trim().replace(/\s+/g, '');
  if (code.indexOf('HOPR1-') !== 0) throw new Error('format');
  const rep = JSON.parse(b64dec(code.slice(6)));
  if (!validReplay(rep)) throw new Error('invalid');
  rep.name = String(rep.name).slice(0, 12);
  rep.char = clamp(rep.char | 0, 0, 3);
  return rep;
}
// ===================== storage, language, settings, saved data =====================
const Store = (() => {
  const P = 'hopscraper.v1.';
  const mem = Object.create(null);
  let ls = null;
  try { ls = window.localStorage; const k = P + 't'; ls.setItem(k, '1'); ls.removeItem(k); } catch (e) { ls = null; }
  return {
    get(key, def) {
      try {
        if (key in mem) return JSON.parse(mem[key]);
        if (ls) { const v = ls.getItem(P + key); if (v != null) return JSON.parse(v); }
      } catch (e) { /* unreadable: fall back to default */ }
      return def;
    },
    set(key, val) {
      const s = JSON.stringify(val);
      try { if (ls) { ls.setItem(P + key, s); delete mem[key]; return true; } } catch (e) { /* quota or blocked */ }
      mem[key] = s;
      return false;
    },
    clear() {
      try {
        if (ls) {
          const ks = [];
          for (let i = 0; i < ls.length; i++) { const k = ls.key(i); if (k && k.indexOf(P) === 0) ks.push(k); }
          ks.forEach(k => ls.removeItem(k));
        }
      } catch (e) { /* ignore */ }
      for (const k in mem) delete mem[k];
    }
  };
})();

const STR = {
  play: ['PLAY GAME', 'OYNA'],
  character: ['CHARACTER', 'KARAKTER'],
  highscores: ['HIGHSCORES', 'SKOR TABLOSU'],
  replays: ['REPLAYS', 'TEKRARLAR'],
  trophies: ['TROPHIES', 'KUPALAR'],
  options: ['OPTIONS', 'AYARLAR'],
  help: ['HOW TO PLAY', 'NASIL OYNANIR'],
  back: ['BACK', 'GERİ'],
  tagline: ['How high can you climb?', 'Ne kadar yükseğe tırmanabilirsin?'],
  hintKeys: ['ARROWS OR A / D TO RUN · SPACE TO JUMP', 'YÖN TUŞLARI YA DA A / D İLE KOŞ · BOŞLUK İLE ZIPLA'],
  hintTouch: ['TAP A MENU ITEM TO START', 'BAŞLAMAK İÇİN BİR SEÇENEĞE DOKUN'],
  best: ['BEST', 'EN İYİ'],
  rank: ['RANK', 'RÜTBE'],
  score: ['SCORE', 'SKOR'],
  floor: ['FLOOR', 'KAT'],
  combo: ['COMBO', 'KOMBO'],
  bestCombo: ['BEST COMBO', 'EN İYİ KOMBO'],
  time: ['TIME', 'SÜRE'],
  jumps: ['JUMPS', 'ZIPLAMA'],
  personal: ['PERSONAL', 'KİŞİSEL'],
  chooseChar: ['CHOOSE YOUR CLIMBER', 'TIRMANICINI SEÇ'],
  selected: ['SELECTED', 'SEÇİLDİ'],
  language: ['LANGUAGE', 'DİL'],
  langName: ['ENGLISH', 'TÜRKÇE'],
  music: ['MUSIC', 'MÜZİK'],
  sfx: ['SOUND FX', 'SES EFEKTLERİ'],
  voice: ['VOICE CALLOUTS', 'SESLİ ANONS'],
  rejump: ['HOLD TO REJUMP', 'BASILI TUTUNCA ZIPLA'],
  floorStyle: ['FLOOR STYLE', 'KAT STİLİ'],
  classic: ['CLASSIC', 'KLASİK'],
  shake: ['SCREEN SHAKE', 'EKRAN SARSINTISI'],
  touchCtl: ['TOUCH BUTTONS', 'DOKUNMATİK TUŞLAR'],
  auto: ['AUTO', 'OTOMATİK'],
  on: ['ON', 'AÇIK'],
  off: ['OFF', 'KAPALI'],
  fullscreen: ['FULLSCREEN', 'TAM EKRAN'],
  playerName: ['PLAYER NAME', 'OYUNCU ADI'],
  controls: ['CONTROLS', 'KONTROLLER'],
  resetData: ['RESET ALL DATA', 'TÜM VERİYİ SİL'],
  resetAsk: ['Delete all scores, replays, records and trophies?', 'Tüm skorlar, tekrarlar, rekorlar ve kupalar silinsin mi?'],
  yes: ['YES', 'EVET'],
  no: ['NO', 'HAYIR'],
  left: ['RUN LEFT', 'SOLA KOŞ'],
  right: ['RUN RIGHT', 'SAĞA KOŞ'],
  jump: ['JUMP', 'ZIPLA'],
  pause: ['PAUSE', 'DURAKLAT'],
  pressKey: ['PRESS A KEY  ·  ESC CANCELS', 'BİR TUŞA BAS  ·  ESC İPTAL'],
  resetKeys: ['RESET TO DEFAULT', 'VARSAYILANA DÖN'],
  padInfo: ['Gamepad: stick or D-pad to run, A to jump, START to pause.', 'Oyun kolu: çubuk ya da yön tuşlarıyla koş, A ile zıpla, START ile duraklat.'],
  touchInfo: ['Touch screens get on-screen buttons automatically.', 'Dokunmatik ekranlarda tuşlar otomatik çıkar.'],
  paused: ['PAUSED', 'DURAKLATILDI'],
  resume: ['RESUME', 'DEVAM ET'],
  restart: ['RESTART', 'YENİDEN BAŞLA'],
  quit: ['QUIT TO MENU', 'MENÜYE DÖN'],
  playAgain: ['PLAY AGAIN', 'TEKRAR OYNA'],
  watchReplay: ['WATCH REPLAY', 'TEKRARI İZLE'],
  saveReplay: ['SAVE REPLAY', 'TEKRARI KAYDET'],
  saved: ['SAVED', 'KAYDEDİLDİ'],
  menu: ['MENU', 'MENÜ'],
  newHigh: ['NEW HIGHSCORE!', 'YENİ REKOR!'],
  enterName: ['TYPE YOUR NAME, THEN PRESS ENTER', 'ADINI YAZ, SONRA ENTER’A BAS'],
  ok: ['OK', 'TAMAM'],
  newTrophies: ['NEW TROPHIES', 'YENİ KUPALAR'],
  lastGame: ['LAST GAME', 'SON OYUN'],
  watch: ['WATCH', 'İZLE'],
  copyCode: ['COPY CODE', 'KODU KOPYALA'],
  copied: ['CODE COPIED', 'KOD KOPYALANDI'],
  del: ['DELETE', 'SİL'],
  importCode: ['IMPORT CODE', 'KOD YÜKLE'],
  noReplays: ['No replays yet. Finish a game and it shows up here.', 'Henüz tekrar yok. Bir oyunu bitir, burada görünsün.'],
  noScores: ['No scores yet. Go set one!', 'Henüz skor yok. Hadi bir tane yap!'],
  importTitle: ['Import a replay', 'Tekrar yükle'],
  importText: ['Paste a replay code that a friend sent you.', 'Bir arkadaşının gönderdiği tekrar kodunu yapıştır.'],
  exportTitle: ['Replay code', 'Tekrar kodu'],
  exportText: ['Copy this code and send it to a friend. They can load it under Replays → Import code.', 'Bu kodu kopyalayıp bir arkadaşına gönder. Tekrarlar → Kod yükle ile açabilir.'],
  cancel: ['CANCEL', 'İPTAL'],
  load: ['LOAD', 'YÜKLE'],
  close: ['CLOSE', 'KAPAT'],
  badCode: ['That is not a valid replay code. Check that you copied all of it.', 'Bu geçerli bir tekrar kodu değil. Tamamını kopyaladığından emin ol.'],
  imported: ['REPLAY IMPORTED', 'TEKRAR YÜKLENDİ'],
  replay: ['REPLAY', 'TEKRAR'],
  endReplay: ['END OF REPLAY', 'TEKRAR BİTTİ'],
  verified: ['Result matches the saved score', 'Sonuç kayıtlı skorla aynı'],
  desync: ['Result differs from the saved score', 'Sonuç kayıtlı skordan farklı'],
  again: ['WATCH AGAIN', 'TEKRAR İZLE'],
  replayHelp: ['SPACE PAUSE  ·  ← → SEEK  ·  ↑ ↓ SPEED  ·  ESC EXIT', 'BOŞLUK DURDUR  ·  ← → SAR  ·  ↑ ↓ HIZ  ·  ESC ÇIK'],
  unlocked: ['TROPHY UNLOCKED', 'KUPA KAZANILDI'],
  nextRank: ['NEXT RANK', 'SONRAKİ RÜTBE'],
  unranked: ['UNRANKED', 'RÜTBESİZ'],
  games: ['GAMES', 'OYUN'],
  totalFloors: ['TOTAL FLOORS', 'TOPLAM KAT'],
  played: ['PLAY TIME', 'OYUN SÜRESİ'],
  unfinished: ['UNFINISHED COMBO', 'BİTMEYEN KOMBO'],
  nml: ['FLOOR WITHOUT COMBOS', 'KOMBOSUZ KAT'],
  ccTitle: ['FLOOR BY CLOCK TURN', 'SAAT TURUNA GÖRE KAT'],
  jsTitle: ['SAME-SIZE JUMP STREAKS', 'AYNI BOY ZIPLAMA SERİSİ'],
  floorsWord: ['FLOORS', 'KAT'],
  maxLevel: ['MAX SPEED', 'EN YÜKSEK HIZ'],
  newRecord: ['NEW RECORD', 'YENİ REKOR'],
  loading: ['LOADING', 'YÜKLENİYOR'],
  bestReplay: ['BEST REPLAY', 'EN İYİ TEKRAR'],
  replayOf: ['REPLAY', 'TEKRAR'],
  speedWord: ['SPEED', 'HIZ'],
  rankReq: ['Needs', 'Gerekli'],
  achCount: ['UNLOCKED', 'AÇILDI'],
  req_floor: ['floor', 'kat'],
  req_combo: ['combo', 'kombo'],
  req_cc1: ['floor in 1st clock turn', 'ilk saat turunda kat'],
  req_nml: ['floor without combos', 'kombosuz kat'],
  locked: ['LOCKED', 'KİLİTLİ'],
  hofScore: ['TOP SCORES', 'EN YÜKSEK SKORLAR'],
  hofFloor: ['HIGHEST FLOORS', 'EN YÜKSEK KATLAR'],
  hofCombo: ['LONGEST COMBOS', 'EN UZUN KOMBOLAR'],
  clickWatch: ['Rows with ▶ have a replay: select one to watch it.', '▶ olan satırların tekrarı var: izlemek için seç.'],
  saveFail: ['Your browser is not keeping saved data, so scores last until you close this page.', 'Tarayıcın veri saklamıyor; skorlar bu sayfayı kapatana kadar durur.'],
  name: ['NAME', 'AD'],
  date: ['DATE', 'TARİH'],
  rankUp: ['RANK UP!', 'RÜTBE ATLADIN!'],
  deleted: ['REPLAY DELETED', 'TEKRAR SİLİNDİ'],
  replaySaved: ['REPLAY SAVED', 'TEKRAR KAYDEDİLDİ'],
  tapSkip: ['PRESS ENTER TO CONTINUE', 'DEVAM İÇİN ENTER'],
  imported2: ['Imported', 'Yüklendi'],
  by: ['by', ''],
  noFs: ['Fullscreen is not available here.', 'Tam ekran burada kullanılamıyor.'],
  langHint: ['LEFT / RIGHT TO CHANGE', 'DEĞİŞTİRMEK İÇİN SOL / SAĞ']
};
const ZONE_NAMES = [
  ['STONE', 'TAŞ'], ['ICE', 'BUZ'], ['WOOD', 'AHŞAP'], ['STEEL', 'ÇELİK'], ['CANDY', 'ŞEKER'], ['BONE', 'KEMİK'],
  ['JUNGLE', 'ORMAN'], ['PIPES', 'BORULAR'], ['CLOUDS', 'BULUTLAR'], ['RAINBOW', 'GÖKKUŞAĞI'], ['STARS', 'YILDIZLAR']
];
const HELP = [
  [
    ['RUN', 'Arrow keys or A / D. The faster you run, the higher you jump.'],
    ['JUMP', 'Space, Up or W. At top speed one jump clears up to five floors.'],
    ['WALLS', 'Hit a wall in the air and you bounce back at full speed. On the ground, press the other way right as you touch it.'],
    ['CLOCK', 'The tower starts sinking once you reach floor 5. Every 30 seconds the clock rings and everything speeds up. After five rings it breaks.'],
    ['COMBO', 'Jump two or more floors at a time, again and again, each within 3 seconds. A combo needs 2+ such jumps and 4+ floors. It pays floors × floors.'],
    ['BREAKS', 'A one-floor jump, landing lower, running out of time or falling off the screen ends the combo. Unfinished combos score nothing.'],
    ['SCORE', 'Score = highest floor × 10 + all combo points. Every 100 floors the tower changes.']
  ],
  [
    ['KOŞ', 'Yön tuşları ya da A / D. Ne kadar hızlı koşarsan o kadar yükseğe zıplarsın.'],
    ['ZIPLA', 'Boşluk, Yukarı ya da W. Tam hızda tek zıplamayla beş kata kadar çıkarsın.'],
    ['DUVAR', 'Havada duvara çarpınca tam hızla geri sekersin. Yerdeyken, duvara değdiğin an ters yöne bas.'],
    ['SAAT', 'Kat 5’e varınca kule aşağı kaymaya başlar. Her 30 saniyede saat çalar ve her şey hızlanır. Beş çalıştan sonra saat bozulur.'],
    ['KOMBO', 'Arka arkaya ikişer ya da daha fazla kat zıpla, her biri 3 saniye içinde. Kombo için 2+ zıplama ve 4+ kat gerekir. Puanı kat × kat.'],
    ['BİTİŞ', 'Tek katlık zıplama, aşağı inmek, sürenin dolması ya da ekrandan düşmek komboyu bitirir. Bitmeyen kombo puan getirmez.'],
    ['SKOR', 'Skor = en yüksek kat × 10 + tüm kombo puanları. Her 100 katta kule değişir.']
  ]
];

const REDUCED = (() => { try { return window.matchMedia('(prefers-reduced-motion: reduce)').matches; } catch (e) { return false; } })();
const DEF_KEYS = { left: ['ArrowLeft', 'KeyA'], right: ['ArrowRight', 'KeyD'], jump: ['Space', 'ArrowUp', 'KeyW'], pause: ['KeyP', 'Escape'] };
const settings = (() => {
  const d = {
    lang: /^tr/i.test(navigator.language || '') ? 1 : 0, music: 6, sfx: 8, voice: true, rejump: true, style: -1,
    shake: !REDUCED, touch: 0, char: 0, name: '', keys: JSON.parse(JSON.stringify(DEF_KEYS))
  };
  const s = Store.get('settings', null);
  if (s && typeof s === 'object') {
    for (const k in d) if (k !== 'keys' && typeof s[k] === typeof d[k]) d[k] = s[k];
    if (s.keys && typeof s.keys === 'object') {
      for (const a in DEF_KEYS) {
        const v = s.keys[a];
        if (Array.isArray(v) && v.length && v.every(x => typeof x === 'string')) d.keys[a] = v.slice(0, 4);
      }
    }
  }
  d.lang = d.lang === 1 ? 1 : 0;
  d.music = clamp(Math.round(d.music), 0, 10);
  d.sfx = clamp(Math.round(d.sfx), 0, 10);
  d.style = clamp(Math.round(d.style), -1, 10);
  d.touch = clamp(Math.round(d.touch), 0, 2);
  d.char = clamp(Math.round(d.char), 0, 3);
  d.name = String(d.name).slice(0, 12);
  return d;
})();
NUM_SEP = settings.lang === 1 ? '.' : ',';
const saveSettings = () => { NUM_SEP = settings.lang === 1 ? '.' : ','; return Store.set('settings', settings); };
const T = k => { const v = STR[k]; return v ? (v[settings.lang] || v[0]) : k; };
const TT = pair => pair[settings.lang] || pair[0];

const defRecords = () => ({ score: 0, floor: 0, combo: 0, unfinished: 0, nml: 0, cc: [0, 0, 0, 0, 0], js: [0, 0, 0, 0, 0], level: 0 });
const defStats = () => ({ games: 0, floors: 0, jumps: 0, ticks: 0, combos: 0, bounces: 0, chars: [], watched: 0 });
function loadArr(v, len) { const a = new Array(len).fill(0); if (Array.isArray(v)) for (let i = 0; i < len; i++) a[i] = Number(v[i]) || 0; return a; }
function sanitizeEntry(e) {
  if (!e || typeof e !== 'object') return null;
  return {
    name: String(e.name || 'PLAYER').slice(0, 12), score: Number(e.score) || 0, floor: Number(e.floor) || 0, combo: Number(e.combo) || 0,
    date: Number(e.date) || 0, char: clamp(e.char | 0, 0, 3), rid: typeof e.rid === 'string' ? e.rid : null, time: Number(e.time) || 0
  };
}
const Data = (() => {
  const sc = Store.get('scores', null) || {};
  const scores = {};
  for (const t of ['score', 'floor', 'combo']) scores[t] = Array.isArray(sc[t]) ? sc[t].map(sanitizeEntry).filter(Boolean).slice(0, 10) : [];
  const r = Store.get('records', null) || {};
  const records = defRecords();
  for (const k of ['score', 'floor', 'combo', 'unfinished', 'nml', 'level']) records[k] = Number(r[k]) || 0;
  records.cc = loadArr(r.cc, 5); records.js = loadArr(r.js, 5);
  const s = Store.get('stats', null) || {};
  const stats = defStats();
  for (const k of ['games', 'floors', 'jumps', 'ticks', 'combos', 'bounces', 'watched']) stats[k] = Number(s[k]) || 0;
  stats.chars = Array.isArray(s.chars) ? s.chars.filter(x => x >= 0 && x <= 3) : [];
  const ach = Store.get('ach', null);
  const reps = Store.get('replays', null);
  const replays = {};
  if (reps && typeof reps === 'object') for (const k in reps) if (validReplay(reps[k])) replays[k] = reps[k];
  const saved = (Store.get('saved', []) || []).filter(id => typeof id === 'string' && replays[id]);
  const lastRaw = Store.get('last', null);
  return {
    scores, records, stats, replays, saved,
    ach: ach && typeof ach === 'object' ? ach : {},
    last: validReplay(lastRaw) ? lastRaw : null,
    persist: Store.set('probe', 1),
    save(...keys) {
      for (const k of keys) {
        if (k === 'scores') Store.set('scores', this.scores);
        else if (k === 'records') Store.set('records', this.records);
        else if (k === 'stats') Store.set('stats', this.stats);
        else if (k === 'ach') Store.set('ach', this.ach);
        else if (k === 'replays') { this.gc(); Store.set('replays', this.replays); Store.set('saved', this.saved); }
        else if (k === 'last') Store.set('last', this.last);
      }
    },
    gc() {
      const keep = new Set(this.saved);
      for (const t in this.scores) for (const e of this.scores[t]) if (e.rid) keep.add(e.rid);
      for (const k in this.replays) if (!keep.has(k)) delete this.replays[k];
    },
    reset() {
      Store.clear();
      this.scores = { score: [], floor: [], combo: [] };
      this.records = defRecords();
      this.stats = defStats();
      this.ach = {};
      this.replays = {};
      this.saved = [];
      this.last = null;
      saveSettings();
    }
  };
})();

const RANKS = [
  { r: 'F', floor: 50 },
  { r: 'E', floor: 100, combo: 7, cc1: 55 },
  { r: 'D', floor: 150, combo: 15, cc1: 65 },
  { r: 'C', floor: 200, combo: 25, cc1: 75 },
  { r: 'B', floor: 300, combo: 35, cc1: 85 },
  { r: 'A', floor: 400, combo: 70, cc1: 95 },
  { r: '1', stars: 1, floor: 500, combo: 120, cc1: 105, nml: 400 },
  { r: '2', stars: 2, floor: 600, combo: 200, cc1: 115, nml: 500 },
  { r: '3', stars: 3, floor: 750, combo: 300, cc1: 125, nml: 600 },
  { r: '4', stars: 4, floor: 1000, combo: 400, cc1: 135, nml: 700 },
  { r: '5', stars: 5, floor: 1500, combo: 650, cc1: 145, nml: 1200 }
];
function rankMet(rk, rec) {
  return rec.floor >= rk.floor && (!rk.combo || rec.combo >= rk.combo) && (!rk.cc1 || rec.cc[0] >= rk.cc1) && (!rk.nml || rec.nml >= rk.nml);
}
function currentRank(rec) { let r = -1; for (let i = 0; i < RANKS.length; i++) if (rankMet(RANKS[i], rec)) r = i; else break; return r; }
// ===================== audio: synthesized effects, music, voice =====================
const Sound = (() => {
  let ac = null, master = null, sfxBus = null, musBus = null, duck = null, noiseBuf = null, pulse = null;
  const mtof = m => 440 * Math.pow(2, (m - 69) / 12);

  function init() {
    if (ac) { if (ac.state === 'suspended') ac.resume().catch(() => {}); return; }
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return;
    try { ac = new AC(); } catch (e) { ac = null; return; }
    const comp = ac.createDynamicsCompressor();
    comp.threshold.value = -12; comp.knee.value = 10; comp.ratio.value = 4; comp.attack.value = 0.003; comp.release.value = 0.2;
    master = ac.createGain(); master.gain.value = 0.9;
    master.connect(comp); comp.connect(ac.destination);
    sfxBus = ac.createGain(); sfxBus.connect(master);
    duck = ac.createGain(); duck.connect(master);
    musBus = ac.createGain(); musBus.connect(duck);
    const len = Math.floor(ac.sampleRate * 1.2);
    noiseBuf = ac.createBuffer(1, len, ac.sampleRate);
    const d = noiseBuf.getChannelData(0);
    for (let i = 0; i < len; i++) d[i] = Math.random() * 2 - 1;
    const n = 40, re = new Float32Array(n), im = new Float32Array(n);
    for (let k = 1; k < n; k++) im[k] = (2 / (k * Math.PI)) * Math.sin(k * Math.PI * 0.25);
    pulse = ac.createPeriodicWave(re, im);
    applyVolumes();
    if (ac.state === 'suspended') ac.resume().catch(() => {});
  }
  function applyVolumes() {
    if (!ac) return;
    sfxBus.gain.value = Math.pow(settings.sfx / 10, 1.4) * 1.05;
    musBus.gain.value = Math.pow(settings.music / 10, 1.4) * 0.68;
  }
  function setDuck(v) { if (ac) duck.gain.setTargetAtTime(v, ac.currentTime, 0.08); }
  function suspend(yes) { if (!ac) return; if (yes) ac.suspend().catch(() => {}); else ac.resume().catch(() => {}); }

  // one oscillator note with an envelope
  function tone(type, freq, t, dur, vol, o) {
    o = o || {};
    const osc = ac.createOscillator();
    if (type === 'pulse') osc.setPeriodicWave(pulse); else osc.type = type;
    osc.frequency.setValueAtTime(freq, t);
    if (o.to) {
      if (o.lin) osc.frequency.linearRampToValueAtTime(o.to, t + (o.slide || dur));
      else osc.frequency.exponentialRampToValueAtTime(o.to, t + (o.slide || dur));
    }
    if (o.det) osc.detune.value = o.det;
    if (o.vib) {
      const l = ac.createOscillator(), lg = ac.createGain();
      l.frequency.value = o.vibRate || 6; lg.gain.value = freq * o.vib;
      l.connect(lg); lg.connect(osc.frequency);
      l.start(t + (o.vibDelay || 0)); l.stop(t + dur + 0.1);
    }
    const g = ac.createGain();
    const a = o.a || 0.004;
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(vol, t + a);
    if (o.hold) {
      const r = o.r || 0.06;
      g.gain.setValueAtTime(vol, t + Math.max(a + 0.001, dur - r));
      g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    } else g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    let node = osc;
    if (o.lp || o.hp || o.bp) {
      const f = ac.createBiquadFilter();
      f.type = o.lp ? 'lowpass' : o.hp ? 'highpass' : 'bandpass';
      f.frequency.value = o.lp || o.hp || o.bp;
      if (o.q) f.Q.value = o.q;
      osc.connect(f); node = f;
    }
    node.connect(g); g.connect(o.dest || sfxBus);
    osc.start(t); osc.stop(t + dur + 0.05);
  }
  function noise(t, dur, vol, o) {
    o = o || {};
    const src = ac.createBufferSource(); src.buffer = noiseBuf; src.loop = true;
    const f = ac.createBiquadFilter(); f.type = o.type || 'bandpass';
    f.frequency.setValueAtTime(o.f || 1000, t);
    if (o.to) f.frequency.exponentialRampToValueAtTime(o.to, t + dur);
    f.Q.value = o.q === undefined ? 1 : o.q;
    const g = ac.createGain();
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(vol, t + (o.a || 0.003));
    g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
    src.connect(f); f.connect(g); g.connect(o.dest || sfxBus);
    src.start(t, Math.random() * 0.8); src.stop(t + dur + 0.05);
  }
  const ok = () => ac && ac.state !== 'closed' && settings.sfx > 0;
  let lastLand = 0, lastWall = 0;

  const sfx = {
    jump(power, spin) {
      if (!ok()) return;
      const t = ac.currentTime, f = 250 + power * 330;
      tone('square', f, t, 0.14, 0.09, { to: f * 2.2, slide: 0.12, lp: 2600 });
      tone('triangle', f / 2, t, 0.13, 0.14, { to: f * 1.1, slide: 0.11 });
      if (spin) noise(t, 0.38, 0.1, { f: 600, to: 4200, q: 0.9 });
    },
    land(impact) {
      if (!ok()) return;
      const t = ac.currentTime; if (t - lastLand < 0.05) return; lastLand = t;
      const v = clamp(impact / 15, 0.15, 1);
      noise(t, 0.08, 0.13 * v, { type: 'lowpass', f: 520, q: 0.6 });
      tone('sine', 130, t, 0.09, 0.16 * v, { to: 55 });
    },
    wall(speed) {
      if (!ok()) return;
      const t = ac.currentTime; if (t - lastWall < 0.05) return; lastWall = t;
      const v = clamp(speed / 9, 0.25, 1);
      tone('square', 360, t, 0.1, 0.08 * v, { to: 150, lp: 2000 });
      tone('sine', 900, t, 0.06, 0.06 * v, { to: 500 });
      noise(t, 0.05, 0.08 * v, { f: 2600, q: 1.4 });
    },
    bump() {
      if (!ok()) return;
      const t = ac.currentTime;
      tone('sine', 160, t, 0.08, 0.12, { to: 80 });
      noise(t, 0.05, 0.06, { type: 'lowpass', f: 800 });
    },
    comboStep(k) {
      if (!ok()) return;
      const sc = [0, 2, 4, 7, 9, 12, 14, 16, 19, 21, 24, 26, 28, 31, 33, 36];
      const m = 72 + sc[Math.min(k - 1, sc.length - 1)];
      const t = ac.currentTime;
      tone('pulse', mtof(m), t, 0.1, 0.07, { lp: 5000 });
      tone('sine', mtof(m + 12), t + 0.035, 0.09, 0.045);
    },
    combo(tier) {
      if (!ok()) return;
      const t = ac.currentTime;
      const chord = [0, 4, 7, 12, 16, 19, 24, 28];
      const base = 67 + Math.min(Math.max(tier, 0), 7);
      const n = 3 + Math.min(Math.max(tier, 0), 5);
      for (let i = 0; i < n; i++) {
        tone('pulse', mtof(base + chord[i]), t + i * 0.055, 0.16, 0.075, { lp: 6000 });
        tone('triangle', mtof(base + chord[i] - 12), t + i * 0.055, 0.18, 0.07);
      }
      const te = t + n * 0.055;
      tone('square', mtof(base + 12), te, 0.55, 0.06, { hold: true, r: 0.22, vib: 0.012, vibRate: 7, vibDelay: 0.1, lp: 4200 });
      tone('triangle', mtof(base), te, 0.55, 0.08, { hold: true, r: 0.22 });
      if (tier >= 3) noise(te, 0.9, 0.05, { type: 'highpass', f: 6500, q: 0.3 });
      if (tier >= 5) for (let i = 0; i < 7; i++) tone('sine', mtof(96 + Math.floor(Math.random() * 12)), te + 0.08 + i * 0.07, 0.12, 0.035);
    },
    hurry() {
      if (!ok()) return;
      const t = ac.currentTime;
      for (let i = 0; i < 12; i++) {
        const tt = t + i * 0.065;
        tone('sine', 1500, tt, 0.07, 0.05);
        tone('sine', 1500 * 2.76, tt, 0.05, 0.018);
        tone('triangle', 1180, tt + 0.03, 0.05, 0.03);
      }
      tone('triangle', 740, t, 0.85, 0.04, { hold: true, r: 0.3 });
    },
    clockBreak() {
      if (!ok()) return;
      const t = ac.currentTime + 0.25;
      tone('sine', 260, t, 0.7, 0.1, { to: 1300, slide: 0.18, vib: 0.18, vibRate: 22 });
      noise(t, 0.5, 0.12, { type: 'highpass', f: 3000, q: 0.4 });
      tone('square', 90, t + 0.05, 0.3, 0.05, { to: 50, lp: 700 });
    },
    dead() {
      if (!ok()) return;
      const t = ac.currentTime;
      tone('square', 720, t, 1.15, 0.07, { to: 85, slide: 1.1, lp: 2200, vib: 0.03, vibRate: 9, hold: true, r: 0.25 });
      tone('triangle', 360, t, 1.15, 0.06, { to: 45, slide: 1.1, hold: true, r: 0.25 });
    },
    move() { if (!ok()) return; tone('square', 900, ac.currentTime, 0.04, 0.035, { lp: 3200 }); },
    select() {
      if (!ok()) return;
      const t = ac.currentTime;
      tone('pulse', 660, t, 0.07, 0.06); tone('pulse', 990, t + 0.06, 0.12, 0.06);
    },
    back() {
      if (!ok()) return;
      const t = ac.currentTime;
      tone('pulse', 700, t, 0.07, 0.05); tone('pulse', 470, t + 0.06, 0.12, 0.05);
    },
    fanfare() {
      if (!ok()) return;
      const t = ac.currentTime;
      [72, 76, 79, 84].forEach((m, i) => { tone('square', mtof(m), t + i * 0.1, 0.14, 0.06, { lp: 3500 }); tone('triangle', mtof(m - 12), t + i * 0.1, 0.14, 0.06); });
      [72, 76, 79, 84].forEach(m => tone('pulse', mtof(m), t + 0.42, 0.8, 0.04, { hold: true, r: 0.3, vib: 0.01, vibDelay: 0.2 }));
    },
    trophy() {
      if (!ok()) return;
      const t = ac.currentTime;
      [88, 92, 95, 100].forEach((m, i) => tone('sine', mtof(m), t + i * 0.07, 0.3, 0.055));
      tone('triangle', mtof(76), t, 0.45, 0.05, { hold: true, r: 0.2 });
    },
    zone() {
      if (!ok()) return;
      const t = ac.currentTime;
      noise(t, 0.6, 0.06, { f: 400, to: 5000, q: 0.7 });
      [79, 83, 86].forEach((m, i) => tone('triangle', mtof(m), t + 0.1 + i * 0.08, 0.35, 0.06));
    },
    tick() { if (!ok()) return; tone('square', 1800, ac.currentTime, 0.02, 0.02, { lp: 4000 }); }
  };

  // ---------- music: an original looping groove, built from patterns ----------
  const PROG = ['Am', 'F', 'C', 'G', 'Am', 'F', 'Dm', 'E'];
  const CH = { Am: [57, 60, 64], F: [57, 60, 65], C: [55, 60, 64], G: [55, 59, 62], Dm: [57, 62, 65], E: [56, 59, 64] };
  const ROOT = { Am: 45, F: 41, C: 48, G: 43, Dm: 38, E: 40 };
  const LEAD = [
    [[0, 76, 2], [2, 81, 2], [6, 79, 1], [7, 81, 1], [8, 76, 3], [11, 74, 1], [12, 72, 2], [14, 74, 2]],
    [[0, 72, 3], [3, 69, 1], [4, 72, 2], [6, 74, 2], [8, 77, 4], [12, 76, 2], [14, 74, 2]],
    [[0, 76, 2], [2, 79, 2], [4, 84, 3], [7, 83, 1], [8, 79, 2], [10, 76, 2], [12, 79, 4]],
    [[0, 74, 2], [2, 71, 2], [4, 74, 2], [6, 79, 2], [8, 74, 6]],
    [[0, 81, 2], [2, 79, 1], [3, 81, 1], [4, 84, 2], [6, 81, 2], [8, 79, 2], [10, 76, 2], [12, 74, 2], [14, 76, 2]],
    [[0, 77, 3], [3, 76, 1], [4, 72, 2], [6, 69, 2], [8, 72, 2], [10, 74, 2], [12, 77, 2], [14, 81, 2]],
    [[0, 81, 2], [2, 77, 2], [4, 74, 2], [6, 77, 1], [7, 79, 1], [8, 81, 3], [11, 79, 1], [12, 77, 2], [14, 74, 2]],
    [[0, 76, 2], [2, 80, 2], [4, 83, 3], [7, 80, 1], [8, 76, 6]]
  ];
  const BASS = [[0, 0, 3], [3, 0, 2], [6, 7, 2], [8, 12, 2], [10, 0, 2], [14, 7, 2]];
  const ARP = [0, 1, 2, 3, 2, 1, 0, 1, 2, 3, 4, 3, 2, 1, 2, 3];
  let mode = null, bpm = 96, nextT = 0, step = 0, timer = null;
  function drum(kind, t, v) {
    if (kind === 'k') {
      tone('sine', 155, t, 0.26, 0.55 * v, { to: 42, slide: 0.12, dest: musBus });
      tone('triangle', 90, t, 0.06, 0.2 * v, { to: 40, dest: musBus });
    } else if (kind === 's') {
      noise(t, 0.16, 0.28 * v, { f: 1900, q: 0.7, dest: musBus });
      tone('triangle', 190, t, 0.1, 0.18 * v, { to: 140, dest: musBus });
    } else if (kind === 'h') noise(t, 0.035, 0.1 * v, { type: 'highpass', f: 7500, q: 0.2, dest: musBus });
    else if (kind === 'o') noise(t, 0.2, 0.07 * v, { type: 'highpass', f: 6500, q: 0.2, dest: musBus });
  }
  function playStep(s, t) {
    const sd = 60 / bpm / 4;
    const bar = Math.floor(s / 16), st = s % 16;
    const bi = bar % 8, chord = PROG[bi];
    const section = Math.floor(bar / 8) % 2;
    const tt = t + (st % 2 ? sd * 0.14 : 0);
    const game = mode === 'game';
    // drums
    const fill = bi === 7 && section === 1;
    if (st === 0 || st === 10 || (game && (st === 7 || (st === 13 && bi % 2)))) drum('k', tt, st === 0 ? 1 : 0.8);
    if (game || bar % 2) {
      if (st === 4 || st === 12) drum('s', tt, 1);
      if (fill && st >= 13) drum('s', tt, 0.55);
    }
    if (st % 2 === 0) drum('h', tt, st % 4 === 0 ? 0.9 : 0.6);
    else if (game && st === 15) drum('h', tt, 0.4);
    if (game && st === 14 && bi % 4 === 3) drum('o', tt, 1);
    // bass
    for (const b of BASS) if (b[0] === st) tone('triangle', mtof(ROOT[chord] + b[1]), tt, b[2] * sd * 0.95, 0.24, { hold: true, r: 0.04, dest: musBus, lp: 900 });
    // pads (short chord stabs)
    if (st === 0 || st === 6 || (game && st === 11)) {
      const len = st === 0 ? 5 : 3;
      for (const m of CH[chord]) tone('sawtooth', mtof(m), tt, len * sd, 0.028, { hold: true, r: 0.06, lp: 1400, det: (Math.random() - 0.5) * 12, dest: musBus });
    }
    // lead or arpeggio
    if (game && section === 0) {
      for (const n of LEAD[bi]) if (n[0] === st) tone('pulse', mtof(n[1]), tt, n[2] * sd * 0.92, 0.06, { hold: true, r: 0.05, vib: 0.008, vibDelay: 0.12, lp: 3800, dest: musBus });
    } else {
      const notes = CH[chord].concat([CH[chord][0] + 12, CH[chord][1] + 12]);
      const m = notes[ARP[st]] + 12;
      tone('square', mtof(m), tt, sd * 0.9, game ? 0.03 : 0.022, { lp: game ? 3000 : 2000, dest: musBus });
    }
  }
  function schedule() {
    if (!ac || !mode) return;
    if (nextT < ac.currentTime - 0.3) nextT = ac.currentTime + 0.05;
    while (nextT < ac.currentTime + 0.14) {
      if (settings.music > 0) playStep(step, nextT);
      nextT += 60 / bpm / 4;
      step++;
    }
  }
  const music = {
    start(m) {
      if (!ac) return;
      if (mode === m) return;
      mode = m; step = 0; nextT = ac.currentTime + 0.08;
      bpm = m === 'game' ? 104 : 94;
      if (!timer) timer = setInterval(schedule, 25);
    },
    stop() { mode = null; },
    level(l) { if (mode === 'game') bpm = 104 + Math.max(0, l - 1) * 5; },
    get mode() { return mode; }
  };

  // ---------- voice callouts (browser speech, optional) ----------
  let voiceObj = null;
  function pickVoice() {
    try {
      const vs = window.speechSynthesis.getVoices();
      voiceObj = vs.find(v => /en[-_]US/i.test(v.lang) && /female|samantha|zira|google/i.test(v.name)) || vs.find(v => /^en/i.test(v.lang)) || null;
    } catch (e) { voiceObj = null; }
  }
  try { if (window.speechSynthesis) { pickVoice(); window.speechSynthesis.onvoiceschanged = pickVoice; } } catch (e) { /* no speech */ }
  function say(text) {
    if (!settings.voice || settings.sfx === 0) return;
    try {
      const ss = window.speechSynthesis;
      if (!ss || typeof SpeechSynthesisUtterance === 'undefined') return;
      ss.cancel();
      const u = new SpeechSynthesisUtterance(text);
      u.lang = 'en-US'; u.rate = 1.05; u.pitch = 1.3; u.volume = clamp(settings.sfx / 10 + 0.15, 0, 1);
      if (voiceObj) u.voice = voiceObj;
      ss.speak(u);
    } catch (e) { /* ignore */ }
  }

  return { init, applyVolumes, setDuck, suspend, sfx, music, say, get ready() { return !!ac; } };
})();
// ===================== input: keyboard, touch buttons, gamepad =====================
const Input = (() => {
  const down = new Set();
  const queue = [];          // key presses for menus: {code, key, repeat}
  const touch = { left: 0, right: 0, jump: 0 };
  const pad = { left: false, right: false, jump: false };
  const padPrev = {};
  let capture = null;
  let usedTouch = false;
  let jLatch = false;   // a quick tap between two ticks still counts as a jump
  const isField = t => t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.tagName === 'BUTTON');

  window.addEventListener('keydown', e => {
    if (isField(e.target)) return;
    Sound.init();
    if (capture) { e.preventDefault(); const cb = capture; capture = null; cb(e.code); return; }
    if (/^(Arrow|Space|PageUp|PageDown|Backspace)/.test(e.code) || e.code === 'Tab') e.preventDefault();
    if (!e.repeat) { down.add(e.code); if (settings.keys.jump.includes(e.code)) jLatch = true; }
    queue.push({ code: e.code, key: e.key, repeat: e.repeat });
    if (queue.length > 20) queue.shift();
  });
  window.addEventListener('keyup', e => { down.delete(e.code); });
  window.addEventListener('blur', () => { down.clear(); resetTouch(); });

  // touch buttons: pointers can slide between buttons
  const ptr = new Map();
  const btnEls = Array.from(document.querySelectorAll('#touch .tbtn'));
  function refreshBtns() { for (const b of btnEls) b.classList.toggle('on', touch[b.dataset.k] > 0); }
  function setPtr(id, k) {
    const old = ptr.get(id);
    if (old === k) return;
    if (old) touch[old] = Math.max(0, touch[old] - 1);
    if (k) { touch[k]++; ptr.set(id, k); if (k === 'jump') jLatch = true; } else ptr.delete(id);
    refreshBtns();
  }
  function resetTouch() { ptr.clear(); touch.left = touch.right = touch.jump = 0; refreshBtns(); }
  for (const b of btnEls) {
    const k = b.dataset.k;
    b.addEventListener('pointerdown', e => {
      e.preventDefault();
      usedTouch = true;
      Sound.init();
      try { b.releasePointerCapture(e.pointerId); } catch (err) { /* not captured */ }
      setPtr(e.pointerId, k);
    });
    b.addEventListener('pointerenter', e => { if (e.pointerType !== 'mouse' || e.buttons) setPtr(e.pointerId, k); });
    b.addEventListener('pointerleave', e => { if (ptr.get(e.pointerId) === k) setPtr(e.pointerId, null); });
    b.addEventListener('contextmenu', e => e.preventDefault());
  }
  const endPtr = e => setPtr(e.pointerId, null);
  window.addEventListener('pointerup', endPtr);
  window.addEventListener('pointercancel', endPtr);
  window.addEventListener('touchstart', () => { usedTouch = true; }, { passive: true });

  function pollPad() {
    let gp = null;
    try { const pads = navigator.getGamepads ? navigator.getGamepads() : []; for (const p of pads) if (p && p.connected) { gp = p; break; } } catch (e) { gp = null; }
    if (!gp) { pad.left = pad.right = pad.jump = false; return; }
    const b = i => !!(gp.buttons[i] && gp.buttons[i].pressed);
    const ax = gp.axes[0] || 0, ay = gp.axes[1] || 0;
    const L = ax < -0.35 || b(14), R = ax > 0.35 || b(15), U = ay < -0.55 || b(12), D = ay > 0.55 || b(13);
    const pj = b(0) || b(2) || b(12);
    if (pj && !pad.jump) jLatch = true;
    pad.left = L; pad.right = R; pad.jump = pj;
    const edge = (name, v, code) => { if (v && !padPrev[name]) { Sound.init(); queue.push({ code, key: '', repeat: false, pad: true }); } padPrev[name] = v; };
    edge('u', U, 'ArrowUp'); edge('d', D, 'ArrowDown'); edge('l', L, 'ArrowLeft'); edge('r', R, 'ArrowRight');
    edge('a', b(0), 'Enter'); edge('b', b(1), 'Escape'); edge('st', b(9), 'KeyP');
  }

  function bits() {
    const k = settings.keys;
    const has = a => { const l = k[a]; for (let i = 0; i < l.length; i++) if (down.has(l[i])) return true; return false; };
    const Lf = has('left') || touch.left > 0 || pad.left;
    const Rt = has('right') || touch.right > 0 || pad.right;
    const J = has('jump') || touch.jump > 0 || pad.jump || jLatch;
    jLatch = false;
    return (Lf ? 1 : 0) | (Rt ? 2 : 0) | (J ? 4 : 0);
  }
  function takeQueue() { const q = queue.slice(); queue.length = 0; return q; }
  function navOf(ev) {
    switch (ev.code) {
      case 'ArrowUp': case 'KeyW': return 'up';
      case 'ArrowDown': case 'KeyS': return 'down';
      case 'ArrowLeft': case 'KeyA': return 'left';
      case 'ArrowRight': case 'KeyD': return 'right';
      case 'Enter': case 'NumpadEnter': case 'Space': return 'ok';
      case 'Escape': case 'Backspace': return 'back';
      default: return null;
    }
  }
  const isPause = code => settings.keys.pause.includes(code);
  function keyName(code) {
    const tr = settings.lang === 1;
    const map = {
      ArrowLeft: tr ? 'SOL OK' : 'LEFT', ArrowRight: tr ? 'SAĞ OK' : 'RIGHT', ArrowUp: tr ? 'YUKARI' : 'UP', ArrowDown: tr ? 'AŞAĞI' : 'DOWN',
      Space: tr ? 'BOŞLUK' : 'SPACE', Escape: 'ESC', Enter: 'ENTER', ShiftLeft: 'L-SHIFT', ShiftRight: 'R-SHIFT',
      ControlLeft: 'L-CTRL', ControlRight: 'R-CTRL', AltLeft: 'L-ALT', AltRight: 'R-ALT', Tab: 'TAB', Backspace: 'BKSP'
    };
    if (map[code]) return map[code];
    if (/^Key[A-Z]$/.test(code)) return code.slice(3);
    if (/^Digit\d$/.test(code)) return code.slice(5);
    if (/^Numpad/.test(code)) return 'NUM ' + code.slice(6).toUpperCase();
    return code.replace(/([a-z])([A-Z])/g, '$1 $2').toUpperCase();
  }
  return {
    bits, takeQueue, navOf, isPause, keyName, pollPad, resetTouch,
    capture(cb) { capture = cb; },
    cancelCapture() { capture = null; },
    get capturing() { return !!capture; },
    get usedTouch() { return usedTouch; },
    clearKeys() { down.clear(); jLatch = false; }
  };
})();
// ===================== drawing helpers + pre-rendered art =====================
const DISPLAY = '"Lilita One", "Arial Black", Impact, sans-serif';
const UIF = '"Baloo 2", "Trebuchet MS", "Segoe UI", system-ui, sans-serif';
const OUTL = '#1d1631';

function rrect(g, x, y, w, h, r) {
  const rs = typeof r === 'number' ? [r, r, r, r] : r;
  const m = Math.min(w, h) / 2;
  const tl = Math.min(rs[0], m), tr = Math.min(rs[1], m), br = Math.min(rs[2], m), bl = Math.min(rs[3], m);
  g.beginPath();
  g.moveTo(x + tl, y);
  g.lineTo(x + w - tr, y); g.arcTo(x + w, y, x + w, y + tr, tr);
  g.lineTo(x + w, y + h - br); g.arcTo(x + w, y + h, x + w - br, y + h, br);
  g.lineTo(x + bl, y + h); g.arcTo(x, y + h, x, y + h - bl, bl);
  g.lineTo(x, y + tl); g.arcTo(x, y, x + tl, y, tl);
  g.closePath();
}
function circ(g, x, y, r) { g.beginPath(); g.arc(x, y, Math.max(0.01, r), 0, TAU); }
function ell(g, x, y, rx, ry, rot) { g.beginPath(); g.ellipse(x, y, Math.max(0.01, rx), Math.max(0.01, ry), rot || 0, 0, TAU); }
function starPath(g, cx, cy, spikes, outer, inner, rot) {
  g.beginPath();
  for (let i = 0; i < spikes * 2; i++) {
    const r = i % 2 ? inner : outer, a = rot + (i * Math.PI) / spikes;
    if (i === 0) g.moveTo(cx + Math.cos(a) * r, cy + Math.sin(a) * r); else g.lineTo(cx + Math.cos(a) * r, cy + Math.sin(a) * r);
  }
  g.closePath();
}
function sparkle(g, x, y, s, col) {
  g.fillStyle = col;
  g.beginPath();
  g.moveTo(x, y - s * 2); g.quadraticCurveTo(x, y, x + s * 2, y); g.quadraticCurveTo(x, y, x, y + s * 2);
  g.quadraticCurveTo(x, y, x - s * 2, y); g.quadraticCurveTo(x, y, x, y - s * 2);
  g.fill();
}
function leaf(g, x, y, ang, col, s) {
  g.save(); g.translate(x, y); g.rotate(ang); g.scale(s || 1, s || 1);
  g.beginPath(); g.moveTo(0, 0); g.quadraticCurveTo(4, -3.2, 9, 0); g.quadraticCurveTo(4, 3.2, 0, 0);
  g.fillStyle = col; g.fill(); g.strokeStyle = '#1e4d1f'; g.lineWidth = 0.9; g.stroke();
  g.restore();
}
// Outlined text. o: {size, font, fill, stroke, lw, align, base, weight, alpha}
function text(g, str, x, y, o) {
  o = o || {};
  g.font = (o.weight ? o.weight + ' ' : '') + (o.size || 16) + 'px ' + (o.font || DISPLAY);
  g.textAlign = o.align || 'center';
  g.textBaseline = o.base || 'middle';
  if (o.stroke) { g.lineJoin = 'round'; g.miterLimit = 2; g.lineWidth = o.lw || 4; g.strokeStyle = o.stroke; g.strokeText(str, x, y); }
  g.fillStyle = o.fill || '#fff';
  g.fillText(str, x, y);
}
function textW(g, str, size, font, weight) { g.font = (weight ? weight + ' ' : '') + size + 'px ' + (font || DISPLAY); return g.measureText(str).width; }
function fitSize(g, str, size, maxW, font, weight) { let s = size; while (s > 8 && textW(g, str, s, font, weight) > maxW) s -= 1; return s; }

const ZONE_VIS = [
  { tint: '#9690c0', wall: '#bab4d6', sky: ['#2a2350', '#f39c6b'], accent: '#e25b45', amb: 'dust' },
  { tint: '#86b9e8', wall: '#c4e4ff', sky: ['#8fd0ff', '#eaf8ff'], accent: '#3fa9f5', amb: 'snow' },
  { tint: '#b48c66', wall: '#dcb690', sky: ['#5fb0e8', '#ffe2a8'], accent: '#b5652b', amb: 'leaf' },
  { tint: '#8e9bab', wall: '#bfcbd6', sky: ['#4b5a6e', '#a9bccf'], accent: '#ffc93c', amb: 'spark' },
  { tint: '#e6a6c9', wall: '#ffd2ea', sky: ['#ffb3de', '#fff0b3'], accent: '#ff4fa3', amb: 'sprinkle' },
  { tint: '#a39680', wall: '#e2d6b8', sky: ['#1e1a2e', '#6b4f7a'], accent: '#c9b98a', amb: 'wisp' },
  { tint: '#7fb07a', wall: '#b2dea2', sky: ['#2e7d4f', '#d4eca4'], accent: '#3c9a3c', amb: 'firefly' },
  { tint: '#80a69f', wall: '#c4dbd2', sky: ['#35524f', '#e0b98a'], accent: '#c0392b', amb: 'steam' },
  { tint: '#a9c8f5', wall: '#e8f1ff', sky: ['#4f9ff0', '#e2f3ff'], accent: '#ffffff', amb: 'feather' },
  { tint: '#c9a9f0', wall: '#ecdfff', sky: ['#ff8fcf', '#ffe29a'], accent: '#9b59ff', amb: 'sparkle' },
  { tint: '#5c5a9c', wall: '#aaaae2', sky: ['#05041a', '#2c1d63'], accent: '#ffe45c', amb: 'shoot' }
];
const STAR_COLS = ['#ffe45c', '#ff7ad9', '#7cf0ff', '#9dff7a', '#ffb347', '#c7a4ff', '#ffffff'];

// ---------- floor painters: top surface at FT, body FB tall, decorations may hang below ----------
const FT = 12, FB = 22, FSH = 66;
function crackLine(g, x, y, r) {
  g.strokeStyle = 'rgba(30,24,52,0.55)'; g.lineWidth = 1;
  g.beginPath(); g.moveTo(x, y);
  for (let i = 0; i < 4; i++) { x += r() * 7 - 3; y += 2.5 + r() * 2; g.lineTo(x, y); }
  g.stroke();
}
function rivet(g, x, y) { g.fillStyle = '#5f6b79'; circ(g, x, y, 1.8); g.fill(); g.fillStyle = '#f2f6fa'; circ(g, x - 0.5, y - 0.6, 0.7); g.fill(); }
function dropShadow(g, w, rad, h) { g.fillStyle = 'rgba(0,0,0,0.26)'; rrect(g, 4, FT + 6, w - 5, h || FB, rad); g.fill(); }
const FLOOR_PAINTERS = [
  function stone(g, w, r) {
    const y = FT, h = FB;
    dropShadow(g, w, 6);
    const gr = g.createLinearGradient(0, y, 0, y + h);
    gr.addColorStop(0, '#c6c3d6'); gr.addColorStop(0.3, '#a3a0ba'); gr.addColorStop(1, '#625c7a');
    rrect(g, 1, y, w - 2, h, 6); g.fillStyle = gr; g.fill();
    g.save(); rrect(g, 1, y, w - 2, h, 6); g.clip();
    g.fillStyle = '#e9e6f3'; g.fillRect(0, y, w, 4);
    g.fillStyle = 'rgba(255,255,255,0.3)'; g.fillRect(0, y + 4, w, 1);
    g.strokeStyle = 'rgba(40,34,62,0.5)'; g.lineWidth = 1.3;
    for (let x = 10 + r() * 22; x < w - 8; x += 26 + r() * 16) { g.beginPath(); g.moveTo(x, y + 5); g.lineTo(x, y + h); g.stroke(); }
    g.strokeStyle = 'rgba(40,34,62,0.22)'; g.beginPath(); g.moveTo(0, y + 13.5); g.lineTo(w, y + 13.5); g.stroke();
    for (let i = 0; i < w / 5; i++) { g.fillStyle = 'rgba(30,24,52,' + (0.12 + r() * 0.18).toFixed(2) + ')'; g.fillRect(r() * w, y + 6 + r() * (h - 8), 1.6, 1.6); }
    if (r() < 0.6) crackLine(g, 8 + r() * (w - 24), y + 5, r);
    g.restore();
    rrect(g, 1, y, w - 2, h, 6); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
  },
  function ice(g, w, r) {
    const y = FT, h = FB;
    for (let x = 6 + r() * 8; x < w - 6; x += 7 + r() * 15) {
      const len = 5 + r() * 18, wd = 2.5 + r() * 3;
      const gi = g.createLinearGradient(0, y + h - 2, 0, y + h + len);
      gi.addColorStop(0, '#c9f1ff'); gi.addColorStop(1, 'rgba(170,228,255,0.55)');
      g.beginPath(); g.moveTo(x - wd, y + h - 4); g.lineTo(x + wd, y + h - 4); g.lineTo(x + (r() - 0.5) * 2, y + h + len); g.closePath();
      g.fillStyle = gi; g.fill(); g.strokeStyle = '#2a6b9c'; g.lineWidth = 1; g.stroke();
    }
    dropShadow(g, w, 7);
    const gr = g.createLinearGradient(0, y, 0, y + h);
    gr.addColorStop(0, '#dff9ff'); gr.addColorStop(0.45, '#93d8f7'); gr.addColorStop(1, '#3d8fd2');
    rrect(g, 1, y, w - 2, h, 7); g.fillStyle = gr; g.fill();
    g.save(); rrect(g, 1, y, w - 2, h, 7); g.clip();
    g.fillStyle = 'rgba(255,255,255,0.38)';
    for (let x = r() * 30; x < w + 20; x += 30 + r() * 24) { g.beginPath(); g.moveTo(x, y + h); g.lineTo(x + 5, y + h); g.lineTo(x + 17, y); g.lineTo(x + 12, y); g.closePath(); g.fill(); }
    g.strokeStyle = 'rgba(255,255,255,0.55)'; g.lineWidth = 0.8;
    for (let i = 0; i < w / 40; i++) { let x = r() * w, yy = y + 8 + r() * 6; g.beginPath(); g.moveTo(x, yy); for (let k = 0; k < 3; k++) { x += 3 + r() * 5; yy += (r() - 0.5) * 5; g.lineTo(x, yy); } g.stroke(); }
    g.restore();
    rrect(g, 1, y, w - 2, h, 7); g.lineWidth = 2; g.strokeStyle = '#1f5a8a'; g.stroke();
    rrect(g, 0, y - 3, w, 7, 4); g.fillStyle = '#ffffff'; g.fill(); g.strokeStyle = '#9cc3dd'; g.lineWidth = 1.2; g.stroke();
    g.fillStyle = '#ffffff';
    for (let x = 4 + r() * 6; x < w - 4; x += 6 + r() * 10) { circ(g, x, y + 3.5, 1.6 + r() * 1.6); g.fill(); }
  },
  function wood(g, w, r) {
    const y = FT, h = FB;
    for (const bx of [12, w - 12]) {
      g.beginPath(); g.moveTo(bx - 6, y + h - 2); g.lineTo(bx + 6, y + h - 2); g.lineTo(bx, y + h + 13); g.closePath();
      g.fillStyle = '#6b3f1d'; g.fill(); g.strokeStyle = OUTL; g.lineWidth = 1.5; g.stroke();
    }
    dropShadow(g, w, 3);
    for (const [py, ph] of [[y, 11], [y + 11, 11]]) {
      const gr = g.createLinearGradient(0, py, 0, py + ph);
      gr.addColorStop(0, '#e6a866'); gr.addColorStop(1, '#a1622d');
      rrect(g, 1, py, w - 2, ph, 3); g.fillStyle = gr; g.fill();
      g.save(); rrect(g, 1, py, w - 2, ph, 3); g.clip();
      g.strokeStyle = 'rgba(90,48,18,0.35)'; g.lineWidth = 0.8;
      for (let k = 0; k < 3; k++) {
        const gy = py + 2.5 + k * 3 + r(), ph2 = r() * 6;
        g.beginPath(); g.moveTo(0, gy);
        for (let x = 0; x <= w; x += 8) g.lineTo(x, gy + Math.sin(x * 0.07 + ph2) * 0.9);
        g.stroke();
      }
      if (r() < 0.7) { g.fillStyle = 'rgba(90,48,18,0.5)'; ell(g, 10 + r() * (w - 20), py + ph / 2, 3, 1.5); g.fill(); }
      for (let x = 22 + r() * 30; x < w - 10; x += 40 + r() * 30) {
        g.fillStyle = 'rgba(70,36,12,0.7)'; g.fillRect(x, py, 1.4, ph);
        g.fillStyle = '#d6d0c2'; circ(g, x - 4, py + ph / 2, 1.2); g.fill(); circ(g, x + 5, py + ph / 2, 1.2); g.fill();
      }
      g.restore();
      rrect(g, 1, py, w - 2, ph, 3); g.strokeStyle = '#4a2810'; g.lineWidth = 1.6; g.stroke();
    }
    g.fillStyle = 'rgba(255,232,196,0.55)'; g.fillRect(4, y + 1.2, w - 8, 1.4);
  },
  function steel(g, w, r) {
    const y = FT, h = FB;
    g.fillStyle = 'rgba(0,0,0,0.28)'; g.fillRect(4, y + 6, w - 5, h - 2);
    const gr = g.createLinearGradient(0, y, 0, y + h);
    gr.addColorStop(0, '#dde6ee'); gr.addColorStop(0.5, '#8e9baa'); gr.addColorStop(1, '#4f5b69');
    g.fillStyle = gr; g.fillRect(1, y, w - 2, h);
    g.fillStyle = '#5c6876'; g.fillRect(1, y + 6, w - 2, h - 12);
    for (let x = 20; x < w - 16; x += 22) { g.fillStyle = '#262d36'; rrect(g, x - 5, y + 8, 10, h - 16, 3); g.fill(); }
    g.fillStyle = '#eef3f7'; g.fillRect(1, y, w - 2, 2);
    g.fillStyle = '#a3b0bd'; g.fillRect(1, y + h - 5, w - 2, 3);
    for (let x = 18; x < w - 14; x += 12) { rivet(g, x, y + 3.4); rivet(g, x + 6, y + h - 3); }
    for (const ex of [1, w - 14]) {
      g.save(); g.beginPath(); g.rect(ex, y, 13, h); g.clip();
      g.fillStyle = '#ffc93c'; g.fillRect(ex, y, 13, h);
      g.fillStyle = '#23262b';
      for (let k = -h; k < 20; k += 7) { g.beginPath(); g.moveTo(ex + k, y + h); g.lineTo(ex + k + 3.5, y + h); g.lineTo(ex + k + 3.5 + h, y); g.lineTo(ex + k + h, y); g.closePath(); g.fill(); }
      g.restore();
      g.strokeStyle = OUTL; g.lineWidth = 1.2; g.strokeRect(ex, y, 13, h);
    }
    g.strokeStyle = OUTL; g.lineWidth = 2; g.strokeRect(1, y, w - 2, h);
  },
  function candy(g, w, r) {
    const y = FT, h = FB - 2;
    for (let x = 8 + r() * 12; x < w - 8; x += 14 + r() * 22) {
      const len = 4 + r() * 12;
      g.beginPath(); g.moveTo(x - 3.5, y + h - 4); g.lineTo(x + 3.5, y + h - 4); g.lineTo(x + 3, y + h + len - 3); g.arc(x, y + h + len - 3, 3, 0, Math.PI); g.closePath();
      g.fillStyle = '#ff6fb3'; g.fill(); g.strokeStyle = '#8a1d55'; g.lineWidth = 1.2; g.stroke();
    }
    dropShadow(g, w, 10, h);
    rrect(g, 1, y, w - 2, h, 10); g.fillStyle = '#ff8cc6'; g.fill();
    g.save(); rrect(g, 1, y, w - 2, h, 10); g.clip();
    g.fillStyle = '#fff3fa';
    for (let x = -h; x < w + h; x += 16) { g.beginPath(); g.moveTo(x, y + h); g.lineTo(x + 7, y + h); g.lineTo(x + 7 + h, y); g.lineTo(x + h, y); g.closePath(); g.fill(); }
    const gl = g.createLinearGradient(0, y, 0, y + h);
    gl.addColorStop(0, 'rgba(255,255,255,0.55)'); gl.addColorStop(0.45, 'rgba(255,255,255,0)'); gl.addColorStop(1, 'rgba(120,0,60,0.35)');
    g.fillStyle = gl; g.fillRect(0, y, w, h);
    g.restore();
    rrect(g, 1, y, w - 2, h, 10); g.strokeStyle = '#8a1d55'; g.lineWidth = 2; g.stroke();
    const cols = ['#ffe45c', '#5ce1ff', '#8dff6a', '#ffffff', '#b98cff'];
    for (let i = 0; i < w / 9; i++) { g.save(); g.translate(5 + r() * (w - 10), y + 2 + r() * 3); g.rotate(r() * 3); g.fillStyle = cols[i % cols.length]; g.fillRect(-2, -0.7, 4, 1.4); g.restore(); }
  },
  function bone(g, w, r) {
    const y = FT + 2, h = FB - 6, cy = y + h / 2;
    g.fillStyle = 'rgba(0,0,0,0.22)'; rrect(g, 8, y + 6, w - 14, h, 7); g.fill();
    for (const x of [8, w - 8]) for (const dy of [-5.5, 5.5]) { circ(g, x, cy + dy, 7.5); g.fillStyle = '#f7efd9'; g.fill(); g.strokeStyle = '#5b4a2e'; g.lineWidth = 2; g.stroke(); }
    const gr = g.createLinearGradient(0, y, 0, y + h);
    gr.addColorStop(0, '#fffaf0'); gr.addColorStop(0.6, '#ebe0c2'); gr.addColorStop(1, '#bfae84');
    rrect(g, 8, y, w - 16, h, 6); g.fillStyle = gr; g.fill(); g.strokeStyle = '#5b4a2e'; g.lineWidth = 2; g.stroke();
    for (const x of [8, w - 8]) for (const dy of [-5.5, 5.5]) { circ(g, x, cy + dy, 6.2); g.fillStyle = '#f7efd9'; g.fill(); }
    for (const x of [8, w - 8]) { g.fillStyle = '#f7efd9'; g.fillRect(x - 5, cy - 5, 10, 10); }
    g.fillStyle = 'rgba(255,255,255,0.75)'; g.fillRect(14, y + 2, w - 28, 1.6);
    g.strokeStyle = 'rgba(91,74,46,0.45)'; g.lineWidth = 1;
    for (let x = 30 + r() * 30; x < w - 30; x += 40 + r() * 40) { g.beginPath(); g.moveTo(x, y + 2); g.quadraticCurveTo(x + 3, cy, x - 1, y + h - 2); g.stroke(); }
  },
  function jungle(g, w, r) {
    const y = FT, h = FB - 3;
    for (let x = 10 + r() * 20; x < w - 8; x += 18 + r() * 30) {
      const len = 10 + r() * 22;
      g.strokeStyle = '#2f7d32'; g.lineWidth = 2;
      g.beginPath(); g.moveTo(x, y + h - 2); g.bezierCurveTo(x + 5, y + h + len * 0.3, x - 5, y + h + len * 0.7, x + 2, y + h + len); g.stroke();
      leaf(g, x + 2, y + h + len, 0.4 + r(), '#4caf50', 1);
      if (len > 18) leaf(g, x - 2, y + h + len * 0.5, 2.4, '#66bb6a', 0.9);
    }
    dropShadow(g, w, 8, h);
    const gr = g.createLinearGradient(0, y, 0, y + h);
    gr.addColorStop(0, '#ad7d4c'); gr.addColorStop(1, '#5d3b1c');
    rrect(g, 1, y + 2, w - 2, h - 2, 8); g.fillStyle = gr; g.fill();
    g.save(); rrect(g, 1, y + 2, w - 2, h - 2, 8); g.clip();
    g.strokeStyle = 'rgba(50,28,10,0.45)'; g.lineWidth = 1;
    for (let k = 0; k < 3; k++) { const ly = y + 7 + k * 4; g.beginPath(); g.moveTo(0, ly); for (let x = 0; x <= w; x += 10) g.lineTo(x, ly + (r() - 0.5) * 1.6); g.stroke(); }
    g.fillStyle = '#5cbf4a'; g.fillRect(0, y + 2, w, 3.5);
    g.restore();
    rrect(g, 1, y + 2, w - 2, h - 2, 8); g.strokeStyle = '#2b1a0a'; g.lineWidth = 2; g.stroke();
    for (const ex of [7, w - 7]) {
      ell(g, ex, y + 1 + h / 2, 5, h / 2 - 2); g.fillStyle = '#dcb582'; g.fill(); g.strokeStyle = '#2b1a0a'; g.lineWidth = 1.5; g.stroke();
      ell(g, ex, y + 1 + h / 2, 2.4, h / 4); g.strokeStyle = 'rgba(90,50,20,0.6)'; g.lineWidth = 1; g.stroke();
    }
    for (let x = 6 + r() * 10; x < w - 6; x += 9 + r() * 12) leaf(g, x, y + 3, -1.6 + (r() - 0.5) * 1.6, r() < 0.5 ? '#4caf50' : '#7bd35f', 0.75 + r() * 0.5);
  },
  function pipes(g, w, r) {
    const y = FT + 1, h = FB - 4;
    if (w > 90) {
      const gx = 24 + r() * (w - 48);
      g.strokeStyle = '#3b1d0a'; g.lineWidth = 2; g.beginPath(); g.moveTo(gx, y + h); g.lineTo(gx, y + h + 6); g.stroke();
      circ(g, gx, y + h + 13, 7); g.fillStyle = '#f4ecd8'; g.fill(); g.strokeStyle = '#3b1d0a'; g.lineWidth = 2; g.stroke();
      const a = -2.4 + r() * 1.6;
      g.strokeStyle = '#c0392b'; g.lineWidth = 1.4; g.beginPath(); g.moveTo(gx, y + h + 13); g.lineTo(gx + Math.cos(a) * 5.5, y + h + 13 + Math.sin(a) * 5.5); g.stroke();
    }
    g.fillStyle = 'rgba(0,0,0,0.26)'; g.fillRect(4, y + 6, w - 6, h);
    const gr = g.createLinearGradient(0, y, 0, y + h);
    gr.addColorStop(0, '#ffe2b4'); gr.addColorStop(0.25, '#e59a52'); gr.addColorStop(0.7, '#a85a24'); gr.addColorStop(1, '#6b3312');
    g.fillStyle = gr; g.fillRect(2, y, w - 4, h);
    g.strokeStyle = '#3b1d0a'; g.lineWidth = 2; g.strokeRect(2, y, w - 4, h);
    const flange = x => {
      const fg = g.createLinearGradient(0, y - 3, 0, y + h + 3);
      fg.addColorStop(0, '#ffe9c8'); fg.addColorStop(0.5, '#c77936'); fg.addColorStop(1, '#6b3312');
      rrect(g, x - 4, y - 3, 8, h + 6, 2); g.fillStyle = fg; g.fill(); g.strokeStyle = '#3b1d0a'; g.lineWidth = 1.6; g.stroke();
      g.fillStyle = '#4a2a14'; circ(g, x, y, 1.1); g.fill(); circ(g, x, y + h, 1.1); g.fill();
    };
    flange(6); flange(w - 6);
    for (let x = 40 + r() * 30; x < w - 30; x += 50 + r() * 40) flange(x);
    g.fillStyle = 'rgba(255,255,255,0.4)'; g.fillRect(8, y + 2, w - 16, 1.5);
  },
  function cloud(g, w, r) {
    const y = FT, puffs = [];
    for (let x = 7; x < w - 5; x += 9 + r() * 6) puffs.push([x, y + 6 + r() * 3, 7 + r() * 6]);
    puffs.push([w - 7, y + 8, 7]);
    g.fillStyle = '#86a8e2';
    for (const p of puffs) { circ(g, p[0], p[1] + 1.6, p[2] + 1.8); g.fill(); }
    rrect(g, 2, y + 6, w - 4, 14, 7); g.fill();
    const gr = g.createLinearGradient(0, y - 6, 0, y + 20);
    gr.addColorStop(0, '#ffffff'); gr.addColorStop(0.6, '#eef5ff'); gr.addColorStop(1, '#b9cff5');
    g.fillStyle = gr;
    for (const p of puffs) { circ(g, p[0], p[1], p[2]); g.fill(); }
    rrect(g, 4, y + 6, w - 8, 12, 6); g.fill();
    g.fillStyle = 'rgba(255,255,255,0.9)';
    for (const p of puffs) { circ(g, p[0] - p[2] * 0.3, p[1] - p[2] * 0.35, p[2] * 0.35); g.fill(); }
  },
  function rainbow(g, w, r) {
    const y = FT, h = 18;
    const cols = ['#ff4d4d', '#ff9f1a', '#ffe14d', '#4cd964', '#3fa9ff', '#9b59ff'];
    g.fillStyle = 'rgba(40,0,80,0.2)'; rrect(g, 4, y + 6, w - 5, h, 9); g.fill();
    g.save(); rrect(g, 1, y, w - 2, h, 9); g.clip();
    cols.forEach((c, i) => { g.fillStyle = c; g.fillRect(0, y + i * 3, w, 3.2); });
    const gl = g.createLinearGradient(0, y, 0, y + h);
    gl.addColorStop(0, 'rgba(255,255,255,0.6)'); gl.addColorStop(0.35, 'rgba(255,255,255,0)'); gl.addColorStop(1, 'rgba(0,0,0,0.2)');
    g.fillStyle = gl; g.fillRect(0, y, w, h);
    g.restore();
    rrect(g, 1, y, w - 2, h, 9); g.strokeStyle = '#2d1f5c'; g.lineWidth = 2; g.stroke();
    for (let i = 0; i < w / 28; i++) sparkle(g, 6 + r() * (w - 12), y + h + 5 + r() * 16, 1.6 + r() * 2.2, 'rgba(255,255,255,0.95)');
  },
  function glass(g, w, r) {
    const y = FT, h = FB - 4;
    if (r() < 0.6) {
      const sx = 18 + r() * (w - 36);
      g.strokeStyle = 'rgba(255,255,255,0.6)'; g.lineWidth = 0.8; g.beginPath(); g.moveTo(sx, y + h); g.lineTo(sx, y + h + 10); g.stroke();
      starPath(g, sx, y + h + 15, 5, 5.5, 2.4, -Math.PI / 2); g.fillStyle = '#ffe45c'; g.fill(); g.strokeStyle = '#8a6d00'; g.lineWidth = 1; g.stroke();
    }
    rrect(g, 1, y, w - 2, h, 3); g.fillStyle = 'rgba(170,220,255,0.3)'; g.fill();
    g.save(); rrect(g, 1, y, w - 2, h, 3); g.clip();
    g.fillStyle = 'rgba(255,255,255,0.35)';
    for (let x = r() * 20; x < w + 20; x += 26 + r() * 20) { g.beginPath(); g.moveTo(x, y + h); g.lineTo(x + 4, y + h); g.lineTo(x + 14, y); g.lineTo(x + 10, y); g.closePath(); g.fill(); }
    for (let i = 0; i < w / 12; i++) { g.fillStyle = 'rgba(255,255,255,' + (0.5 + r() * 0.5).toFixed(2) + ')'; circ(g, r() * w, y + 3 + r() * (h - 6), 0.6 + r() * 0.8); g.fill(); }
    g.restore();
    g.strokeStyle = 'rgba(230,245,255,0.95)'; g.lineWidth = 1.6; rrect(g, 1, y, w - 2, h, 3); g.stroke();
    g.fillStyle = '#ffffff'; g.fillRect(4, y + 1, w - 8, 1.4);
    for (const ex of [1, w - 9]) {
      const fg = g.createLinearGradient(0, y, 0, y + h);
      fg.addColorStop(0, '#f4f7fb'); fg.addColorStop(1, '#8a94a8');
      rrect(g, ex, y - 1, 8, h + 2, 2); g.fillStyle = fg; g.fill(); g.strokeStyle = '#3c4458'; g.lineWidth = 1.4; g.stroke();
    }
  }
];

// ---------- asset builder (re-run when the canvas resolution changes) ----------
const Assets = (() => {
  const A = { scale: 0, bg: null, wall: null, wallR: null, vignette: null, clock: null, stars: [], glow: null, base: null, fcache: new Map(), tcache: new Map() };
  function mk(w, h, sc) {
    const s = sc || A.scale;
    const c = document.createElement('canvas');
    c.width = Math.max(1, Math.ceil(w * s));
    c.height = Math.max(1, Math.ceil(h * s));
    const g = c.getContext('2d');
    g.scale(c.width / w, c.height / h);
    return [c, g];
  }
  function buildBg() {
    const [c, g] = mk(512, 320, Math.min(A.scale, 2.2));
    const r = mulberry32(1234);
    g.fillStyle = '#5a5770'; g.fillRect(0, 0, 512, 320);
    for (let row = 0; row < 20; row++) {
      const y = row * 16, off = (row % 2) * 16;
      for (let col = -1; col < 17; col++) {
        const x = col * 32 + off;
        const l = Math.floor(168 + r() * 52), v = Math.floor(r() * 10) - 5;
        g.fillStyle = 'rgb(' + (l + v) + ',' + (l + v - 3) + ',' + Math.min(255, l + 12) + ')';
        g.fillRect(x + 1, y + 1, 30, 14);
        g.fillStyle = 'rgba(255,255,255,0.2)'; g.fillRect(x + 1, y + 1, 30, 2);
        g.fillStyle = 'rgba(0,0,0,0.18)'; g.fillRect(x + 1, y + 13, 30, 2);
        for (let k = 0; k < 4; k++) { g.fillStyle = 'rgba(0,0,0,' + (0.05 + r() * 0.08).toFixed(3) + ')'; g.fillRect(x + 2 + r() * 26, y + 3 + r() * 9, 2, 2); }
        if (r() < 0.05) crackLine(g, x + 4 + r() * 20, y + 2, r);
      }
    }
    A.bg = c;
  }
  function buildWall() {
    const [c, g] = mk(64, 256);
    const r = mulberry32(99);
    g.fillStyle = '#3f3c4d'; g.fillRect(0, 0, 64, 256);
    for (let row = 0; row < 8; row++) {
      const y = row * 32, split = row % 2 ? 24 : 40;
      for (const [bx, bw] of [[0, split], [split, 64 - split]]) {
        const l = Math.floor(150 + r() * 40);
        const gr = g.createLinearGradient(0, y, 0, y + 32);
        gr.addColorStop(0, 'rgb(' + (l + 22) + ',' + (l + 20) + ',' + (l + 28) + ')');
        gr.addColorStop(1, 'rgb(' + (l - 28) + ',' + (l - 30) + ',' + (l - 18) + ')');
        g.fillStyle = gr; rrect(g, bx + 1.5, y + 1.5, bw - 3, 29, 4); g.fill();
        g.strokeStyle = 'rgba(255,255,255,0.28)'; g.lineWidth = 1.5;
        g.beginPath(); g.moveTo(bx + 3, y + 28); g.lineTo(bx + 3, y + 3); g.lineTo(bx + bw - 3, y + 3); g.stroke();
        g.strokeStyle = 'rgba(0,0,0,0.32)';
        g.beginPath(); g.moveTo(bx + bw - 3, y + 3); g.lineTo(bx + bw - 3, y + 28); g.lineTo(bx + 3, y + 28); g.stroke();
        for (let k = 0; k < 5; k++) { g.fillStyle = 'rgba(0,0,0,' + (0.08 + r() * 0.1).toFixed(3) + ')'; circ(g, bx + 5 + r() * (bw - 10), y + 6 + r() * 20, 0.8 + r() * 1.4); g.fill(); }
      }
    }
    A.wall = c;
    const [c2, g2] = mk(64, 256);
    g2.translate(64, 0); g2.scale(-1, 1); g2.drawImage(c, 0, 0, 64, 256);
    A.wallR = c2;
  }
  function buildBase() {
    const [c, g] = mk(512, 120);
    const gr = g.createLinearGradient(0, 0, 0, 120);
    gr.addColorStop(0, '#3a3450'); gr.addColorStop(1, '#141122');
    g.fillStyle = gr; g.fillRect(0, 0, 512, 120);
    const r = mulberry32(7);
    for (let row = 0; row < 6; row++) for (let col = -1; col < 9; col++) {
      const x = col * 64 + (row % 2) * 32, y = row * 20;
      g.fillStyle = 'rgba(255,255,255,' + (0.04 + r() * 0.05).toFixed(3) + ')';
      rrect(g, x + 2, y + 2, 60, 16, 3); g.fill();
    }
    A.base = c;
  }
  function buildVignette() {
    const [c, g] = mk(W, 64, Math.min(A.scale, 2));
    const gr = g.createLinearGradient(0, 0, 0, 64);
    gr.addColorStop(0, 'rgba(0,0,0,0.34)'); gr.addColorStop(1, 'rgba(0,0,0,0)');
    g.fillStyle = gr; g.fillRect(0, 0, W, 64);
    A.vignette = c;
  }
  function buildClock() {
    const [c, g] = mk(72, 72);
    const cx = 36, cy = 40;
    g.lineWidth = 2; g.strokeStyle = OUTL;
    for (const s of [-1, 1]) {
      g.save(); g.translate(cx + s * 12, cy + 23); g.rotate(s * 0.5);
      g.fillStyle = '#6b5a3a'; g.fillRect(-2, -4, 4, 9); g.strokeRect(-2, -4, 4, 9);
      g.restore();
    }
    for (const s of [-1, 1]) {
      g.save(); g.translate(cx + s * 16, cy - 22); g.rotate(s * 0.55);
      const bg = g.createLinearGradient(0, -9, 0, 4); bg.addColorStop(0, '#fff3b0'); bg.addColorStop(1, '#d4a01c');
      g.beginPath(); g.arc(0, 0, 9, Math.PI, 0); g.lineTo(9, 3); g.lineTo(-9, 3); g.closePath();
      g.fillStyle = bg; g.fill(); g.stroke();
      g.restore();
    }
    g.fillStyle = '#d4a01c'; g.fillRect(cx - 2, cy - 30, 4, 6); g.strokeRect(cx - 2, cy - 30, 4, 6);
    const ring = g.createLinearGradient(0, cy - 26, 0, cy + 26);
    ring.addColorStop(0, '#ff7a6b'); ring.addColorStop(1, '#a8231a');
    circ(g, cx, cy, 26); g.fillStyle = ring; g.fill(); g.stroke();
    const face = g.createRadialGradient(cx - 5, cy - 6, 2, cx, cy, 21);
    face.addColorStop(0, '#fffdf2'); face.addColorStop(1, '#e8dfc2');
    circ(g, cx, cy, 20.5); g.fillStyle = face; g.fill(); g.lineWidth = 1.5; g.stroke();
    for (let i = 0; i < 12; i++) {
      const a = (i / 12) * TAU, r1 = i % 3 === 0 ? 13.5 : 16.5;
      g.lineWidth = i % 3 === 0 ? 2.4 : 1.2; g.strokeStyle = '#3a2f24';
      g.beginPath(); g.moveTo(cx + Math.cos(a) * r1, cy + Math.sin(a) * r1); g.lineTo(cx + Math.cos(a) * 18.5, cy + Math.sin(a) * 18.5); g.stroke();
    }
    g.fillStyle = 'rgba(255,255,255,0.55)'; ell(g, cx - 7, cy - 10, 7, 3.5, -0.5); g.fill();
    A.clock = c;
  }
  function buildStars() {
    A.stars = STAR_COLS.map(col => {
      const [c, g] = mk(24, 24);
      g.shadowColor = col; g.shadowBlur = 5 * A.scale;
      starPath(g, 12, 12, 5, 9, 4, -Math.PI / 2); g.fillStyle = col; g.fill();
      g.shadowBlur = 0;
      starPath(g, 12, 12.5, 5, 4.5, 2, -Math.PI / 2); g.fillStyle = 'rgba(255,255,255,0.85)'; g.fill();
      return c;
    });
    const [c, g] = mk(64, 64);
    const gr = g.createRadialGradient(32, 32, 0, 32, 32, 32);
    gr.addColorStop(0, 'rgba(255,200,120,0.55)'); gr.addColorStop(0.4, 'rgba(255,150,60,0.18)'); gr.addColorStop(1, 'rgba(255,120,40,0)');
    g.fillStyle = gr; g.fillRect(0, 0, 64, 64);
    A.glow = c;
  }
  // Zone-tinted copies of the brick backdrop and the side walls (cached, so no per-frame blending)
  A.tinted = function (kind, z) {
    const key = kind + z;
    let c = A.tcache.get(key);
    if (c) return c;
    const Z = ZONE_VIS[z];
    let g;
    if (kind === 'bg') { [c, g] = mk(512, 320, Math.min(A.scale, 2.2)); g.drawImage(A.bg, 0, 0, 512, 320); g.fillStyle = Z.tint; }
    else { [c, g] = mk(64, 256); g.drawImage(kind === 'wl' ? A.wall : A.wallR, 0, 0, 64, 256); g.fillStyle = Z.wall; }
    g.globalCompositeOperation = 'multiply';
    g.fillRect(0, 0, kind === 'bg' ? 512 : 64, kind === 'bg' ? 320 : 256);
    g.globalCompositeOperation = 'source-over';
    if (A.tcache.size > 12) A.tcache.delete(A.tcache.keys().next().value);
    A.tcache.set(key, c);
    return c;
  };
  A.build = function (scale) {
    scale = Math.max(0.5, Math.min(4, scale));
    if (Math.abs(scale - A.scale) < 0.01 && A.bg) return;
    A.scale = scale;
    A.fcache.clear();
    A.tcache.clear();
    buildBg(); buildWall(); buildBase(); buildVignette(); buildClock(); buildStars();
  };
  // A cached sprite for one floor (whole width, drawn procedurally)
  A.floor = function (f, style) {
    const key = style + '|' + f.w + '|' + f.n;
    let c = A.fcache.get(key);
    if (c) { A.fcache.delete(key); A.fcache.set(key, c); return c; }
    const [cv, g] = mk(f.w, FSH);
    const r = mulberry32(hash32(f.n * 7919 + style * 131 + f.w));
    FLOOR_PAINTERS[style](g, f.w, r);
    A.fcache.set(key, cv);
    if (A.fcache.size > 48) A.fcache.delete(A.fcache.keys().next().value);
    return cv;
  };
  return A;
})();
// ===================== characters (original designs, drawn with vectors) =====================
function eye(g, x, y, r, mode, look, pupil) {
  g.lineCap = 'round';
  if (mode === 'closed') { g.strokeStyle = OUTL; g.lineWidth = 1.4; g.beginPath(); g.moveTo(x - r, y); g.quadraticCurveTo(x, y + r * 0.6, x + r, y); g.stroke(); return; }
  if (mode === 'happy') { g.strokeStyle = OUTL; g.lineWidth = 1.5; g.beginPath(); g.moveTo(x - r, y + r * 0.35); g.quadraticCurveTo(x, y - r * 0.9, x + r, y + r * 0.35); g.stroke(); return; }
  if (mode === 'x') {
    g.strokeStyle = OUTL; g.lineWidth = 1.5; const q = r * 0.7;
    g.beginPath(); g.moveTo(x - q, y - q); g.lineTo(x + q, y + q); g.moveTo(x + q, y - q); g.lineTo(x - q, y + q); g.stroke(); return;
  }
  const rr = mode === 'wide' ? r * 1.2 : r;
  ell(g, x, y, rr * 0.86, rr); g.fillStyle = '#fff'; g.fill(); g.lineWidth = 1.2; g.strokeStyle = OUTL; g.stroke();
  const px = x + look * rr * 0.32, py = y + (mode === 'wide' ? 0 : rr * 0.12);
  circ(g, px, py, rr * (mode === 'wide' ? 0.36 : 0.52)); g.fillStyle = pupil || OUTL; g.fill();
  circ(g, px - rr * 0.16, py - rr * 0.22, rr * 0.17); g.fillStyle = '#fff'; g.fill();
}
function mouthShape(g, x, y, w, mode) {
  g.strokeStyle = OUTL; g.lineWidth = 1.3; g.lineCap = 'round';
  if (mode === 'o') { ell(g, x, y + 0.6, w * 0.26, w * 0.34); g.fillStyle = '#5a1d2a'; g.fill(); g.stroke(); }
  else if (mode === 'grin') {
    g.beginPath(); g.moveTo(x - w / 2, y - 0.6); g.quadraticCurveTo(x, y + w * 0.8, x + w / 2, y - 0.6); g.closePath();
    g.fillStyle = '#5a1d2a'; g.fill(); g.stroke();
  } else { g.beginPath(); g.moveTo(x - w / 2, y); g.quadraticCurveTo(x, y + w * 0.42, x + w / 2, y); g.stroke(); }
}
function limb(g, a, b, wdt, col) {
  g.lineCap = 'round';
  g.strokeStyle = OUTL; g.lineWidth = wdt + 2.4; g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(b[0], b[1]); g.stroke();
  g.strokeStyle = col; g.lineWidth = wdt; g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(b[0], b[1]); g.stroke();
}
function bentLimb(g, a, b, bend, wdt, col) {
  const dx = b[0] - a[0], dy = b[1] - a[1], len = Math.hypot(dx, dy) || 1;
  const kx = (a[0] + b[0]) / 2 - (dy / len) * bend, ky = (a[1] + b[1]) / 2 + (dx / len) * bend;
  g.lineCap = 'round'; g.lineJoin = 'round';
  for (const [c, lw] of [[OUTL, wdt + 2.4], [col, wdt]]) {
    g.strokeStyle = c; g.lineWidth = lw;
    g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(kx, ky); g.lineTo(b[0], b[1]); g.stroke();
  }
}
function flipper(g, sh, hand, col) {
  const dx = hand[0] - sh[0], dy = hand[1] - sh[1], len = Math.hypot(dx, dy);
  g.save(); g.translate(sh[0], sh[1]); g.rotate(Math.atan2(dy, dx));
  ell(g, len * 0.5, 0, len * 0.55 + 1.5, 3.4); g.fillStyle = col; g.fill(); g.strokeStyle = OUTL; g.lineWidth = 1.6; g.stroke();
  g.restore();
}
function springLeg(g, a, b, col) {
  const n = 7, dx = b[0] - a[0], dy = b[1] - a[1], len = Math.hypot(dx, dy) || 1, nx = -dy / len, ny = dx / len;
  const pts = [a];
  for (let i = 1; i < n; i++) { const t = i / n, s = (i % 2 ? 1 : -1) * 3.2; pts.push([a[0] + dx * t + nx * s, a[1] + dy * t + ny * s]); }
  pts.push(b);
  g.lineCap = 'round'; g.lineJoin = 'round';
  for (const [c, lw] of [[OUTL, 3.6], [col, 1.6]]) {
    g.strokeStyle = c; g.lineWidth = lw; g.beginPath(); g.moveTo(pts[0][0], pts[0][1]);
    for (let i = 1; i < pts.length; i++) g.lineTo(pts[i][0], pts[i][1]);
    g.stroke();
  }
}
const rainbowCol = t => 'hsl(' + Math.floor((t * 220) % 360) + ',95%,62%)';

function skeleton(ps) {
  const t = ps.t;
  const k = { fL: [-4.5, 0], fR: [4.5, 0], hL: [-8, -16], hR: [8, -16], lean: 0, sx: 1, sy: 1, bob: 0, eyes: 'open', mouth: 'smile', look: 1, sweat: false };
  switch (ps.state) {
    case 'idle': {
      const b = Math.sin(t * 3.2) * 0.7;
      k.bob = b; k.hL = [-8.5, -15.5 + b]; k.hR = [8.5, -15.5 + b];
      if (mod(t, 3.3) < 0.13) k.eyes = 'closed';
      break;
    }
    case 'bored': {
      k.look = 0;
      k.fR = [5, -Math.max(0, Math.sin(t * 9)) * 2.5];
      k.hL = [-7, -18]; k.hR = [6, -20];
      if (mod(t, 6) > 5) k.mouth = 'o';
      if (mod(t, 2.9) < 0.12) k.eyes = 'closed';
      break;
    }
    case 'run': {
      const s1 = Math.sin(ps.phase), c1 = Math.cos(ps.phase);
      k.fL = [c1 * 7.5 - 1, -Math.max(0, s1) * 5];
      k.fR = [-c1 * 7.5 + 1, -Math.max(0, -s1) * 5];
      k.bob = -Math.abs(s1) * 1.8;
      k.lean = Math.min(0.3, Math.abs(ps.vx) * 0.032);
      k.hL = [-c1 * 7, -17 + k.bob]; k.hR = [c1 * 7, -17 + k.bob];
      if (Math.abs(ps.vx) > 7) k.mouth = 'grin';
      break;
    }
    case 'skid':
      k.lean = -0.28; k.fL = [3, 0]; k.fR = [10, -1]; k.hL = [-11, -25]; k.hR = [-3, -29]; k.mouth = 'o'; k.eyes = 'wide';
      break;
    case 'jump':
      k.fL = [-4, -7]; k.fR = [5, -5]; k.hL = [-9, -38]; k.hR = [10, -39]; k.sy = 1.06; k.sx = 0.95; k.mouth = 'grin';
      break;
    case 'fall': {
      const w = Math.sin(t * 18) * 3;
      k.fL = [-5, 1]; k.fR = [4, 2.5]; k.hL = [-13, -31 + w]; k.hR = [12, -32 - w];
      if (ps.vy > 9) { k.eyes = 'wide'; k.mouth = 'o'; }
      break;
    }
    case 'spin':
      k.fL = [-3, -9]; k.fR = [4, -8]; k.hL = [-5, -21]; k.hR = [7, -19]; k.eyes = 'happy'; k.mouth = 'grin';
      break;
    case 'edge': {
      const e = ps.edgeLocal || 1, a = t * 14;
      k.lean = e * (0.3 + Math.sin(a) * 0.08);
      k.hL = [Math.cos(a) * 11, -26 + Math.sin(a) * 11];
      k.hR = [Math.cos(a + Math.PI) * 11, -26 + Math.sin(a + Math.PI) * 11];
      k.eyes = 'wide'; k.mouth = 'o'; k.sweat = true;
      break;
    }
    case 'dead': {
      const w = Math.sin(t * 20);
      k.hL = [-10, -38 + w * 4]; k.hR = [10, -38 - w * 4]; k.fL = [-6, -2 + w * 3]; k.fR = [6, -2 - w * 3];
      k.eyes = 'x'; k.mouth = 'o';
      break;
    }
    case 'cheer': {
      const w = Math.sin(t * 12) * 3;
      k.hL = [-10, -40 + w]; k.hR = [10, -40 - w]; k.mouth = 'grin'; k.eyes = 'happy';
      k.bob = -Math.abs(Math.sin(t * 6)) * 2;
      break;
    }
    default: break;
  }
  if (ps.land > 0) {
    const q = ps.land;
    k.sy *= 1 - 0.2 * q; k.sx *= 1 + 0.15 * q;
    k.fL = [k.fL[0] - 2 * q, k.fL[1]]; k.fR = [k.fR[0] + 2 * q, k.fR[1]];
  }
  return k;
}

const CHARS = [
  {
    name: 'PIP', trail: 0,
    desc: ['A penguin who never takes off his lucky scarf.', 'Uğurlu atkısını hiç çıkarmayan bir penguen.'],
    draw(g, k, ps) {
      const b = k.bob, body = '#23263f', belly = '#f6f7ff', orange = '#ffa51f', red = '#e8413c';
      const sp = clamp(Math.abs(ps.vx) * 0.9 + Math.max(0, -ps.vy) * 0.4 + 3, 3, 13), wv = Math.sin(ps.t * 13) * 2.2;
      g.beginPath();
      g.moveTo(-5, -25 + b);
      g.quadraticCurveTo(-7 - sp * 0.5, -25 + b + wv, -9 - sp, -21 + b - wv);
      g.lineTo(-8 - sp, -16.5 + b - wv);
      g.quadraticCurveTo(-5 - sp * 0.4, -20 + b + wv * 0.5, -2, -21.5 + b);
      g.closePath();
      g.fillStyle = red; g.fill(); g.strokeStyle = OUTL; g.lineWidth = 1.4; g.stroke();
      g.strokeStyle = '#ffd35c'; g.lineWidth = 1.2; g.beginPath(); g.moveTo(-6 - sp * 0.8, -22 + b - wv * 0.6); g.lineTo(-5.5 - sp * 0.8, -18 + b - wv * 0.6); g.stroke();
      flipper(g, [-6, -24 + b], k.hL, body);
      const foot = f => { ell(g, f[0] + 2, f[1] - 1.6, 5.2, 2.4); g.fillStyle = orange; g.fill(); g.strokeStyle = OUTL; g.lineWidth = 1.4; g.stroke(); };
      foot(k.fL);
      ell(g, 0, -20 + b, 12.5, 17.5); g.fillStyle = body; g.fill(); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
      ell(g, 3, -16.5 + b, 8.2, 12.5); g.fillStyle = belly; g.fill();
      g.fillStyle = 'rgba(255,255,255,0.18)'; ell(g, -5, -29 + b, 3, 5, 0.4); g.fill();
      foot(k.fR);
      const lk = k.look;
      eye(g, 2.5 + lk, -31.5 + b, 3.5, k.eyes, lk);
      eye(g, 9.2 + lk, -31.5 + b, 3.5, k.eyes, lk);
      g.fillStyle = 'rgba(255,120,150,0.45)'; ell(g, 12, -26.5 + b, 2.2, 1.3); g.fill();
      const open = k.mouth === 'o' ? 2.6 : k.mouth === 'grin' ? 1.6 : 0;
      g.lineWidth = 1.3; g.strokeStyle = OUTL;
      g.beginPath(); g.moveTo(9, -28.5 + b); g.quadraticCurveTo(16, -28.5 + b - open * 0.3, 18.5, -26.5 + b - open * 0.5); g.lineTo(10, -26 + b); g.closePath();
      g.fillStyle = orange; g.fill(); g.stroke();
      if (open) { g.beginPath(); g.moveTo(10, -25.6 + b); g.lineTo(16, -25 + b + open); g.lineTo(10, -23.8 + b + open * 0.4); g.closePath(); g.fillStyle = '#e8870e'; g.fill(); g.stroke(); }
      rrect(g, -11, -25.5 + b, 23, 5.5, 2.6); g.fillStyle = red; g.fill(); g.lineWidth = 1.4; g.stroke();
      g.strokeStyle = '#ffd35c'; g.lineWidth = 1.2;
      for (const sx of [-6, 0, 6]) { g.beginPath(); g.moveTo(sx, -25 + b); g.lineTo(sx + 1, -20.5 + b); g.stroke(); }
      flipper(g, [5, -23 + b], k.hR, body);
    }
  },
  {
    name: 'COG', trail: 2,
    desc: ['A spring-legged robot built for one job: going up.', 'Tek iş için yapılmış yaylı bacaklı robot: yukarı çıkmak.'],
    draw(g, k, ps) {
      const b = k.bob, glow = ps.combo ? rainbowCol(ps.t) : '#7ff3ff';
      limb(g, [-6, -24 + b], k.hL, 2.4, '#a9bccf');
      circ(g, k.hL[0], k.hL[1], 2.6); g.fillStyle = '#5a6f88'; g.fill(); g.lineWidth = 1.3; g.strokeStyle = OUTL; g.stroke();
      springLeg(g, [-4, -12 + b], [k.fL[0], k.fL[1] - 2], '#c7d3df');
      const foot = f => { rrect(g, f[0] - 4.5, f[1] - 3.2, 10, 3.6, 1.6); g.fillStyle = '#2d3a4d'; g.fill(); g.lineWidth = 1.3; g.strokeStyle = OUTL; g.stroke(); };
      foot(k.fL);
      const bg = g.createLinearGradient(0, -29 + b, 0, -11 + b);
      bg.addColorStop(0, '#a6c1dc'); bg.addColorStop(1, '#5a7797');
      rrect(g, -10, -29 + b, 20, 18, 5); g.fillStyle = bg; g.fill(); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
      g.fillStyle = 'rgba(255,255,255,0.3)'; g.fillRect(-7, -27 + b, 12, 1.6);
      g.fillStyle = '#2d3a4d'; for (const yy of [-16, -13.5]) g.fillRect(-7, yy + b, 7, 1.2);
      circ(g, 4, -20 + b, 3.3); g.fillStyle = glow; g.fill(); g.lineWidth = 1.2; g.stroke();
      springLeg(g, [4, -12 + b], [k.fR[0], k.fR[1] - 2], '#c7d3df');
      foot(k.fR);
      g.strokeStyle = OUTL; g.lineWidth = 3.4; g.beginPath(); g.moveTo(0, -30 + b); g.lineTo(0, -32 + b); g.stroke();
      const hg = g.createLinearGradient(0, -45 + b, 0, -31 + b);
      hg.addColorStop(0, '#c0d6ea'); hg.addColorStop(1, '#6d8cad');
      rrect(g, -9, -45 + b, 20, 14, 5); g.fillStyle = hg; g.fill(); g.lineWidth = 2; g.stroke();
      rrect(g, -4, -42 + b, 14, 8, 3); g.fillStyle = '#16202e'; g.fill(); g.lineWidth = 1.2; g.stroke();
      g.save(); g.shadowColor = glow; g.shadowBlur = 4 * Assets.scale;
      g.fillStyle = glow; g.strokeStyle = glow; g.lineWidth = 1.5; g.lineCap = 'round';
      for (const ex of [1, 6.5]) {
        const x = ex + k.look * 1.2, y = -38 + b;
        if (k.eyes === 'closed' || k.eyes === 'happy') { g.beginPath(); g.moveTo(x - 1.8, y + 0.8); g.lineTo(x, y - 0.9); g.lineTo(x + 1.8, y + 0.8); g.stroke(); }
        else if (k.eyes === 'x') { g.beginPath(); g.moveTo(x - 1.5, y - 1.5); g.lineTo(x + 1.5, y + 1.5); g.moveTo(x + 1.5, y - 1.5); g.lineTo(x - 1.5, y + 1.5); g.stroke(); }
        else { ell(g, x, y, k.eyes === 'wide' ? 1.9 : 1.4, k.eyes === 'wide' ? 2.4 : 1.9); g.fill(); }
      }
      g.restore();
      g.strokeStyle = OUTL; g.lineWidth = 1.6; g.beginPath(); g.moveTo(-2, -45 + b); g.lineTo(-3.5, -50.5 + b); g.stroke();
      circ(g, -3.8, -51.8 + b, 2.3); g.fillStyle = mod(ps.t, 1.2) < 0.6 ? '#ff5a5a' : '#8a1f1f'; g.fill(); g.lineWidth = 1.2; g.stroke();
      if (k.mouth === 'o' || k.mouth === 'grin') { g.fillStyle = glow; g.fillRect(2.5, -35.4 + b, 3.5, 0.9); }
      limb(g, [6, -24 + b], k.hR, 2.4, '#a9bccf');
      circ(g, k.hR[0], k.hR[1], 2.6); g.fillStyle = '#5a6f88'; g.fill(); g.lineWidth = 1.3; g.strokeStyle = OUTL; g.stroke();
    }
  },
  {
    name: 'HOPS', trail: 3,
    desc: ['A tree frog who wears a leaf as a hat.', 'Şapka yerine yaprak takan bir ağaç kurbağası.'],
    draw(g, k, ps) {
      const b = k.bob, green = '#4cc75a', dk = '#2e8a3c', belly = '#e4f8b0';
      limb(g, [-6, -22 + b], k.hL, 2.4, green);
      circ(g, k.hL[0], k.hL[1], 2); g.fillStyle = green; g.fill(); g.lineWidth = 1.2; g.strokeStyle = OUTL; g.stroke();
      const foot = f => { ell(g, f[0] + 1.8, f[1] - 1.3, 5.5, 2); g.fillStyle = dk; g.fill(); g.lineWidth = 1.3; g.strokeStyle = OUTL; g.stroke(); };
      bentLimb(g, [-3, -11 + b], [k.fL[0], k.fL[1] - 1.5], -4, 3.2, green); foot(k.fL);
      ell(g, 0, -17 + b, 11, 12); g.fillStyle = green; g.fill(); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
      ell(g, 3, -15 + b, 7, 8.5); g.fillStyle = belly; g.fill();
      g.fillStyle = dk; circ(g, -6, -19 + b, 1.6); g.fill(); circ(g, -4, -12 + b, 1.2); g.fill();
      bentLimb(g, [3, -11 + b], [k.fR[0], k.fR[1] - 1.5], -4, 3.2, green); foot(k.fR);
      ell(g, 2.5, -28.5 + b, 12.5, 8.5); g.fillStyle = green; g.fill(); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
      for (const ex of [-2.5, 8]) { circ(g, ex, -35.5 + b, 5.2); g.fillStyle = green; g.fill(); g.lineWidth = 1.8; g.stroke(); }
      g.fillStyle = green; g.fillRect(-4, -35 + b, 13, 6);
      eye(g, -2.5 + k.look * 0.6, -36 + b, 3.3, k.eyes, k.look);
      eye(g, 8 + k.look * 0.6, -36.5 + b, 3.3, k.eyes, k.look);
      if (k.mouth === 'o' || k.mouth === 'grin') mouthShape(g, 8, -26.5 + b, 9, k.mouth);
      else { g.strokeStyle = OUTL; g.lineWidth = 1.4; g.beginPath(); g.moveTo(-3, -27 + b); g.quadraticCurveTo(6, -22.5 + b, 14, -27.5 + b); g.stroke(); }
      g.fillStyle = 'rgba(255,120,150,0.45)'; ell(g, 12, -29 + b, 2, 1.2); g.fill();
      g.save(); g.translate(2.5, -41 + b); g.rotate(-0.25 + Math.sin(ps.t * 3) * 0.05);
      g.beginPath(); g.moveTo(-8, 1); g.quadraticCurveTo(0, -8, 9, 0); g.quadraticCurveTo(0, 5, -8, 1); g.closePath();
      g.fillStyle = '#8fd14f'; g.fill(); g.lineWidth = 1.4; g.strokeStyle = OUTL; g.stroke();
      g.strokeStyle = '#4f8f2a'; g.lineWidth = 1; g.beginPath(); g.moveTo(-6, 0.6); g.lineTo(7, -0.3); g.stroke();
      g.strokeStyle = OUTL; g.lineWidth = 1.4; g.beginPath(); g.moveTo(9, 0); g.lineTo(11.5, -2); g.stroke();
      g.restore();
      limb(g, [6, -21 + b], k.hR, 2.4, green);
      circ(g, k.hR[0], k.hR[1], 2); g.fillStyle = green; g.fill(); g.lineWidth = 1.2; g.strokeStyle = OUTL; g.stroke();
    }
  },
  {
    name: 'MISO', trail: 1,
    desc: ['A tabby cat in fast sneakers. Always lands on her feet.', 'Hızlı spor ayakkabılı tekir kedi. Hep dört ayak üstüne düşer.'],
    draw(g, k, ps) {
      const b = k.bob, fur = '#ff9f43', stripe = '#d06a22', cream = '#fff1dc';
      const sw = Math.sin(ps.t * 4) * 4 - Math.min(6, Math.abs(ps.vx) * 0.7);
      g.lineCap = 'round';
      for (const [c, lw] of [[OUTL, 6], [fur, 3.6]]) {
        g.strokeStyle = c; g.lineWidth = lw; g.beginPath(); g.moveTo(-6, -13 + b);
        g.bezierCurveTo(-16, -13 + b, -15 + sw, -26 + b, -10 + sw, -31 + b); g.stroke();
      }
      circ(g, -10 + sw, -31 + b, 2.4); g.fillStyle = cream; g.fill(); g.lineWidth = 1.3; g.strokeStyle = OUTL; g.stroke();
      limb(g, [-5, -23 + b], k.hL, 3, fur);
      circ(g, k.hL[0], k.hL[1], 2.3); g.fillStyle = cream; g.fill(); g.lineWidth = 1.2; g.strokeStyle = OUTL; g.stroke();
      const shoe = f => {
        rrect(g, f[0] - 4, f[1] - 4.2, 10, 4.6, 2.2); g.fillStyle = '#3b82f6'; g.fill(); g.lineWidth = 1.3; g.strokeStyle = OUTL; g.stroke();
        g.fillStyle = '#ffffff'; g.fillRect(f[0] - 3.5, f[1] - 1.4, 9, 1.3);
      };
      limb(g, [-3, -12 + b], [k.fL[0], k.fL[1] - 3], 3.4, fur); shoe(k.fL);
      ell(g, 0, -18 + b, 9.5, 11.5); g.fillStyle = fur; g.fill(); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
      ell(g, 3, -16 + b, 5.5, 8); g.fillStyle = cream; g.fill();
      g.strokeStyle = stripe; g.lineWidth = 1.6;
      for (const yy of [-24, -19, -14]) { g.beginPath(); g.moveTo(-9, yy + b); g.quadraticCurveTo(-5, yy + 1.5 + b, -3, yy + b); g.stroke(); }
      limb(g, [3, -12 + b], [k.fR[0], k.fR[1] - 3], 3.4, fur); shoe(k.fR);
      for (const [ex, ang] of [[-4.5, -0.35], [7.5, 0.3]]) {
        g.save(); g.translate(ex, -40 + b); g.rotate(ang);
        g.beginPath(); g.moveTo(-4.5, 3); g.lineTo(0, -6); g.lineTo(4.5, 3); g.closePath(); g.fillStyle = fur; g.fill(); g.lineWidth = 1.6; g.strokeStyle = OUTL; g.stroke();
        g.beginPath(); g.moveTo(-2.2, 2); g.lineTo(0, -3); g.lineTo(2.2, 2); g.closePath(); g.fillStyle = '#ffb3c1'; g.fill();
        g.restore();
      }
      circ(g, 2, -32 + b, 10.5); g.fillStyle = fur; g.fill(); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
      g.strokeStyle = stripe; g.lineWidth = 1.5;
      for (const sx of [-2, 1.5, 5]) { g.beginPath(); g.moveTo(sx, -42 + b); g.lineTo(sx + 0.5, -38.5 + b); g.stroke(); }
      ell(g, 7.5, -28.5 + b, 5.2, 3.8); g.fillStyle = cream; g.fill();
      eye(g, 1.5 + k.look, -33 + b, 3.2, k.eyes, k.look, '#1d5c1d');
      eye(g, 8.5 + k.look, -33 + b, 3.2, k.eyes, k.look, '#1d5c1d');
      g.fillStyle = '#ff7a9a'; g.beginPath(); g.moveTo(9.5, -30 + b); g.lineTo(12, -30 + b); g.lineTo(10.8, -28.6 + b); g.closePath(); g.fill();
      if (k.mouth === 'o' || k.mouth === 'grin') mouthShape(g, 10.5, -26.5 + b, 5, k.mouth);
      else { g.strokeStyle = OUTL; g.lineWidth = 1.2; g.beginPath(); g.moveTo(8.5, -27 + b); g.quadraticCurveTo(10, -25.5 + b, 10.8, -27.4 + b); g.quadraticCurveTo(11.6, -25.5 + b, 13, -27 + b); g.stroke(); }
      g.strokeStyle = 'rgba(29,22,49,0.6)'; g.lineWidth = 0.8;
      for (const dy of [-1, 1]) { g.beginPath(); g.moveTo(12, -28.5 + b + dy); g.lineTo(17, -29 + b + dy * 2); g.stroke(); }
      limb(g, [5, -22 + b], k.hR, 3, fur);
      circ(g, k.hR[0], k.hR[1], 2.3); g.fillStyle = cream; g.fill(); g.lineWidth = 1.2; g.strokeStyle = OUTL; g.stroke();
    }
  }
];

// ps: {x, y, face, state, t, phase, vx, vy, land, spinA, edgeLocal, combo, scale}
function drawChar(g, id, ps) {
  const ch = CHARS[id] || CHARS[0];
  const k = skeleton(ps);
  g.save();
  g.translate(ps.x, ps.y);
  if (ps.scale && ps.scale !== 1) g.scale(ps.scale, ps.scale);
  if (ps.spinA) { g.translate(0, -21); g.rotate(ps.spinA); g.translate(0, 21); }
  g.scale((ps.face || 1) * k.sx, k.sy);
  if (k.lean) g.rotate(k.lean);
  g.lineJoin = 'round'; g.lineCap = 'round';
  ch.draw(g, k, ps);
  if (k.sweat) {
    g.beginPath(); g.moveTo(-9, -44); g.quadraticCurveTo(-12, -39, -9, -37.5); g.quadraticCurveTo(-6, -39, -9, -44);
    g.fillStyle = '#8fd8ff'; g.fill(); g.lineWidth = 1; g.strokeStyle = OUTL; g.stroke();
  }
  g.restore();
}
// ===================== world rendering, effects, HUD =====================
const View = { shake: 0, flash: 0, flashCol: '#ffffff', ringT: 0, comboPulse: 0, cheerTick: -999, shownScore: 0, clockParts: 0 };
const TIER_GRAD = [
  ['#eaffd9', '#46c932'], ['#ffe3f5', '#ff3fa9'], ['#e2fbff', '#1fb0ef'], ['#fff1d9', '#ff8414'], ['#fffbd6', '#ffbf00'],
  ['#ffe3e3', '#ff3434'], ['#f0e4ff', '#8a45ff'], ['#dcfff4', '#10c496'], ['#fff3c4', '#ff7300'], ['#ffffff', '#ffffff']
];

// ---------- particles ----------
const FX = {
  parts: [],
  add(p) {
    if (this.parts.length > 500) this.parts.shift();
    p.age = 0; p.rot = p.rot || 0;
    this.parts.push(p);
  },
  clear() { this.parts.length = 0; },
  update(dt) {
    const ps = this.parts;
    for (let i = ps.length - 1; i >= 0; i--) {
      const p = ps[i];
      p.age += dt;
      if (p.age >= p.life || (p.screen && (p.y > H + 40 || p.y < -90))) { ps.splice(i, 1); continue; }
      if (p.drag) { const d = Math.pow(p.drag, dt * 60); p.vx *= d; p.vy *= d; }
      p.vy += (p.grav || 0) * dt;
      p.x += p.vx * dt; p.y += p.vy * dt;
      if (p.vr) p.rot += p.vr * dt;
      if (p.sway) p.x += Math.sin(p.age * p.sway + (p.ph || 0)) * (p.swayA || 10) * dt;
    }
  },
  draw(g, camY, layer) {
    for (const p of this.parts) {
      if (p.layer !== layer) continue;
      const k = p.age / p.life;
      const x = p.x, y = p.screen ? p.y : p.y - camY;
      if (y < -60 || y > H + 60) continue;
      let a = p.fade === false ? 1 : 1 - k;
      if (p.fadeIn) a *= clamp(p.age / p.fadeIn, 0, 1);
      g.globalAlpha = clamp(a * (p.alpha || 1), 0, 1);
      switch (p.t) {
        case 'star': {
          const s = p.s * (p.grow ? 1 + k * p.grow : 1 - k * 0.4);
          g.save(); g.translate(x, y); g.rotate(p.rot); g.drawImage(Assets.stars[p.c], -s / 2, -s / 2, s, s); g.restore();
          break;
        }
        case 'dust': circ(g, x, y, p.s * (1 + k * 1.2)); g.fillStyle = p.col || 'rgba(235,230,255,0.8)'; g.fill(); break;
        case 'spark': {
          const len = Math.hypot(p.vx, p.vy) * 0.03 + 2;
          const ang = Math.atan2(p.vy, p.vx);
          g.strokeStyle = p.col || '#ffe9a8'; g.lineWidth = p.s || 2; g.lineCap = 'round';
          g.beginPath(); g.moveTo(x, y); g.lineTo(x - Math.cos(ang) * len, y - Math.sin(ang) * len); g.stroke();
          break;
        }
        case 'ring': circ(g, x, y, p.s + k * p.grow); g.strokeStyle = p.col || '#fff'; g.lineWidth = 3 * (1 - k) + 0.5; g.stroke(); break;
        case 'snow': circ(g, x, y, p.s); g.fillStyle = '#ffffff'; g.fill(); break;
        case 'leaf': leaf(g, x, y, p.rot, p.col, p.s); break;
        case 'conf': g.save(); g.translate(x, y); g.rotate(p.rot); g.fillStyle = p.col; g.fillRect(-p.s, -p.s * 0.35, p.s * 2, p.s * 0.7); g.restore(); break;
        case 'glow': {
          const s = p.s * (0.8 + Math.sin(p.age * 6 + (p.ph || 0)) * 0.2);
          g.globalCompositeOperation = 'lighter';
          circ(g, x, y, s * 2.4); g.fillStyle = p.col2 || 'rgba(255,240,120,0.18)'; g.fill();
          circ(g, x, y, s); g.fillStyle = p.col || '#fff7a8'; g.fill();
          g.globalCompositeOperation = 'source-over';
          break;
        }
        case 'steam': circ(g, x, y, p.s * (1 + k * 2)); g.fillStyle = 'rgba(240,240,250,0.35)'; g.fill(); break;
        case 'feather': g.save(); g.translate(x, y); g.rotate(p.rot); ell(g, 0, 0, p.s, p.s * 0.35); g.fillStyle = '#ffffff'; g.fill(); g.strokeStyle = 'rgba(120,140,190,0.6)'; g.lineWidth = 0.6; g.stroke(); g.restore(); break;
        case 'twinkle': sparkle(g, x, y, p.s * Math.sin(k * Math.PI), p.col || '#ffffff'); break;
        case 'shoot': {
          g.strokeStyle = '#fffbe0'; g.lineWidth = 1.6; g.lineCap = 'round';
          g.beginPath(); g.moveTo(x, y); g.lineTo(x - p.vx * 0.08, y - p.vy * 0.08); g.stroke();
          break;
        }
        case 'gear': {
          g.save(); g.translate(x, y); g.rotate(p.rot);
          starPath(g, 0, 0, 8, p.s, p.s * 0.72, 0); g.fillStyle = '#d4a01c'; g.fill(); g.strokeStyle = OUTL; g.lineWidth = 1.2; g.stroke();
          circ(g, 0, 0, p.s * 0.3); g.fillStyle = OUTL; g.fill();
          g.restore();
          break;
        }
        default: break;
      }
    }
    g.globalAlpha = 1;
  }
};
function burst(x, y, n, o) {
  o = o || {};
  for (let i = 0; i < n; i++) {
    const a = o.ang !== undefined ? o.ang + rand(-o.spread, o.spread) : rand(TAU);
    const sp = rand(o.min || 60, o.max || 260);
    FX.add({
      t: o.t || 'star', x, y, vx: Math.cos(a) * sp, vy: Math.sin(a) * sp, life: rand(o.lifeMin || 0.5, o.life || 1.1),
      s: rand(o.sMin || 8, o.s || 16), c: randi(0, STAR_COLS.length - 1), col: o.col, rot: rand(TAU), vr: rand(-8, 8),
      grav: o.grav === undefined ? 300 : o.grav, drag: o.drag || 0.95, layer: o.layer || 1, screen: !!o.screen, grow: o.grow
    });
  }
}
function dust(x, y, n, spread, up) {
  for (let i = 0; i < n; i++) {
    FX.add({ t: 'dust', x: x + rand(-spread, spread), y: y - rand(0, 3), vx: rand(-60, 60), vy: -rand(10, up || 50), life: rand(0.3, 0.55), s: rand(2, 4.5), grav: 40, drag: 0.9, layer: 1 });
  }
}

// ---------- popups ----------
const Pops = {
  list: [], toasts: [],
  add(p) {
    p.age = 0;
    if (p.t === 'toast') { this.toasts.push(p); return; }
    if (p.t === 'reward' || p.t === 'hurry' || p.t === 'banner' || p.t === 'gameover') this.list = this.list.filter(q => q.t !== p.t);
    this.list.push(p);
  },
  clear() { this.list.length = 0; },
  update(dt) { for (let i = this.list.length - 1; i >= 0; i--) { const p = this.list[i]; p.age += dt; if (p.age > p.dur) this.list.splice(i, 1); } },
  updateToasts(dt) {
    const q = this.toasts[0];
    if (!q) return;
    q.age += dt * (this.toasts.length > 3 ? 1.8 : 1);
    if (q.age > q.dur) this.toasts.shift();
  },
  draw(g, time) {
    for (const p of this.list) {
      if (p.t === 'reward') drawReward(g, p, time);
      else if (p.t === 'hurry') drawHurry(g, p);
      else if (p.t === 'banner') drawBanner(g, p);
      else if (p.t === 'gameover') drawGameOverText(g, p);
    }
  },
  drawToasts(g, y0) { if (this.toasts.length) drawToast(g, this.toasts[0], y0, this.toasts.length - 1); }
};
function drawReward(g, p, time) {
  const t = p.age, d = p.dur;
  const tin = clamp(t / 0.35, 0, 1), tout = clamp((t - (d - 0.35)) / 0.35, 0, 1);
  const sc = Math.max(0.01, ease.outBack(tin) * (1 - 0.25 * tout));
  const alpha = 1 - tout, cx = W / 2, cy = 196 - tout * 36;
  const grd = TIER_GRAD[clamp(p.tier, 0, 9)];
  g.save();
  g.globalAlpha = alpha * 0.28; g.translate(cx, cy); g.rotate(t * 0.7);
  g.fillStyle = grd[1];
  for (let i = 0; i < 14; i++) { g.rotate(TAU / 14); g.beginPath(); g.moveTo(0, 0); g.lineTo(-16, -165 * sc); g.lineTo(16, -165 * sc); g.closePath(); g.fill(); }
  g.restore();
  g.save();
  g.globalAlpha = alpha; g.translate(cx, cy); g.scale(sc, sc); g.rotate(Math.sin(t * 6) * 0.035);
  const size = p.tier >= 7 ? 68 : 62;
  let fill;
  if (p.tier >= 9) {
    fill = g.createLinearGradient(-160, 0, 160, 0);
    for (let i = 0; i <= 6; i++) fill.addColorStop(i / 6, 'hsl(' + Math.floor((i * 60 + time * 240) % 360) + ',95%,62%)');
  } else {
    fill = g.createLinearGradient(0, -size / 2, 0, size / 2);
    fill.addColorStop(0, grd[0]); fill.addColorStop(0.55, grd[1]); fill.addColorStop(1, grd[1]);
  }
  const fs = fitSize(g, p.word, size, 540);
  text(g, p.word, 3, 5, { size: fs, fill: 'rgba(0,0,0,0.35)' });
  text(g, p.word, 0, 0, { size: fs, fill, stroke: '#150b27', lw: 11 });
  text(g, p.floors + ' ' + T('floorsWord'), 0, 48, { size: 26, fill: '#ffffff', stroke: '#150b27', lw: 7 });
  text(g, '+' + fmt(p.pts), 0, 77, { size: 20, fill: '#ffe45c', stroke: '#150b27', lw: 6 });
  g.restore();
}
function drawHurry(g, p) {
  const t = p.age, d = p.dur;
  let x;
  if (t < 0.4) x = lerp(W + 220, W / 2, ease.outBack(t / 0.4));
  else if (t > d - 0.35) x = lerp(W / 2, -240, ease.inCubic((t - (d - 0.35)) / 0.35));
  else x = W / 2;
  g.save();
  g.translate(x, 128);
  g.rotate(-0.06 + Math.sin(t * 22) * (t < 1.1 ? 0.04 : 0));
  const fill = g.createLinearGradient(0, -30, 0, 30);
  fill.addColorStop(0, '#fff2b0'); fill.addColorStop(0.5, '#ff8a1a'); fill.addColorStop(1, '#e8261c');
  text(g, 'HURRY UP!', 3, 5, { size: 60, fill: 'rgba(0,0,0,0.35)' });
  text(g, 'HURRY UP!', 0, 0, { size: 60, fill, stroke: '#1d0b12', lw: 12 });
  if (p.broken) text(g, T('maxLevel'), 0, 46, { size: 20, font: UIF, weight: 800, fill: '#ffd24a', stroke: '#1d0b12', lw: 5 });
  g.restore();
}
function drawBanner(g, p) {
  const t = p.age, d = p.dur;
  const a = clamp(t / 0.3, 0, 1) * (1 - clamp((t - (d - 0.5)) / 0.5, 0, 1));
  g.save(); g.globalAlpha = a;
  const y = 86 + (1 - ease.outCubic(clamp(t / 0.4, 0, 1))) * -20;
  text(g, p.sub, W / 2, y - 22, { size: 15, font: UIF, weight: 800, fill: '#ffffff', stroke: OUTL, lw: 4 });
  text(g, p.text, W / 2, y + 4, { size: 34, fill: p.col || '#bfe9ff', stroke: OUTL, lw: 8 });
  g.restore();
}
function drawGameOverText(g, p) {
  const t = p.age;
  const y = lerp(-60, 170, ease.outElastic(clamp(t / 1.1, 0, 1)));
  const fill = g.createLinearGradient(0, y - 34, 0, y + 34);
  fill.addColorStop(0, '#ffd0d0'); fill.addColorStop(0.5, '#ff4a4a'); fill.addColorStop(1, '#a3122a');
  text(g, 'GAME OVER', W / 2 + 3, y + 5, { size: 72, fill: 'rgba(0,0,0,0.4)' });
  text(g, 'GAME OVER', W / 2, y, { size: 72, fill, stroke: '#1a0710', lw: 13 });
}
function drawTrophyIcon(g, x, y, s, got) {
  g.save(); g.translate(x, y); g.scale(s, s);
  const gold = got ? '#ffd24a' : '#6f6a8c', dark = got ? '#b8860b' : '#4a4666';
  g.lineWidth = 1.6; g.strokeStyle = OUTL;
  g.beginPath(); g.moveTo(-8, -9); g.lineTo(8, -9); g.quadraticCurveTo(8, 3, 0, 4); g.quadraticCurveTo(-8, 3, -8, -9); g.closePath();
  g.fillStyle = gold; g.fill(); g.stroke();
  g.beginPath(); g.arc(-8, -5, 4, Math.PI * 0.5, Math.PI * 1.5); g.stroke();
  g.beginPath(); g.arc(8, -5, 4, -Math.PI * 0.5, Math.PI * 0.5); g.stroke();
  g.fillStyle = dark; g.fillRect(-1.5, 4, 3, 4); g.strokeRect(-1.5, 4, 3, 4);
  rrect(g, -6, 8, 12, 3.5, 1.2); g.fillStyle = gold; g.fill(); g.stroke();
  if (got) { g.fillStyle = 'rgba(255,255,255,0.6)'; g.fillRect(-5, -7.5, 2, 7); }
  g.restore();
}
function drawToast(g, p, y0, more) {
  const t = p.age, d = p.dur;
  const k = t < 0.35 ? ease.outBack(t / 0.35) : t > d - 0.3 ? 1 - ease.inCubic((t - (d - 0.3)) / 0.3) : 1;
  const w = 300, h = 46, x = W / 2 - w / 2, y = lerp(y0 - 70, y0, k);
  g.save();
  rrect(g, x, y, w, h, 12); g.fillStyle = 'rgba(20,14,42,0.95)'; g.fill(); g.lineWidth = 2; g.strokeStyle = '#ffd24a'; g.stroke();
  drawTrophyIcon(g, x + 26, y + 23, 1.25, true);
  text(g, T('unlocked'), x + 50, y + 15, { size: 12, font: UIF, weight: 800, fill: '#ffd24a', align: 'left' });
  const a = ACH.find(q => q.id === p.id), name = a ? TT(a.n) : '';
  text(g, name, x + 50, y + 32, { size: fitSize(g, name, 19, w - (more ? 100 : 62)), fill: '#ffffff', align: 'left' });
  if (more) {
    rrect(g, x + w - 44, y + 12, 34, 22, 11); g.fillStyle = '#ffd24a'; g.fill();
    text(g, '+' + more, x + w - 27, y + 24, { size: 13, fill: '#2a1d04' });
  }
  g.restore();
}

// ---------- backdrop ----------
function zoneBlend(camY) {
  const cf = -(camY + H / 2) / FLOOR_H;
  const z0 = clamp(Math.floor(cf / 100), 0, 10);
  const z1 = Math.min(10, z0 + 1);
  const f = z0 >= 10 ? 0 : clamp((cf - z0 * 100 - 88) / 12, 0, 1);
  return { z0, z1, f, cf };
}
function archPath(g, x, y, w, h) {
  g.beginPath(); g.moveTo(x, y + h); g.lineTo(x, y + w / 2); g.arc(x + w / 2, y + w / 2, w / 2, Math.PI, 0); g.lineTo(x + w, y + h); g.closePath();
}
function flamePath(g, x, y, w, h) {
  g.beginPath(); g.moveTo(x - w, y); g.quadraticCurveTo(x - w, y - h * 0.55, x, y - h); g.quadraticCurveTo(x + w, y - h * 0.55, x + w, y); g.quadraticCurveTo(x, y + w * 0.7, x - w, y); g.closePath();
}
function drawBgFeatures(g, camY, t, zb) {
  const P = 0.5, SP = 150, top = camY * P;
  const k0 = Math.floor(-(top + H + 90) / SP), k1 = Math.ceil(-(top - 90) / SP);
  const Z0 = ZONE_VIS[zb.z0], Z1 = ZONE_VIS[zb.z1];
  for (let k = k0; k <= k1; k++) {
    const h = hash32(Math.imul(k, 0x27d4eb2d) + 17);
    const type = h % 8, y = -k * SP - top;
    const x = TL + 52 + ((h >>> 8) % 400);
    if (type <= 1) {
      g.fillStyle = 'rgba(20,16,36,0.55)'; archPath(g, x - 25, y - 36, 50, 72); g.fill();
      g.save(); archPath(g, x - 19, y - 30, 38, 60); g.clip();
      const gr = g.createLinearGradient(0, y - 30, 0, y + 30);
      gr.addColorStop(0, mixHex(Z0.sky[0], Z1.sky[0], zb.f)); gr.addColorStop(1, mixHex(Z0.sky[1], Z1.sky[1], zb.f));
      g.fillStyle = gr; g.fillRect(x - 20, y - 31, 40, 62);
      g.fillStyle = 'rgba(255,255,255,0.75)';
      const cx = x - 12 + ((h >>> 3) % 20) + Math.sin(t * 0.3 + k) * 4;
      circ(g, cx, y + 6, 5); g.fill(); circ(g, cx + 6, y + 4, 6.5); g.fill(); circ(g, cx + 12, y + 7, 4.5); g.fill();
      if (zb.z0 === 0 || zb.z0 === 5) { circ(g, x + 8, y - 16, 4); g.fillStyle = '#fff6d0'; g.fill(); }
      g.restore();
      g.strokeStyle = '#2a2238'; g.lineWidth = 3;
      g.beginPath(); g.moveTo(x, y - 30); g.lineTo(x, y + 30); g.moveTo(x - 19, y + 2); g.lineTo(x + 19, y + 2); g.stroke();
      g.fillStyle = 'rgba(160,150,190,0.9)'; g.fillRect(x - 27, y + 30, 54, 6);
      g.fillStyle = 'rgba(0,0,0,0.3)'; g.fillRect(x - 27, y + 35, 54, 2);
    } else if (type === 2 || type === 3) {
      const tx = type === 2 ? TL + 36 : TR - 36;
      const fl = 0.85 + Math.sin(t * 13 + k) * 0.08 + Math.sin(t * 23 + k * 3) * 0.06;
      g.globalCompositeOperation = 'lighter';
      g.drawImage(Assets.glow, tx - 50 * fl, y - 64 * fl, 100 * fl, 100 * fl);
      g.globalCompositeOperation = 'source-over';
      g.fillStyle = '#3b3346'; g.fillRect(tx - 7, y + 6, 14, 3); g.fillRect(tx - 2, y + 2, 4, 12);
      g.beginPath(); g.moveTo(tx - 4.5, y - 8); g.lineTo(tx + 4.5, y - 8); g.lineTo(tx + 2.2, y + 9); g.lineTo(tx - 2.2, y + 9); g.closePath();
      g.fillStyle = '#7a4a24'; g.fill(); g.strokeStyle = OUTL; g.lineWidth = 1.2; g.stroke();
      const fh = 13 + Math.sin(t * 17 + k) * 2.2;
      flamePath(g, tx + Math.sin(t * 9 + k) * 0.8, y - 8, 6, fh); g.fillStyle = '#ff6a1a'; g.fill();
      flamePath(g, tx, y - 8, 3.4, fh * 0.62); g.fillStyle = '#ffe45c'; g.fill();
    } else if (type === 4) {
      const col = mixHex(Z0.accent, Z1.accent, zb.f), sw = Math.sin(t * 1.6 + k) * 2;
      g.fillStyle = '#5a4a32'; g.fillRect(x - 17, y - 33, 34, 4);
      g.beginPath(); g.moveTo(x - 13, y - 30); g.lineTo(x + 13, y - 30); g.lineTo(x + 13 + sw, y + 20); g.lineTo(x + sw * 0.5, y + 11); g.lineTo(x - 13 + sw, y + 20); g.closePath();
      g.fillStyle = col; g.fill(); g.strokeStyle = 'rgba(20,14,36,0.8)'; g.lineWidth = 1.6; g.stroke();
      g.fillStyle = 'rgba(0,0,0,0.18)'; g.fillRect(x - 13, y - 30, 26, 4);
      starPath(g, x + sw * 0.3, y - 8, 5, 7, 3, -Math.PI / 2); g.fillStyle = 'rgba(255,245,210,0.85)'; g.fill();
    }
  }
}
function drawSky(g, camY, t, zb) {
  const Z0 = ZONE_VIS[zb.z0], Z1 = ZONE_VIS[zb.z1];
  const gr = g.createLinearGradient(0, 0, 0, H);
  gr.addColorStop(0, mixHex(Z0.sky[0], Z1.sky[0], zb.f)); gr.addColorStop(1, mixHex(Z0.sky[1], Z1.sky[1], zb.f));
  g.fillStyle = gr; g.fillRect(TL, 0, TW, H);
  const starA = clamp((zb.cf - 960) / 50, 0, 1);
  if (starA > 0) {
    const top = camY * 0.12;
    for (let i = 0; i < 70; i++) {
      const h = hash32(i * 977 + 3);
      const sx = TL + (h % TW), sy = mod((h >>> 9) % 1400 - top, 1400) - 200;
      if (sy < -4 || sy > H + 4) continue;
      g.globalAlpha = starA * (0.45 + 0.55 * Math.abs(Math.sin(t * (1 + (h % 7) * 0.3) + i)));
      g.fillStyle = '#ffffff'; g.fillRect(sx, sy, (h & 3) === 0 ? 2 : 1.3, (h & 3) === 0 ? 2 : 1.3);
    }
    g.globalAlpha = 1;
  }
  const cloudA = 1 - starA * 0.85;
  const top = camY * 0.3;
  for (let i = 0; i < 9; i++) {
    const h = hash32(i * 4099 + 11);
    const cx = TL + (h % TW) + Math.sin(t * 0.1 + i) * 10;
    const cy = mod((h >>> 10) % 900 - top, 900) - 150;
    if (cy < -60 || cy > H + 60) continue;
    const s = 0.7 + ((h >>> 5) % 60) / 60;
    g.fillStyle = 'rgba(255,255,255,' + (0.55 * cloudA).toFixed(3) + ')';
    circ(g, cx, cy, 16 * s); g.fill(); circ(g, cx + 18 * s, cy - 6 * s, 20 * s); g.fill(); circ(g, cx + 38 * s, cy, 15 * s); g.fill();
    rrect(g, cx - 4, cy - 2, 46 * s, 16 * s, 8 * s); g.fill();
  }
}
function drawBackdrop(g, camY, t) {
  const zb = zoneBlend(camY);
  const Z0 = ZONE_VIS[zb.z0], Z1 = ZONE_VIS[zb.z1];
  const sky = clamp((zb.cf - 775) / 30, 0, 1);
  if (sky < 1) {
    const off = mod(-camY * 0.5, 320);
    const t0 = Assets.tinted('bg', zb.z0);
    for (let y = off - 320; y < H; y += 320) g.drawImage(t0, TL, y, TW, 320);
    if (zb.f > 0.01) {
      const t1 = Assets.tinted('bg', zb.z1);
      g.globalAlpha = zb.f;
      for (let y = off - 320; y < H; y += 320) g.drawImage(t1, TL, y, TW, 320);
      g.globalAlpha = 1;
    }
    drawBgFeatures(g, camY, t, zb);
  }
  void Z0; void Z1;
  if (sky > 0) { g.globalAlpha = sky; drawSky(g, camY, t, zb); g.globalAlpha = 1; }
  return zb;
}
function drawWalls(g, camY, zb) {
  const Z0 = ZONE_VIS[zb.z0], Z1 = ZONE_VIS[zb.z1];
  const off = mod(-camY, 256);
  const pass = (z, alpha) => {
    const wl = Assets.tinted('wl', z), wr = Assets.tinted('wr', z);
    g.globalAlpha = alpha;
    for (let y = off - 256; y < H; y += 256) { g.drawImage(wl, 0, y, TL, 256); g.drawImage(wr, TR, y, W - TR, 256); }
    g.globalAlpha = 1;
  };
  pass(zb.z0, 1);
  if (zb.f > 0.01) pass(zb.z1, zb.f);
  void Z0; void Z1;
  let gr = g.createLinearGradient(TL, 0, TL + 16, 0);
  gr.addColorStop(0, 'rgba(0,0,0,0.38)'); gr.addColorStop(1, 'rgba(0,0,0,0)');
  g.fillStyle = gr; g.fillRect(TL, 0, 16, H);
  gr = g.createLinearGradient(TR, 0, TR - 16, 0);
  gr.addColorStop(0, 'rgba(0,0,0,0.38)'); gr.addColorStop(1, 'rgba(0,0,0,0)');
  g.fillStyle = gr; g.fillRect(TR - 16, 0, 16, H);
  g.fillStyle = 'rgba(255,255,255,0.2)'; g.fillRect(TL - 3, 0, 2, H); g.fillRect(TR + 1, 0, 2, H);
  g.fillStyle = 'rgba(0,0,0,0.45)'; g.fillRect(TL - 1, 0, 1, H); g.fillRect(TR, 0, 1, H);
}
function drawSign(g, f, sy, n) {
  const big = f.full;
  const cx = f.x + f.w / 2, y = sy + FB + 6;
  const label = String(n);
  const w = Math.max(big ? 52 : 34, textW(g, label, big ? 20 : 14) + (big ? 22 : 14)), h = big ? 24 : 17;
  g.strokeStyle = '#3a3346'; g.lineWidth = 1.6;
  g.beginPath(); g.moveTo(cx - w / 2 + 6, sy + FB - 2); g.lineTo(cx - w / 2 + 6, y); g.moveTo(cx + w / 2 - 6, sy + FB - 2); g.lineTo(cx + w / 2 - 6, y); g.stroke();
  const gr = g.createLinearGradient(0, y, 0, y + h);
  gr.addColorStop(0, big ? '#ffe27a' : '#5a4631'); gr.addColorStop(1, big ? '#d99a12' : '#3a2b1c');
  rrect(g, cx - w / 2, y, w, h, 5); g.fillStyle = gr; g.fill(); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
  text(g, label, cx, y + h / 2 + 1, { size: big ? 20 : 14, fill: big ? '#3a2200' : '#ffd24a' });
}
function floorStyleFor(n, style) { return style >= 0 ? style : zoneOf(n); }

// ---------- player pose ----------
function poseFor(G, a, time) {
  const p = G.p;
  let state;
  if (G.state === 'dead') state = 'dead';
  else if (!p.ground) state = p.spin ? 'spin' : (p.vy < -1 ? 'jump' : 'fall');
  else if (p.skid) state = 'skid';
  else if (p.edge && Math.abs(p.vx) < 0.6) state = 'edge';
  else if (Math.abs(p.vx) > 0.25) state = 'run';
  else if (G.tick - View.cheerTick < 55 && G.tick >= View.cheerTick) state = 'cheer';
  else state = p.idle > 300 ? 'bored' : 'idle';
  return {
    state, t: time, phase: p.run * 0.2, vx: p.vx, vy: p.vy, face: p.face,
    land: p.ground ? clamp(1 - (G.tick + a - p.landTick) / 8, 0, 1) : 0,
    spinA: p.spin ? p.spin * (G.tick + a - p.jumpTick) * 0.3 : 0,
    edgeLocal: p.edge * p.face, combo: G.combo.on
  };
}

// ---------- world ----------
// o: {char, style, time, noPlayer}
function drawWorld(g, G, a, o) {
  const camY = lerp(G.cam.py, G.cam.y, a);
  const t = o.time;
  const zb = drawBackdrop(g, camY, t);
  const nMin = Math.max(0, Math.floor(-(camY + H + 80) / FLOOR_H)), nMax = Math.ceil(-(camY - 40) / FLOOR_H);
  if (nMin === 0) g.drawImage(Assets.base, TL, -camY + 16, TW, 120);
  for (let n = nMin; n <= nMax; n++) {
    const f = floorAt(G.seed, n), sy = -n * FLOOR_H - camY;
    g.drawImage(Assets.floor(f, floorStyleFor(n, o.style)), f.x, sy - FT, f.w, FSH);
    if (n % 10 === 0 && n > 0) drawSign(g, f, sy, n);
  }
  FX.draw(g, camY, 0);
  if (!o.noPlayer) {
    const p = G.p;
    const x = lerp(p.px, p.x, a), y = lerp(p.py, p.y, a) - camY;
    if (p.ground && G.state === 'play') { g.fillStyle = 'rgba(0,0,0,0.28)'; ell(g, x, y + 0.5, 11, 2.6); g.fill(); }
    const ps = poseFor(G, a, t);
    ps.x = x; ps.y = y;
    drawChar(g, o.char, ps);
  }
  FX.draw(g, camY, 1);
  drawWalls(g, camY, zb);
  FX.draw(g, camY, 2);
  return { camY, zb };
}

// ---------- HUD ----------
function drawClock(g, G, t) {
  const c = G.cam;
  const ring = View.ringT;
  g.save();
  if (ring > 0) { g.translate(36, 40); g.rotate(Math.sin(t * 70) * 0.09 * Math.min(1, ring)); g.translate(-36, -40); }
  g.drawImage(Assets.clock, 0, 0, 72, 72);
  const cx = 36, cy = 40;
  g.lineCap = 'round';
  if (c.broken) {
    g.strokeStyle = 'rgba(40,30,20,0.75)'; g.lineWidth = 1.1;
    g.beginPath(); g.moveTo(cx - 12, cy - 12); g.lineTo(cx - 3, cy - 2); g.lineTo(cx - 6, cy + 6); g.lineTo(cx + 2, cy + 14); g.moveTo(cx - 3, cy - 2); g.lineTo(cx + 9, cy - 5); g.stroke();
    const ang = Math.PI / 2 + 0.35 + Math.sin(t * 2.2) * 0.25;
    g.strokeStyle = OUTL; g.lineWidth = 3;
    g.beginPath(); g.moveTo(cx + 2, cy + 2); g.lineTo(cx + 2 + Math.cos(ang) * 13, cy + 2 + Math.sin(ang) * 13); g.stroke();
  } else {
    const ang = (c.clock / REV_TICKS) * TAU - Math.PI / 2;
    g.strokeStyle = OUTL; g.lineWidth = 3.2;
    g.beginPath(); g.moveTo(cx, cy); g.lineTo(cx + Math.cos(ang) * 15.5, cy + Math.sin(ang) * 15.5); g.stroke();
    g.strokeStyle = '#e8413c'; g.lineWidth = 1.6;
    g.beginPath(); g.moveTo(cx + Math.cos(ang) * 8, cy + Math.sin(ang) * 8); g.lineTo(cx + Math.cos(ang) * 15, cy + Math.sin(ang) * 15); g.stroke();
  }
  circ(g, cx, cy, 2.6); g.fillStyle = '#e8413c'; g.fill(); g.lineWidth = 1.2; g.strokeStyle = OUTL; g.stroke();
  if (ring > 0) {
    g.strokeStyle = 'rgba(255,240,180,' + Math.min(1, ring).toFixed(2) + ')'; g.lineWidth = 2;
    for (const s of [-1, 1]) for (let i = 0; i < 3; i++) {
      const a0 = -Math.PI / 2 + s * (0.9 + i * 0.25);
      g.beginPath(); g.moveTo(cx + Math.cos(a0) * 31, cy - 8 + Math.sin(a0) * 31); g.lineTo(cx + Math.cos(a0) * 37, cy - 8 + Math.sin(a0) * 37); g.stroke();
    }
  }
  g.restore();
  for (let i = 1; i <= 6; i++) {
    const on = c.level >= i;
    circ(g, 9 + (i - 1) * 9.2, 82, 3.2);
    g.fillStyle = on ? (i >= 5 ? '#ff5a5a' : i >= 3 ? '#ffb347' : '#8dff6a') : 'rgba(20,16,40,0.8)';
    g.fill(); g.lineWidth = 1.2; g.strokeStyle = OUTL; g.stroke();
  }
}
function drawComboMeter(g, G, a, t) {
  const cb = G.combo, x = 21, y = 124, w = 22, h = 196;
  rrect(g, x, y, w, h, 11); g.fillStyle = 'rgba(12,9,28,0.78)'; g.fill(); g.lineWidth = 2.5; g.strokeStyle = OUTL; g.stroke();
  if (cb.on) {
    const f = clamp((cb.timer - a) / COMBO_TIME, 0, 1), fh = Math.max(6, (h - 6) * f);
    const col = f > 0.5 ? ['#c8ffd4', '#2fd35a'] : f > 0.25 ? ['#fff3b8', '#f0b400'] : ['#ffd0d0', '#e8261c'];
    const gr = g.createLinearGradient(x, 0, x + w, 0);
    gr.addColorStop(0, col[1]); gr.addColorStop(0.45, col[0]); gr.addColorStop(1, col[1]);
    rrect(g, x + 3, y + h - 3 - fh, w - 6, fh, 8); g.fillStyle = gr; g.fill();
  }
  g.strokeStyle = 'rgba(255,255,255,0.14)'; g.lineWidth = 1;
  for (let i = 1; i < 6; i++) { const yy = y + (h / 6) * i; g.beginPath(); g.moveTo(x + 4, yy); g.lineTo(x + w - 4, yy); g.stroke(); }
  g.fillStyle = 'rgba(255,255,255,0.22)'; rrect(g, x + 4, y + 6, 4, h - 12, 2); g.fill();
  const n = cb.on ? cb.floors : 0;
  const pulse = 1 + View.comboPulse * 0.35;
  g.save(); g.translate(x + w / 2, y - 16); g.scale(pulse, pulse); g.rotate(Math.sin(t * 3) * 0.08);
  starPath(g, 0, 0, 5, 17, 9, -Math.PI / 2);
  g.fillStyle = cb.on ? (n >= 25 ? rainbowCol(t) : '#ffd24a') : '#4a4570'; g.fill(); g.lineWidth = 2.2; g.strokeStyle = OUTL; g.stroke();
  text(g, String(n), 0, 2, { size: n >= 100 ? 12 : 15, fill: cb.on ? '#2a1a00' : '#bdb6e6' });
  g.restore();
  g.save(); g.translate(x + w / 2, y + h + 13);
  text(g, T('combo'), 0, 0, { size: 12, font: UIF, weight: 800, fill: '#ffe9a8', stroke: OUTL, lw: 4 });
  g.restore();
}
function drawHUD(g, G, a, o) {
  const t = o.time;
  drawClock(g, G, t);
  drawComboMeter(g, G, a, t);
  const sc = gameScore(G);
  View.shownScore = View.shownScore > sc ? sc : View.shownScore + Math.max(1, (sc - View.shownScore) * 0.2);
  if (sc - View.shownScore < 1) View.shownScore = sc;
  text(g, T('score'), 12, 432, { size: 13, font: UIF, weight: 800, fill: '#ffe9a8', stroke: OUTL, lw: 4, align: 'left' });
  text(g, fmt(View.shownScore), 12, 456, { size: 26, fill: '#ffffff', stroke: OUTL, lw: 6, align: 'left' });
  text(g, T('floor'), W - 12, 62, { size: 13, font: UIF, weight: 800, fill: '#bfe9ff', stroke: OUTL, lw: 4, align: 'right' });
  text(g, String(G.best), W - 12, 84, { size: 24, fill: '#ffffff', stroke: OUTL, lw: 6, align: 'right' });
}
function drawVignette(g) {
  g.drawImage(Assets.vignette, 0, 0, W, 64);
  g.save(); g.translate(0, H); g.scale(1, -1); g.drawImage(Assets.vignette, 0, 0, W, 64); g.restore();
}
function drawPauseButton(g, x, y, hot) {
  rrect(g, x, y, 30, 30, 8); g.fillStyle = hot ? 'rgba(139,230,255,0.35)' : 'rgba(12,9,28,0.6)'; g.fill(); g.lineWidth = 2; g.strokeStyle = 'rgba(255,255,255,0.5)'; g.stroke();
  g.fillStyle = '#fff'; g.fillRect(x + 10, y + 8, 4, 14); g.fillRect(x + 17, y + 8, 4, 14);
}

// ---------- mapping sim events to sound + effects ----------
// mode: 'live' | 'replay' | 'attract'
function onSimEvent(e, G, mode) {
  const snd = mode === 'live' || mode === 'replay';
  const p = G.p;
  switch (e.type) {
    case 'jump':
      if (snd) Sound.sfx.jump(e.power, e.spin);
      dust(p.x, p.y, 4 + Math.floor(e.power * 5), 8, 40);
      if (e.spin) FX.add({ t: 'ring', x: p.x, y: p.y - 20, vx: 0, vy: 0, life: 0.35, s: 8, grow: 30, col: 'rgba(255,255,255,0.9)', layer: 1 });
      break;
    case 'land':
      if (snd) Sound.sfx.land(e.impact);
      if (e.impact > 4) dust(p.x, p.y, 3 + Math.floor(e.impact / 3), 10, 30 + e.impact * 3);
      break;
    case 'wall': {
      if (snd) Sound.sfx.wall(e.speed);
      const wx = e.side < 0 ? TL + 2 : TR - 2;
      for (let i = 0; i < 8; i++) {
        const ang = (e.side < 0 ? 0 : Math.PI) + rand(-1, 1);
        FX.add({ t: 'spark', x: wx, y: p.y - 22 + rand(-8, 8), vx: Math.cos(ang) * rand(120, 300), vy: Math.sin(ang) * rand(120, 300), life: rand(0.2, 0.4), s: 2, grav: 300, col: '#fff3c0', layer: 1 });
      }
      if (e.speed > 7 && settings.shake && mode !== 'attract') View.shake = Math.max(View.shake, 2.5);
      break;
    }
    case 'bump':
      if (snd) Sound.sfx.bump();
      dust(p.x + (e.side < 0 ? -10 : 10), p.y - 4, 4, 4, 30);
      break;
    case 'cstep':
      if (snd) Sound.sfx.comboStep(e.jumps);
      View.comboPulse = 1;
      burst(p.x, p.y - 6, 5 + Math.min(10, e.d * 2), { min: 60, max: 180, life: 0.7, s: 13, grav: 200 });
      break;
    case 'combo': {
      if (snd) { Sound.sfx.combo(e.tier); if (e.tier >= 0) Sound.say(TIERS[e.tier].w.replace('!', '').toLowerCase()); }
      if (mode === 'attract') { burst(p.x, p.y - 20, 14, { min: 80, max: 260, life: 0.9, s: 14 }); View.cheerTick = G.tick; break; }
      if (e.tier >= 0) Pops.add({ t: 'reward', dur: 2.2, word: TIERS[e.tier].w, floors: e.floors, pts: e.pts, tier: e.tier });
      burst(W / 2, 196, 22 + e.tier * 4, { screen: true, layer: 3, min: 120, max: 420 + e.tier * 20, life: 1.3, s: 20, grav: 380 });
      if (mode !== 'attract' && settings.shake) View.shake = Math.max(View.shake, 3 + e.tier * 0.8);
      if (e.tier >= 6 && !REDUCED) { View.flash = 0.35; View.flashCol = '#ffffff'; }
      View.cheerTick = G.tick;
      break;
    }
    case 'zone':
      if (snd) Sound.sfx.zone();
      if (mode !== 'attract') Pops.add({ t: 'banner', dur: 2.6, text: TT(ZONE_NAMES[e.z]), sub: T('floor') + ' ' + e.z * 100, col: e.z >= 8 ? '#ffffff' : ZONE_VIS[e.z].wall });
      break;
    case 'hurry':
      if (snd) { Sound.sfx.hurry(); Sound.say('hurry up'); if (e.broken) Sound.sfx.clockBreak(); Sound.music.level(e.level); }
      if (mode === 'attract') break;
      Pops.add({ t: 'hurry', dur: 2.1, broken: e.broken });
      View.ringT = 1.5;
      if (!REDUCED) { View.flash = 0.25; View.flashCol = '#ffe0c0'; }
      if (e.broken) {
        for (let i = 0; i < 6; i++) FX.add({ t: 'gear', x: 36, y: 40, vx: rand(-80, 160), vy: rand(-260, -120), life: 1.4, s: rand(4, 7), rot: rand(TAU), vr: rand(-10, 10), grav: 600, layer: 3, screen: true, fade: false });
      }
      break;
    case 'dead':
      if (snd) { Sound.sfx.dead(); Sound.say('game over'); }
      break;
    default: break;
  }
}
// called once per simulated tick for continuous effects
function simTickFX(G) {
  const p = G.p;
  if (G.state !== 'play') return;
  if (G.combo.on && (!p.ground || Math.abs(p.vx) > 2) && G.tick % 2 === 0) {
    FX.add({ t: 'star', x: p.x + rand(-6, 6), y: p.y - 20 + rand(-10, 10), vx: rand(-30, 30) - p.vx * 6, vy: rand(-20, 30), life: rand(0.4, 0.75), s: rand(9, 15), c: (G.tick >> 1) % STAR_COLS.length, rot: rand(TAU), vr: rand(-6, 6), grav: 60, drag: 0.96, layer: 0 });
  } else if (p.spin && G.tick % 3 === 0) {
    FX.add({ t: 'star', x: p.x, y: p.y - 20, vx: rand(-20, 20), vy: rand(-20, 20), life: 0.4, s: 9, c: 6, rot: 0, vr: 4, grav: 0, layer: 0 });
  }
  if (p.skid && G.tick % 3 === 0) dust(p.x + p.face * 6, p.y, 1, 3, 20);
}
// ambient particles for the current zone (screen-space, drawn above the walls)
let ambAcc = 0;
function ambientFX(dt, zb) {
  const z = zb.f > 0.5 ? zb.z1 : zb.z0;
  const kind = ZONE_VIS[z].amb;
  const rates = { dust: 3, snow: 14, leaf: 2, spark: 3, sprinkle: 6, wisp: 1.5, firefly: 2.5, steam: 2, feather: 2, sparkle: 5, shoot: 0.35 };
  ambAcc += dt * (rates[kind] || 0);
  while (ambAcc >= 1) {
    ambAcc -= 1;
    const x = rand(TL, TR);
    const base = { layer: 2, screen: true, rot: rand(TAU) };
    switch (kind) {
      case 'dust': FX.add(Object.assign(base, { t: 'dust', x, y: rand(0, H), vx: rand(-8, 8), vy: rand(-8, 8), life: rand(2, 4), s: rand(0.6, 1.4), col: 'rgba(255,240,220,0.5)', fadeIn: 0.6 })); break;
      case 'snow': FX.add(Object.assign(base, { t: 'snow', x, y: -6, vx: rand(-10, 10), vy: rand(30, 60), life: 10, s: rand(1, 2.4), sway: rand(1, 2), swayA: 18, ph: rand(TAU), alpha: 0.85, fade: false })); break;
      case 'leaf': FX.add(Object.assign(base, { t: 'leaf', x, y: -8, vx: rand(-20, 20), vy: rand(30, 55), life: 10, s: rand(0.7, 1), vr: rand(-2, 2), sway: 1.5, swayA: 30, col: pick(['#e0892b', '#c9582b', '#e8b33b', '#7bb33b']), fade: false })); break;
      case 'spark': FX.add(Object.assign(base, { t: 'spark', x, y: -4, vx: rand(-40, 40), vy: rand(100, 220), life: rand(0.8, 1.6), s: 1.6, grav: 200, col: '#ffd27a' })); break;
      case 'sprinkle': FX.add(Object.assign(base, { t: 'conf', x, y: -6, vx: rand(-20, 20), vy: rand(40, 80), life: 10, s: 2.2, vr: rand(-6, 6), col: pick(['#ffe45c', '#5ce1ff', '#8dff6a', '#ffffff', '#b98cff', '#ff6fb3']), fade: false })); break;
      case 'wisp': FX.add(Object.assign(base, { t: 'glow', x, y: H + 10, vx: rand(-6, 6), vy: -rand(15, 30), life: 6, s: rand(1.5, 3), col: 'rgba(210,230,255,0.6)', col2: 'rgba(160,190,255,0.12)', sway: 1, swayA: 14, fadeIn: 1 })); break;
      case 'firefly': FX.add(Object.assign(base, { t: 'glow', x, y: rand(40, H - 40), vx: rand(-15, 15), vy: rand(-10, 10), life: rand(3, 5), s: rand(1.2, 2), sway: 2, swayA: 16, ph: rand(TAU), fadeIn: 0.8 })); break;
      case 'steam': FX.add(Object.assign(base, { t: 'steam', x, y: H + 10, vx: rand(-8, 8), vy: -rand(20, 40), life: 5, s: rand(4, 8), fadeIn: 1 })); break;
      case 'feather': FX.add(Object.assign(base, { t: 'feather', x, y: -6, vx: rand(-10, 10), vy: rand(20, 35), life: 14, s: rand(3, 4.5), vr: rand(-1, 1), sway: 1.2, swayA: 26, fade: false })); break;
      case 'sparkle': FX.add(Object.assign(base, { t: 'twinkle', x, y: rand(0, H), vx: 0, vy: 0, life: rand(0.8, 1.4), s: rand(1.5, 3), col: pick(['#ffffff', '#ffe45c', '#ff9fe0', '#9fe8ff']), fade: false })); break;
      case 'shoot': FX.add(Object.assign(base, { t: 'shoot', x: rand(TL + 100, TR + 60), y: rand(-10, 120), vx: -rand(300, 420), vy: rand(150, 220), life: 0.9 })); break;
      default: break;
    }
  }
}
// ===================== immediate-mode canvas UI =====================
const UI = {
  items: [], prev: [], focus: 0, mouse: { x: -1, y: -1 }, keyNav: true,
  begin() { this.prev = this.items; this.items = []; },
  end() { const n = this.items.length; if (n && this.focus >= n) this.focus = n - 1; if (this.focus < 0) this.focus = 0; },
  add(it) { const i = this.items.length; it.i = i; this.items.push(it); return i === this.focus && !it.skip; },
  inside(it, x, y) { return x >= it.x && x <= it.x + it.w && y >= it.y && y <= it.y + it.h; },
  reset(f) { this.focus = f || 0; },
  nav(dir) {
    const list = this.prev;
    if (!list.length) return false;
    this.keyNav = true;
    if (dir === 'up' || dir === 'down') {
      const n = list.length;
      let f = this.focus;
      for (let k = 0; k < n; k++) { f = (f + (dir === 'down' ? 1 : -1) + n) % n; if (!list[f].skip && !list[f].noNav) break; }
      if (f !== this.focus) { this.focus = f; Sound.sfx.move(); if (list[f].onHover) list[f].onHover(); }
      return true;
    }
    const it = list[this.focus];
    if (!it || it.skip) return false;
    if (dir === 'left' && it.left) { it.left(); return true; }
    if (dir === 'right' && it.right) { it.right(); return true; }
    if (dir === 'ok' && it.act) { it.act(); return true; }
    return false;
  },
  pointerMove(x, y) {
    this.mouse.x = x; this.mouse.y = y;
    for (let i = this.prev.length - 1; i >= 0; i--) {
      const it = this.prev[i];
      if (!it.skip && this.inside(it, x, y)) {
        if (this.focus !== i) { this.focus = i; if (it.onHover) it.onHover(); }
        this.keyNav = false;
        return;
      }
    }
  },
  click(x, y) {
    for (let i = this.prev.length - 1; i >= 0; i--) {
      const it = this.prev[i];
      if (!it.skip && this.inside(it, x, y)) {
        this.focus = i;
        if (it.click) it.click(x - it.x, y - it.y);
        else if (it.act) it.act();
        return true;
      }
    }
    return false;
  }
};

function wrapText(g, str, maxW, size, font, weight) {
  g.font = (weight ? weight + ' ' : '') + size + 'px ' + (font || UIF);
  const words = str.split(' '), lines = [];
  let line = '';
  for (const w of words) {
    const test = line ? line + ' ' + w : w;
    if (g.measureText(test).width > maxW && line) { lines.push(line); line = w; } else line = test;
  }
  if (line) lines.push(line);
  return lines;
}
function panel(g, x, y, w, h, o) {
  o = o || {};
  rrect(g, x, y, w, h, o.r || 16);
  g.fillStyle = o.fill || 'rgba(17,13,38,0.9)'; g.fill();
  g.lineWidth = 2; g.strokeStyle = o.stroke || 'rgba(190,180,255,0.35)'; g.stroke();
  g.save(); rrect(g, x, y, w, h, o.r || 16); g.clip();
  const gr = g.createLinearGradient(0, y, 0, y + 40);
  gr.addColorStop(0, 'rgba(255,255,255,0.07)'); gr.addColorStop(1, 'rgba(255,255,255,0)');
  g.fillStyle = gr; g.fillRect(x, y, w, 40);
  g.restore();
}
function header(g, title, y) {
  y = y || 38;
  const gr = g.createLinearGradient(0, y - 20, 0, y + 20);
  gr.addColorStop(0, '#ffffff'); gr.addColorStop(0.5, '#aef3ff'); gr.addColorStop(1, '#3aa0ea');
  const size = fitSize(g, title, 38, 520);
  text(g, title, W / 2 + 2, y + 4, { size, fill: 'rgba(0,0,0,0.35)' });
  text(g, title, W / 2, y, { size, fill: gr, stroke: '#101a3a', lw: 9 });
}
function button(g, label, x, y, w, h, act, o) {
  o = o || {};
  const f = UI.add({ x, y, w, h, act, skip: !!o.disabled });
  const on = f && !o.disabled;
  rrect(g, x, y, w, h, 10);
  g.fillStyle = o.disabled ? 'rgba(40,34,70,0.5)' : on ? '#ffd24a' : o.primary ? 'rgba(255,210,74,0.22)' : 'rgba(30,24,60,0.88)';
  g.fill();
  g.lineWidth = 2; g.strokeStyle = on ? '#fff3c0' : o.primary ? 'rgba(255,210,74,0.7)' : 'rgba(190,180,255,0.4)'; g.stroke();
  const size = fitSize(g, label, o.size || 18, w - 14);
  text(g, label, x + w / 2, y + h / 2 + 1, { size, fill: on ? '#2a1d04' : o.disabled ? '#77719a' : '#ffffff' });
  return f;
}
function menuItem(g, label, cy, act, t) {
  const w = 320, h = 34, x = W / 2 - w / 2;
  const f = UI.add({ x, y: cy - h / 2, w, h, act });
  if (f) {
    const gr = g.createLinearGradient(0, cy - 16, 0, cy + 16);
    gr.addColorStop(0, '#fff6c8'); gr.addColorStop(1, '#ffae00');
    text(g, label, W / 2, cy + 1, { size: 31, fill: gr, stroke: OUTL, lw: 8 });
    const tw = textW(g, label, 31), bob = Math.sin(t * 6) * 2;
    for (const s of [-1, 1]) {
      g.save(); g.translate(W / 2 + s * (tw / 2 + 22 + bob), cy); g.rotate(t * 3 * s);
      starPath(g, 0, 0, 5, 9, 4.2, -Math.PI / 2); g.fillStyle = '#ffd24a'; g.fill(); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
      g.restore();
    }
  } else text(g, label, W / 2, cy + 1, { size: 25, fill: '#ebe6ff', stroke: OUTL, lw: 6 });
  return f;
}
// A label/value row. o: {left, right, act, slider (0-10), set(v)}
function optRow(g, label, value, y, o) {
  o = o || {};
  const x = 100, w = 440, h = 25;
  const it = { x: x - 8, y: y - h / 2, w: w + 16, h, left: o.left, right: o.right, act: o.act || o.right };
  if (o.slider !== undefined) {
    it.left = () => { o.set(clamp(o.slider - 1, 0, 10)); };
    it.right = () => { o.set(clamp(o.slider + 1, 0, 10)); };
    it.act = null;
    it.click = lx => { const sx = w - 160; if (lx >= sx - 12) o.set(clamp(lx < sx ? 0 : Math.floor((lx - sx) / 14) + 1, 0, 10)); };
  }
  const f = UI.add(it);
  if (f) {
    rrect(g, x - 8, y - h / 2, w + 16, h, 8); g.fillStyle = 'rgba(255,210,74,0.15)'; g.fill();
    g.strokeStyle = 'rgba(255,210,74,0.65)'; g.lineWidth = 1.5; g.stroke();
  }
  text(g, label, x + 4, y + 1, { size: 15, font: UIF, weight: 800, fill: f ? '#ffe9a8' : '#d8d2f5', align: 'left' });
  if (o.slider !== undefined) {
    const sx = x + w - 168;
    for (let i = 0; i < 10; i++) {
      const on = i < o.slider, bh = 6 + i * 1.1;
      rrect(g, sx + i * 14, y + 7 - bh, 10, bh, 2);
      g.fillStyle = on ? (f ? '#ffd24a' : '#bfe9ff') : 'rgba(255,255,255,0.12)'; g.fill();
    }
    text(g, String(o.slider), x + w - 18, y + 1, { size: 15, fill: '#fff', align: 'right' });
  } else {
    const adj = !!(o.left || o.right);
    const vx = x + w - 18;
    const size = fitSize(g, value, 17, 250);
    text(g, value, vx, y + 1, { size, fill: '#ffffff', align: 'right' });
    if (adj && f) {
      const tw = textW(g, value, size);
      g.fillStyle = '#ffd24a';
      g.beginPath(); g.moveTo(vx - tw - 16, y + 1); g.lineTo(vx - tw - 9, y - 5); g.lineTo(vx - tw - 9, y + 7); g.closePath(); g.fill();
      g.beginPath(); g.moveTo(vx + 13, y + 1); g.lineTo(vx + 6, y - 5); g.lineTo(vx + 6, y + 7); g.closePath(); g.fill();
    }
  }
  return f;
}
function drawRankBadge(g, x, y, r, idx, t) {
  circ(g, x, y, r);
  const gr = g.createRadialGradient(x - r * 0.3, y - r * 0.3, 2, x, y, r);
  if (idx < 0) { gr.addColorStop(0, '#6a6590'); gr.addColorStop(1, '#2d2950'); }
  else if (idx >= 6) { gr.addColorStop(0, '#fff6c0'); gr.addColorStop(1, '#d99a12'); }
  else { gr.addColorStop(0, '#bff3ff'); gr.addColorStop(1, '#2e7fd0'); }
  g.fillStyle = gr; g.fill(); g.lineWidth = 3; g.strokeStyle = OUTL; g.stroke();
  if (idx < 0) text(g, '–', x, y + 2, { size: r, fill: '#cfc9f0' });
  else if (idx < 6) text(g, RANKS[idx].r, x, y + 3, { size: r * 1.15, fill: '#ffffff', stroke: OUTL, lw: 6 });
  else {
    const n = RANKS[idx].stars, s = r * (n > 3 ? 0.3 : 0.38);
    for (let i = 0; i < n; i++) {
      const a = -Math.PI / 2 + (i - (n - 1) / 2) * 0.62;
      const sx = x + Math.cos(a) * r * 0.45 * (n > 1 ? 1 : 0), sy = y + Math.sin(a) * r * 0.45 * (n > 1 ? 1 : 0) + (n > 1 ? r * 0.25 : 0);
      starPath(g, sx, sy, 5, s, s * 0.45, -Math.PI / 2 + Math.sin(t * 2 + i) * 0.1);
      g.fillStyle = '#ffffff'; g.fill(); g.lineWidth = 1.5; g.strokeStyle = OUTL; g.stroke();
    }
  }
}
function rankName(idx) { return idx < 0 ? '–' : idx < 6 ? RANKS[idx].r : '★'.repeat(RANKS[idx].stars); }
// ===================== screens =====================
const Screens = {};

function menuBackdrop(g, dim, t) {
  const at = App.attract;
  const w = drawWorld(g, at.g, App.alpha, { char: at.char, style: settings.style, time: t });
  View.zb = w.zb;
  g.fillStyle = 'rgba(9,7,22,' + dim + ')';
  g.fillRect(0, 0, W, H);
}
function drawLogo(g, cx, cy, t) {
  const word = 'HOPSCRAPER', size = 64;
  g.font = size + 'px ' + DISPLAY;
  const ws = [];
  let total = 0;
  for (const ch of word) { const w = g.measureText(ch).width; ws.push(w); total += w + 2; }
  total -= 2;
  let x = cx - total / 2;
  for (let i = 0; i < word.length; i++) {
    const w = ws[i], y = cy + Math.sin(t * 2.4 - i * 0.55) * 4, rot = Math.sin(t * 1.7 - i * 0.7) * 0.05;
    g.save(); g.translate(x + w / 2, y); g.rotate(rot);
    const fill = g.createLinearGradient(0, -30, 0, 30);
    fill.addColorStop(0, '#ffffff'); fill.addColorStop(0.45, '#b4f4ff'); fill.addColorStop(1, '#2b8de0');
    text(g, word[i], 3, 6, { size, fill: 'rgba(0,0,0,0.38)' });
    text(g, word[i], 0, 0, { size, fill, stroke: '#0e1838', lw: 12 });
    g.fillStyle = '#ffffff'; ell(g, 0, -size * 0.34, w * 0.34, 4.2); g.fill();
    g.restore();
    x += w + 2;
  }
}

// ---------- title ----------
Screens.title = {
  enter() { UI.reset(App.titleFocus || 0); },
  key(nav) { if (nav && nav !== 'back') UI.nav(nav); },
  draw(g, t) {
    menuBackdrop(g, 0.5, t);
    const shade = g.createRadialGradient(W / 2, 290, 30, W / 2, 290, 250);
    shade.addColorStop(0, 'rgba(9,7,22,0.55)'); shade.addColorStop(1, 'rgba(9,7,22,0)');
    g.fillStyle = shade; g.fillRect(0, 110, W, 370);
    drawLogo(g, W / 2, 66, t);
    text(g, T('tagline'), W / 2, 112, { size: 17, font: UIF, weight: 700, fill: '#d4efff', stroke: OUTL, lw: 4 });
    const items = [
      ['play', () => startGame()], ['character', () => App.go('chars')], ['highscores', () => App.go('scores')],
      ['replays', () => App.go('replays')], ['trophies', () => App.go('trophies')], ['options', () => App.go('options')],
      ['help', () => App.go('help')]
    ];
    items.forEach((it, i) => { if (menuItem(g, T(it[0]), 152 + i * 38, () => { App.titleFocus = i; Sound.sfx.select(); it[1](); }, t)) App.titleFocus = i; });
    const R = Data.records, rk = currentRank(R);
    const line = T('best') + ' ' + fmt(R.score) + '    ' + T('rank') + ' ';
    const lw = textW(g, line, 15, UIF, 800);
    const x0 = W / 2 - (lw + 24) / 2;
    text(g, line, x0, 431, { size: 15, font: UIF, weight: 800, fill: '#ffe9a8', stroke: OUTL, lw: 4, align: 'left' });
    drawRankBadge(g, x0 + lw + 11, 430, 11, rk, t);
    text(g, touchMode() ? T('hintTouch') : T('hintKeys'), W / 2, 458, { size: 12.5, font: UIF, weight: 700, fill: 'rgba(230,225,255,0.75)', stroke: OUTL, lw: 3 });
  }
};

// ---------- character select ----------
const PEDESTAL = [1, 3, 6, 4];
Screens.chars = {
  sel: 0,
  enter() { this.sel = settings.char; UI.reset(this.sel); },
  choose(i) { settings.char = i; saveSettings(); Sound.sfx.select(); App.go('title'); },
  key(nav) {
    if (nav === 'left' || nav === 'right') {
      this.sel = (this.sel + (nav === 'left' ? 3 : 1)) % 4; UI.focus = this.sel; Sound.sfx.move();
    } else if (nav === 'up' || nav === 'down') { UI.focus = UI.focus === 4 ? this.sel : 4; Sound.sfx.move(); }
    else if (nav === 'ok') { if (UI.focus === 4) { Sound.sfx.back(); App.go('title'); } else this.choose(this.sel); }
    else if (nav === 'back') { Sound.sfx.back(); App.go('title'); }
  },
  draw(g, t) {
    menuBackdrop(g, 0.74, t);
    header(g, T('chooseChar'));
    for (let i = 0; i < 4; i++) {
      const cx = 110 + i * 140, cy = 292, on = i === this.sel;
      UI.add({ x: cx - 62, y: 118, w: 124, h: 250, act: () => this.choose(i), onHover: () => { this.sel = i; } });
      if (on) {
        const gr = g.createRadialGradient(cx, cy - 50, 5, cx, cy - 50, 110);
        gr.addColorStop(0, 'rgba(255,230,140,0.35)'); gr.addColorStop(1, 'rgba(255,230,140,0)');
        g.fillStyle = gr; g.fillRect(cx - 110, cy - 160, 220, 220);
      }
      g.drawImage(Assets.floor({ n: 900 + i, w: 96, x: 0 }, PEDESTAL[i]), cx - 48, cy - FT, 96, FSH);
      const cyc = mod(t + i * 0.3, 2.6);
      const state = on ? (cyc < 1.4 ? 'run' : 'cheer') : (mod(t + i, 5) < 0.2 ? 'cheer' : 'idle');
      drawChar(g, i, { x: cx, y: cy, face: 1, state, t: t + i * 1.7, phase: t * 12, vx: on ? 6 : 0, vy: 0, land: 0, spinA: 0, scale: on ? 2.15 : 1.7, combo: on, edgeLocal: 0 });
      text(g, CHARS[i].name, cx, cy + 52, { size: on ? 28 : 22, fill: on ? '#ffd24a' : '#ebe6ff', stroke: OUTL, lw: 6 });
      if (i === settings.char) text(g, '✓ ' + T('selected'), cx, cy + 76, { size: 12, font: UIF, weight: 800, fill: '#8dff6a', stroke: OUTL, lw: 3 });
    }
    const lines = wrapText(g, TT(CHARS[this.sel].desc), 460, 17, UIF, 700);
    lines.forEach((ln, i) => text(g, ln, W / 2, 392 + i * 20, { size: 17, font: UIF, weight: 700, fill: '#ebe6ff', stroke: OUTL, lw: 4 }));
    button(g, T('back'), W / 2 - 70, 432, 140, 34, () => { Sound.sfx.back(); App.go('title'); });
  }
};

// ---------- options ----------
function unlockedStyles() { const top = zoneOf(Data.records.floor); const a = [-1]; for (let z = 0; z <= top; z++) a.push(z); return a; }
function cycleStyle(d) {
  const a = unlockedStyles();
  let i = a.indexOf(settings.style); if (i < 0) i = 0;
  settings.style = a[(i + d + a.length) % a.length];
  saveSettings(); Sound.sfx.move();
}
function toggleSetting(k) { return () => { settings[k] = !settings[k]; saveSettings(); Sound.sfx.move(); }; }
Screens.options = {
  from: 'title',
  enter(opts) { this.from = (opts && opts.from) || 'title'; UI.reset(opts && opts.focus ? opts.focus : 0); },
  leave() { Sound.sfx.back(); if (this.from === 'pause' && App.sess) App.go('play', { keep: true }); else App.go('title'); },
  key(nav) { if (nav === 'back') this.leave(); else UI.nav(nav); },
  draw(g, t) {
    if (this.from === 'pause' && App.sess) { Screens.play.drawGame(g, t, 1); g.fillStyle = 'rgba(9,7,22,0.84)'; g.fillRect(0, 0, W, H); }
    else menuBackdrop(g, 0.8, t);
    header(g, T('options'));
    const onOff = v => (v ? T('on') : T('off'));
    let y = 84;
    const dy = 27;
    optRow(g, T('language'), T('langName'), y, { left: () => setLang(1 - settings.lang), right: () => setLang(1 - settings.lang) }); y += dy;
    optRow(g, T('music'), null, y, { slider: settings.music, set: v => { settings.music = v; Sound.applyVolumes(); saveSettings(); } }); y += dy;
    optRow(g, T('sfx'), null, y, { slider: settings.sfx, set: v => { settings.sfx = v; Sound.applyVolumes(); saveSettings(); Sound.sfx.move(); } }); y += dy;
    optRow(g, T('voice'), onOff(settings.voice), y, { left: toggleSetting('voice'), right: toggleSetting('voice') }); y += dy;
    optRow(g, T('rejump'), onOff(settings.rejump), y, { left: toggleSetting('rejump'), right: toggleSetting('rejump') }); y += dy;
    optRow(g, T('floorStyle'), settings.style < 0 ? T('classic') : TT(ZONE_NAMES[settings.style]), y, { left: () => cycleStyle(-1), right: () => cycleStyle(1) }); y += dy;
    optRow(g, T('shake'), onOff(settings.shake), y, { left: toggleSetting('shake'), right: toggleSetting('shake') }); y += dy;
    const tc = d => () => { settings.touch = (settings.touch + d + 3) % 3; saveSettings(); Sound.sfx.move(); layout(); };
    optRow(g, T('touchCtl'), [T('auto'), T('on'), T('off')][settings.touch], y, { left: tc(-1), right: tc(1) }); y += dy;
    optRow(g, T('fullscreen'), onOff(isFullscreen()), y, { act: toggleFullscreen }); y += dy;
    optRow(g, T('playerName'), settings.name || '—', y, { act: () => editPlayerName(y) }); y += dy;
    optRow(g, T('controls'), '›', y, { act: () => { Sound.sfx.select(); const f = this.from; App.go('controls'); Screens.options.from = f; } }); y += dy;
    optRow(g, T('resetData'), '›', y, { act: () => App.ask(T('resetAsk'), () => { Data.reset(); View.shownScore = 0; Sound.sfx.select(); }) }); y += dy;
    if (App.flashMsg && App.flashMsgT > 0) text(g, App.flashMsg, W / 2, 412, { size: 14, font: UIF, weight: 800, fill: '#ffd24a', stroke: OUTL, lw: 4 });
    button(g, T('back'), W / 2 - 70, 432, 140, 34, () => this.leave());
  }
};

// ---------- controls ----------
Screens.controls = {
  waiting: null,
  enter() { this.waiting = null; UI.reset(0); },
  back() { Sound.sfx.back(); App.go('options', { from: Screens.options.from, focus: 10 }); },
  key(nav) { if (nav === 'back') this.back(); else UI.nav(nav); },
  rebind(a) {
    this.waiting = a; Sound.sfx.select();
    Input.capture(code => {
      this.waiting = null;
      if (code === 'Escape' && a !== 'pause') { Sound.sfx.back(); return; }
      for (const k in settings.keys) settings.keys[k] = settings.keys[k].filter(c => c !== code);
      settings.keys[a] = [code].concat(settings.keys[a]).slice(0, 3);
      for (const k in settings.keys) if (!settings.keys[k].length) settings.keys[k] = DEF_KEYS[k].filter(c => !Object.values(settings.keys).some(l => l.includes(c)));
      for (const k in settings.keys) if (!settings.keys[k].length) settings.keys[k] = DEF_KEYS[k].slice(0, 1);
      saveSettings(); Sound.sfx.select();
    });
  },
  draw(g, t) {
    if (Screens.options.from === 'pause' && App.sess) { Screens.play.drawGame(g, t, 1); g.fillStyle = 'rgba(9,7,22,0.84)'; g.fillRect(0, 0, W, H); }
    else menuBackdrop(g, 0.8, t);
    header(g, T('controls'));
    let y = 100;
    for (const a of ['left', 'right', 'jump', 'pause']) {
      const val = this.waiting === a ? T('pressKey') : settings.keys[a].map(c => Input.keyName(c)).join('  ·  ');
      optRow(g, T(a), val, y, { act: () => this.rebind(a) });
      y += 34;
    }
    optRow(g, T('resetKeys'), '›', y, { act: () => { settings.keys = JSON.parse(JSON.stringify(DEF_KEYS)); saveSettings(); Sound.sfx.select(); } });
    y += 52;
    for (const k of ['padInfo', 'touchInfo']) {
      for (const ln of wrapText(g, T(k), 440, 14, UIF, 700)) { text(g, ln, W / 2, y, { size: 14, font: UIF, weight: 700, fill: '#cfc9f0', stroke: OUTL, lw: 3 }); y += 19; }
      y += 6;
    }
    button(g, T('back'), W / 2 - 70, 432, 140, 34, () => this.back());
  }
};

// ---------- highscores ----------
const MEDAL = ['#ffd24a', '#d7dce8', '#e09b5a'];
Screens.scores = {
  tab: 0,
  enter(opts) { if (opts && opts.tab !== undefined) this.tab = opts.tab; UI.reset(0); },
  key(nav) {
    if (nav === 'left' || nav === 'right') { this.tab = (this.tab + (nav === 'left' ? 3 : 1)) % 4; UI.reset(0); Sound.sfx.move(); }
    else if (nav === 'back') { Sound.sfx.back(); App.go('title'); }
    else UI.nav(nav);
  },
  draw(g, t) {
    menuBackdrop(g, 0.8, t);
    header(g, T('highscores'), 34);
    if (this.tab < 3) this.table(g, t, ['score', 'floor', 'combo'][this.tab]);
    else this.personal(g, t);
    button(g, T('back'), W / 2 - 70, 436, 140, 32, () => { Sound.sfx.back(); App.go('title'); });
    const tabs = [T('score'), T('floor'), T('combo'), T('personal')];
    for (let i = 0; i < 4; i++) {
      const x = 84 + i * 120, y = 60, w = 112, h = 28, on = i === this.tab;
      const it = { x, y, w, h, noNav: true, act: () => { if (this.tab !== i) { this.tab = i; UI.reset(0); Sound.sfx.move(); } } };
      UI.add(it);
      const hov = !on && UI.inside(it, UI.mouse.x, UI.mouse.y);
      rrect(g, x, y, w, h, 9);
      g.fillStyle = on ? '#ffd24a' : hov ? 'rgba(255,210,74,0.25)' : 'rgba(30,24,60,0.85)'; g.fill();
      g.lineWidth = 2; g.strokeStyle = on ? '#fff3c0' : 'rgba(190,180,255,0.35)'; g.stroke();
      text(g, tabs[i], x + w / 2, y + h / 2 + 1, { size: fitSize(g, tabs[i], 16, w - 10), fill: on ? '#2a1d04' : '#ebe6ff' });
    }
  },
  table(g, t, key) {
    const list = Data.scores[key];
    const y0 = 118, rh = 29;
    const title = { score: T('hofScore'), floor: T('hofFloor'), combo: T('hofCombo') }[key];
    text(g, title, W / 2, 100, { size: 13, font: UIF, weight: 800, fill: '#bfe9ff' });
    if (!list.length) { text(g, T('noScores'), W / 2, 230, { size: 18, font: UIF, weight: 700, fill: '#cfc9f0', stroke: OUTL, lw: 4 }); return; }
    list.forEach((e, i) => {
      const y = y0 + i * rh;
      const rep = e.rid && Data.replays[e.rid];
      const f = UI.add({ x: 80, y: y - rh / 2 + 2, w: 480, h: rh - 4, act: rep ? () => { Sound.sfx.select(); startReplay(rep, 'scores'); } : null });
      rrect(g, 80, y - rh / 2 + 2, 480, rh - 4, 8);
      g.fillStyle = f ? 'rgba(255,210,74,0.18)' : i % 2 ? 'rgba(20,16,44,0.55)' : 'rgba(30,24,60,0.55)'; g.fill();
      if (f) { g.lineWidth = 1.5; g.strokeStyle = 'rgba(255,210,74,0.7)'; g.stroke(); }
      circ(g, 100, y, 10); g.fillStyle = i < 3 ? MEDAL[i] : 'rgba(255,255,255,0.12)'; g.fill();
      if (i < 3) { g.lineWidth = 1.5; g.strokeStyle = OUTL; g.stroke(); }
      text(g, String(i + 1), 100, y + 1, { size: 13, fill: i < 3 ? '#2a1d04' : '#ebe6ff' });
      text(g, e.name, 120, y + 1, { size: fitSize(g, e.name, 17, 130), fill: '#ffffff', align: 'left' });
      text(g, key === 'score' ? fmt(e.score) : String(e[key]), 360, y + 1, { size: 19, fill: '#ffd24a', align: 'right', stroke: OUTL, lw: 4 });
      const sub = key === 'score' ? T('floor') + ' ' + e.floor + ' · ' + T('combo') + ' ' + e.combo
        : key === 'floor' ? T('score') + ' ' + fmt(e.score) : T('score') + ' ' + fmt(e.score);
      text(g, sub, 372, y + 1, { size: 11.5, font: UIF, weight: 700, fill: '#cfc9f0', align: 'left' });
      text(g, fmtDate(e.date), 530, y + 1, { size: 11, font: UIF, weight: 700, fill: '#9a93c4', align: 'right' });
      if (rep) { g.fillStyle = f ? '#ffd24a' : '#8be6ff'; g.beginPath(); g.moveTo(539, y - 6); g.lineTo(551, y + 1); g.lineTo(539, y + 8); g.closePath(); g.fill(); }
    });
    text(g, T('clickWatch'), W / 2, 418, { size: 11.5, font: UIF, weight: 700, fill: '#9a93c4' });
  },
  personal(g, t) {
    const R = Data.records, S = Data.stats, rk = currentRank(R);
    panel(g, 70, 100, 176, 322);
    text(g, T('rank'), 158, 122, { size: 15, font: UIF, weight: 800, fill: '#bfe9ff' });
    drawRankBadge(g, 158, 176, 42, rk, t);
    if (rk < RANKS.length - 1) {
      const nx = RANKS[rk + 1];
      text(g, T('nextRank') + ': ' + rankName(rk + 1), 158, 236, { size: 13, font: UIF, weight: 800, fill: '#ffe9a8' });
      const req = [['req_floor', R.floor, nx.floor], ['req_combo', R.combo, nx.combo], ['req_cc1', R.cc[0], nx.cc1], ['req_nml', R.nml, nx.nml]].filter(r => r[2]);
      let yy = 260;
      for (const [k, have, need] of req) {
        const ok = have >= need;
        const lines = wrapText(g, T(k) + ' ' + need, 140, 12, UIF, 700);
        lines.forEach((ln, j) => text(g, (j === 0 ? (ok ? '✓ ' : '• ') : '   ') + ln, 86, yy + j * 15, { size: 12, font: UIF, weight: 700, fill: ok ? '#8dff6a' : '#e0dbff', align: 'left' }));
        yy += lines.length * 15 + 5;
      }
    } else text(g, '★★★★★', 158, 240, { size: 16, fill: '#ffd24a' });
    panel(g, 258, 100, 312, 322);
    const rows = [
      [T('score'), fmt(R.score)], [T('floor'), String(R.floor)], [T('bestCombo'), String(R.combo)], [T('unfinished'), String(R.unfinished)],
      [T('nml'), String(R.nml)], [T('games'), String(S.games)], [T('totalFloors'), fmt(S.floors)], [T('played'), fmtTime(S.ticks)]
    ];
    rows.forEach((r, i) => {
      const y = 122 + i * 24;
      text(g, r[0], 274, y, { size: 12.5, font: UIF, weight: 800, fill: '#cfc9f0', align: 'left' });
      text(g, r[1], 554, y, { size: 16, fill: '#ffffff', align: 'right' });
    });
    let y = 122 + rows.length * 24 + 4;
    text(g, T('ccTitle'), 274, y, { size: 12, font: UIF, weight: 800, fill: '#bfe9ff', align: 'left' }); y += 20;
    R.cc.forEach((v, i) => { const x = 290 + i * 56; text(g, (i + 1) + '.', x - 8, y, { size: 11, font: UIF, weight: 700, fill: '#9a93c4', align: 'right' }); text(g, String(v), x, y, { size: 15, fill: '#fff', align: 'left' }); });
    y += 24;
    text(g, T('jsTitle'), 274, y, { size: 12, font: UIF, weight: 800, fill: '#bfe9ff', align: 'left' }); y += 20;
    R.js.forEach((v, i) => { const x = 290 + i * 56; text(g, (i + 1) + '×', x - 6, y, { size: 11, font: UIF, weight: 700, fill: '#9a93c4', align: 'right' }); text(g, String(v), x - 2, y, { size: 15, fill: '#fff', align: 'left' }); });
  }
};

// ---------- replays ----------
Screens.replays = {
  sel: 0, scroll: 0, msg: '', msgT: 0,
  list() {
    const arr = [];
    if (Data.last) arr.push({ rep: Data.last, last: true });
    for (const id of Data.saved.slice().reverse()) if (Data.replays[id] && !(Data.last && Data.last.id === id)) arr.push({ rep: Data.replays[id], id });
    return arr;
  },
  enter() { this.sel = 0; this.scroll = 0; UI.reset(0); },
  say(m) { this.msg = m; this.msgT = 2.5; },
  key(nav, ev) {
    const L = this.list();
    if (nav === 'back') { Sound.sfx.back(); App.go('title'); return; }
    if (ev && ev.code === 'KeyC' && L[this.sel]) { this.copy(L[this.sel].rep); return; }
    if (ev && ev.code === 'Delete' && L[this.sel] && !L[this.sel].last) { this.del(L[this.sel].id); return; }
    const vis = Math.min(7, L.length - this.scroll);
    if ((nav === 'down' || nav === 'up') && L.length && UI.focus < vis) {
      if (nav === 'down' && this.sel < L.length - 1) { this.step(1); return; }
      if (nav === 'up' && this.sel > 0) { this.step(-1); return; }
    }
    UI.nav(nav);
  },
  step(d) {
    const n = this.list().length;
    const s = clamp(this.sel + d, 0, Math.max(0, n - 1));
    if (s !== this.sel) { this.sel = s; this.syncF = true; Sound.sfx.move(); }
  },
  wheel(dy) { this.step(dy > 0 ? 1 : -1); },
  copy(rep) { copyReplayCode(rep, ok => this.say(ok ? T('copied') : '')); },
  del(id) { Data.saved = Data.saved.filter(x => x !== id); Data.save('replays'); Sound.sfx.back(); this.say(T('deleted')); this.sel = Math.max(0, this.sel - 1); },
  save(rep) { saveReplay(rep); Sound.sfx.select(); this.say(T('replaySaved')); },
  draw(g, t) {
    menuBackdrop(g, 0.8, t);
    header(g, T('replays'), 34);
    const L = this.list();
    if (this.sel >= L.length) this.sel = Math.max(0, L.length - 1);
    const vis = 7, rh = 38, y0 = 84;
    if (this.sel < this.scroll) this.scroll = this.sel;
    if (this.sel >= this.scroll + vis) this.scroll = this.sel - vis + 1;
    this.scroll = clamp(this.scroll, 0, Math.max(0, L.length - vis));
    if (this.syncF) { UI.focus = this.sel - this.scroll; this.syncF = false; }
    if (!L.length) text(g, T('noReplays'), W / 2, 200, { size: 17, font: UIF, weight: 700, fill: '#cfc9f0', stroke: OUTL, lw: 4 });
    for (let i = this.scroll; i < Math.min(L.length, this.scroll + vis); i++) {
      const e = L[i], rep = e.rep, y = y0 + (i - this.scroll) * rh;
      const f = UI.add({ x: 80, y: y - rh / 2 + 2, w: 480, h: rh - 4, act: () => { Sound.sfx.select(); startReplay(rep, 'replays'); }, onHover: () => { this.sel = i; } });
      if (f) this.sel = i;
      const on = i === this.sel;
      rrect(g, 80, y - rh / 2 + 2, 480, rh - 4, 9);
      g.fillStyle = on ? 'rgba(255,210,74,0.18)' : 'rgba(30,24,60,0.6)'; g.fill();
      g.lineWidth = 1.5; g.strokeStyle = on ? 'rgba(255,210,74,0.75)' : 'rgba(190,180,255,0.25)'; g.stroke();
      g.save(); g.beginPath(); g.rect(84, y - rh / 2 + 3, 30, rh - 6); g.clip();
      drawChar(g, rep.char | 0, { x: 99, y: y + 20, face: 1, state: 'idle', t: t + i, phase: 0, vx: 0, vy: 0, land: 0, spinA: 0, scale: 0.72, combo: false, edgeLocal: 0 });
      g.restore();
      text(g, rep.name || 'PLAYER', 122, y - 6, { size: fitSize(g, rep.name || 'PLAYER', 17, 170), fill: '#ffffff', align: 'left' });
      text(g, (e.last ? T('lastGame') + ' · ' : '') + T('floor') + ' ' + rep.floor + ' · ' + T('combo') + ' ' + rep.combo + ' · ' + fmtDate(rep.date || 0),
        122, y + 10, { size: 11.5, font: UIF, weight: 700, fill: e.last ? '#8be6ff' : '#cfc9f0', align: 'left' });
      text(g, fmt(rep.score), 548, y + 1, { size: 20, fill: '#ffd24a', align: 'right', stroke: OUTL, lw: 4 });
    }
    if (L.length > vis) {
      const top = y0 - rh / 2 + 22, sh = vis * rh - 44, th = Math.max(18, sh * vis / L.length), ty = top + (sh - th) * (this.scroll / (L.length - vis));
      rrect(g, 566, top, 6, sh, 3); g.fillStyle = 'rgba(255,255,255,0.1)'; g.fill();
      rrect(g, 566, ty, 6, th, 3); g.fillStyle = '#8be6ff'; g.fill();
      const arrow = (y, up) => {
        const it = { x: 557, y: y - 11, w: 24, h: 22, noNav: true, act: () => this.step(up ? -1 : 1) };
        UI.add(it);
        g.fillStyle = UI.inside(it, UI.mouse.x, UI.mouse.y) ? '#ffd24a' : '#8be6ff';
        g.beginPath();
        if (up) { g.moveTo(569, y - 6); g.lineTo(577, y + 5); g.lineTo(561, y + 5); } else { g.moveTo(569, y + 6); g.lineTo(577, y - 5); g.lineTo(561, y - 5); }
        g.closePath(); g.fill();
      };
      arrow(y0 - rh / 2 + 9, true);
      arrow(y0 - rh / 2 + vis * rh - 9, false);
    }
    const cur = L[this.sel];
    const by = 358, bw = 114;
    button(g, T('watch'), 80, by, bw, 32, () => { if (cur) { Sound.sfx.select(); startReplay(cur.rep, 'replays'); } }, { disabled: !cur, primary: true });
    button(g, T('copyCode'), 80 + (bw + 8), by, bw, 32, () => { if (cur) this.copy(cur.rep); }, { disabled: !cur, size: 16 });
    if (cur && cur.last) {
      const already = Data.saved.includes(cur.rep.id);
      button(g, already ? T('saved') : T('saveReplay'), 80 + (bw + 8) * 2, by, bw, 32, () => { if (!already) this.save(cur.rep); }, { disabled: already, size: 15 });
    } else button(g, T('del'), 80 + (bw + 8) * 2, by, bw, 32, () => { if (cur) this.del(cur.id); }, { disabled: !cur });
    button(g, T('importCode'), 80 + (bw + 8) * 3, by, bw, 32, () => importReplay(r => { this.sel = 1; this.say(T('imported')); void r; }), { size: 15 });
    if (this.msgT > 0) { this.msgT -= App.dt; text(g, this.msg, W / 2, 408, { size: 15, font: UIF, weight: 800, fill: '#8dff6a', stroke: OUTL, lw: 4 }); }
    button(g, T('back'), W / 2 - 70, 432, 140, 34, () => { Sound.sfx.back(); App.go('title'); });
  }
};

// ---------- trophies ----------
Screens.trophies = {
  enter() { UI.reset(0); },
  key(nav) { if (nav === 'back' || nav === 'ok') { Sound.sfx.back(); App.go('title'); } },
  draw(g, t) {
    menuBackdrop(g, 0.82, t);
    header(g, T('trophies'), 32);
    const got = ACH.filter(a => Data.ach[a.id]).length;
    text(g, got + ' / ' + ACH.length + ' ' + T('achCount'), W / 2, 60, { size: 13, font: UIF, weight: 800, fill: '#ffe9a8' });
    const rows = Math.ceil(ACH.length / 2), rh = 25.5, y0 = 86;
    ACH.forEach((a, i) => {
      const col = i < rows ? 0 : 1, row = i < rows ? i : i - rows;
      const x = col ? 332 : 50, y = y0 + row * rh, has = !!Data.ach[a.id];
      rrect(g, x, y - rh / 2 + 1.5, 258, rh - 3, 7);
      g.fillStyle = has ? 'rgba(255,210,74,0.14)' : 'rgba(20,16,44,0.6)'; g.fill();
      drawTrophyIcon(g, x + 14, y + 0.5, 0.72, has);
      text(g, TT(a.n), x + 29, y - 5, { size: 12.5, fill: has ? '#ffe9a8' : '#a6a0cc', align: 'left' });
      text(g, TT(a.d), x + 29, y + 7, { size: fitSize(g, TT(a.d), 10.5, 222, UIF, 700), font: UIF, weight: 700, fill: has ? '#e8e4ff' : '#817ba8', align: 'left' });
    });
    button(g, T('back'), W / 2 - 60, 446, 120, 28, () => { Sound.sfx.back(); App.go('title'); }, { size: 16 });
  }
};

// ---------- help ----------
Screens.help = {
  enter() { UI.reset(0); },
  key(nav) { if (nav === 'back' || nav === 'ok') { Sound.sfx.back(); App.go('title'); } },
  draw(g, t) {
    menuBackdrop(g, 0.84, t);
    header(g, T('help'), 32);
    const entries = HELP[settings.lang];
    let size = 13.5, blocks;
    for (;;) {
      blocks = entries.map(e => wrapText(g, e[1], 400, size, UIF, 700));
      const hgt = blocks.reduce((s, b) => s + b.length * (size + 3.5) + 9, 0);
      if (hgt < 356 || size <= 10.5) break;
      size -= 0.5;
    }
    let y = 66;
    entries.forEach((e, i) => {
      text(g, e[0], 150, y + size / 2 + 1, { size: 15, fill: ['#8be6ff', '#ffd24a', '#8dff6a', '#ff9f43', '#ff7ad9', '#ff6b6b', '#c7a4ff'][i % 7], align: 'right', stroke: OUTL, lw: 4 });
      blocks[i].forEach((ln, j) => text(g, ln, 162, y + size / 2 + 1 + j * (size + 3.5), { size, font: UIF, weight: 700, fill: '#ebe6ff', align: 'left' }));
      y += blocks[i].length * (size + 3.5) + 9;
    });
    button(g, T('back'), W / 2 - 60, 440, 120, 30, () => { Sound.sfx.back(); App.go('title'); }, { size: 16 });
  }
};

// ---------- the game ----------
Screens.play = {
  enter(opts) { if (!(opts && opts.keep)) UI.reset(0); },
  tick() { tickPlay(); },
  key(nav, ev) {
    const s = App.sess;
    if (!s) return;
    if (s.state === 'run') { if (Input.isPause(ev.code)) pauseGame(); return; }
    if (s.state === 'pause') {
      if (nav === 'back' || Input.isPause(ev.code)) resumeGame(); else UI.nav(nav);
      return;
    }
    if (s.state === 'over') {
      if (NameBox.open) return;
      if (!s.showResults) { if (nav === 'ok' || nav === 'back') s.deadT = Math.max(s.deadT, 99); return; }
      if (App.time - s.resultsAt < 0.5) return;
      if (nav === 'back') quitToMenu(); else UI.nav(nav);
    }
  },
  drawGame(g, t, a) {
    const s = App.sess, G = s.g;
    g.save();
    if (View.shake > 0.15 && settings.shake) g.translate(rand(-1, 1) * View.shake, rand(-1, 1) * View.shake);
    const w = drawWorld(g, G, a, { char: s.char, style: settings.style, time: t });
    View.zb = w.zb;
    g.restore();
    drawVignette(g);
    FX.draw(g, 0, 3);
    drawHUD(g, G, a, { time: t });
    Pops.draw(g, t);
    if (View.flash > 0.01) { g.globalAlpha = View.flash; g.fillStyle = View.flashCol; g.fillRect(0, 0, W, H); g.globalAlpha = 1; }
  },
  draw(g, t, a) {
    const s = App.sess;
    if (!s) return;
    this.drawGame(g, t, s.state === 'pause' ? 1 : a);
    if (s.state === 'run') {
      const it = { x: 600, y: 8, w: 32, h: 32, act: pauseGame, noNav: true };
      UI.add(it);
      drawPauseButton(g, 601, 9, UI.inside(it, UI.mouse.x, UI.mouse.y));
    } else if (s.state === 'pause') this.pauseMenu(g, t);
    else if (s.state === 'over' && s.showResults) this.results(g, t);
  },
  pauseMenu(g, t) {
    g.fillStyle = 'rgba(8,6,20,0.7)'; g.fillRect(0, 0, W, H);
    header(g, T('paused'), 118);
    const bx = W / 2 - 115;
    button(g, T('resume'), bx, 164, 230, 36, resumeGame, { primary: true });
    button(g, T('restart'), bx, 210, 230, 36, () => { Sound.sfx.select(); startGame(); });
    button(g, T('options'), bx, 256, 230, 36, () => { Sound.sfx.select(); App.go('options', { from: 'pause' }); });
    button(g, T('quit'), bx, 302, 230, 36, quitToMenu);
    if (!touchMode()) text(g, T('hintKeys'), W / 2, 372, { size: 12.5, font: UIF, weight: 700, fill: 'rgba(230,225,255,0.7)' });
  },
  results(g, t) {
    const s = App.sess, r = s.results;
    const k = ease.outCubic(clamp((App.time - s.resultsAt) / 0.4, 0, 1));
    g.fillStyle = 'rgba(8,6,20,' + (0.62 * k).toFixed(3) + ')'; g.fillRect(0, 0, W, H);
    g.save(); g.translate(0, (1 - k) * 40); g.globalAlpha = k;
    const gr = g.createLinearGradient(0, 22, 0, 70);
    gr.addColorStop(0, '#ffd0d0'); gr.addColorStop(0.5, '#ff4a4a'); gr.addColorStop(1, '#a3122a');
    text(g, 'GAME OVER', W / 2, 46, { size: 48, fill: gr, stroke: '#1a0710', lw: 10 });
    panel(g, 110, 76, 420, 316);
    text(g, T('score'), W / 2, 98, { size: 14, font: UIF, weight: 800, fill: '#ffe9a8' });
    const sgr = g.createLinearGradient(0, 108, 0, 148);
    sgr.addColorStop(0, '#ffffff'); sgr.addColorStop(1, '#ffd24a');
    text(g, fmt(r.score), W / 2, 128, { size: 42, fill: sgr, stroke: OUTL, lw: 8 });
    const stats = [
      ['floor', String(r.floor), r.newRec.includes('floor')], ['bestCombo', String(r.combo), r.newRec.includes('combo')],
      ['time', fmtTime(r.time), false], ['jumps', String(r.jumps), false]
    ];
    stats.forEach((st, i) => {
      const x = i % 2 ? 340 : 132, y = 170 + Math.floor(i / 2) * 36;
      text(g, T(st[0]), x, y, { size: 13, font: UIF, weight: 800, fill: '#cfc9f0', align: 'left' });
      text(g, st[1], x + 176, y, { size: 19, fill: '#ffffff', align: 'right' });
      if (st[2]) text(g, '▲ ' + T('newRecord'), x + 176, y + 15, { size: 9.5, font: UIF, weight: 800, fill: '#8dff6a', align: 'right' });
    });
    if (r.newRec.includes('score')) text(g, '▲ ' + T('newRecord'), W / 2, 151, { size: 10.5, font: UIF, weight: 800, fill: '#8dff6a' });
    let y = 246;
    if (r.rankAfter > r.rankBefore) {
      text(g, T('rankUp'), W / 2 - 18, y, { size: 18, fill: '#8dff6a', stroke: OUTL, lw: 5 });
      drawRankBadge(g, W / 2 + textW(g, T('rankUp'), 18) / 2 + 2, y - 1, 13, r.rankAfter, t);
      y += 28;
    }
    if (s.qual.length) {
      const pulse = 1 + Math.sin(t * 6) * 0.04;
      g.save(); g.translate(W / 2, y); g.scale(pulse, pulse);
      text(g, T('newHigh'), 0, 0, { size: 22, fill: '#ffd24a', stroke: OUTL, lw: 6 });
      g.restore();
      y += 22;
      if (!s.nameDone) {
        text(g, T('enterName'), W / 2, y + 2, { size: 11.5, font: UIF, weight: 800, fill: '#cfc9f0' });
        NameBox.place(210, y + 12, 160, 32);
        button(g, T('ok'), 378, y + 12, 52, 32, () => NameBox.commit(), { primary: true, size: 16 });
        y += 50;
      } else {
        text(g, s.results.name, W / 2, y + 8, { size: 20, fill: '#ffffff', stroke: OUTL, lw: 5 });
        y += 30;
      }
    }
    if (s.newAch.length) {
      text(g, T('newTrophies'), W / 2, y + 6, { size: 11.5, font: UIF, weight: 800, fill: '#ffe9a8' });
      const names = s.newAch.map(id => TT(ACH.find(a => a.id === id).n));
      const line = names.slice(0, 3).join(' · ') + (names.length > 3 ? ' +' + (names.length - 3) : '');
      text(g, line, W / 2, y + 24, { size: fitSize(g, line, 14, 390), fill: '#ffffff' });
    }
    g.restore();
    const by = 404, bw = 96, gap = 8, bx = W / 2 - (bw * 4 + gap * 3) / 2;
    const blocked = s.qual.length && !s.nameDone;
    button(g, T('playAgain'), bx, by, bw, 36, () => { Sound.sfx.select(); startGame(); }, { primary: true, size: 15, disabled: blocked });
    button(g, T('watchReplay'), bx + (bw + gap), by, bw, 36, () => { Sound.sfx.select(); startReplay(s.replay, 'over'); }, { size: 14, disabled: blocked });
    const saved = Data.saved.includes(s.replay.id);
    button(g, saved ? T('saved') : T('saveReplay'), bx + (bw + gap) * 2, by, bw, 36, () => { if (!saved) { saveReplay(s.replay); Sound.sfx.select(); } }, { size: 14, disabled: blocked || saved });
    button(g, T('menu'), bx + (bw + gap) * 3, by, bw, 36, quitToMenu, { size: 15, disabled: blocked });
  }
};

// ---------- replay viewer ----------
const RP_SPEEDS = [0.25, 0.5, 1, 2, 4, 8];
Screens.replay = {
  enter() { UI.reset(0); },
  tick() {},
  key(nav, ev) {
    const rp = App.rp;
    if (!rp) return;
    if (rp.ended) { if (nav === 'back') exitReplay(); else UI.nav(nav); return; }
    if (nav === 'back') { exitReplay(); return; }
    if (ev.code === 'Space' || ev.code === 'Enter' || ev.code === 'KeyP') { rp.paused = !rp.paused; Sound.sfx.move(); }
    else if (nav === 'left') rpSeek(rp, rp.g.tick - 300);
    else if (nav === 'right') rpSeek(rp, rp.g.tick + 300);
    else if (nav === 'up') { rp.si = Math.min(RP_SPEEDS.length - 1, rp.si + 1); Sound.sfx.move(); }
    else if (nav === 'down') { rp.si = Math.max(0, rp.si - 1); Sound.sfx.move(); }
  },
  draw(g, t, a) {
    const rp = App.rp;
    if (!rp) return;
    const G = rp.g;
    g.save();
    if (View.shake > 0.15 && settings.shake) g.translate(rand(-1, 1) * View.shake, rand(-1, 1) * View.shake);
    const w = drawWorld(g, G, rp.paused ? 1 : a, { char: rp.rep.char | 0, style: settings.style, time: t });
    View.zb = w.zb;
    g.restore();
    drawVignette(g);
    FX.draw(g, 0, 3);
    drawHUD(g, G, rp.paused ? 1 : a, { time: t });
    Pops.draw(g, t);
    if (View.flash > 0.01) { g.globalAlpha = View.flash; g.fillStyle = View.flashCol; g.fillRect(0, 0, W, H); g.globalAlpha = 1; }
    // top bar
    const bx = 84, by = 8, bw = 472, bh = 34, live = !rp.ended;
    const hov = it => UI.inside(it, UI.mouse.x, UI.mouse.y);
    rrect(g, bx, by, bw, bh, 10); g.fillStyle = 'rgba(12,9,28,0.85)'; g.fill(); g.lineWidth = 2; g.strokeStyle = 'rgba(190,180,255,0.4)'; g.stroke();
    const pIt = { x: bx + 4, y: by + 3, w: 30, h: 28, act: () => { rp.paused = !rp.paused; }, noNav: true };
    if (live) UI.add(pIt);
    rrect(g, bx + 5, by + 4, 28, 26, 7); g.fillStyle = hov(pIt) ? 'rgba(255,210,74,0.3)' : 'rgba(255,255,255,0.08)'; g.fill();
    g.fillStyle = '#fff';
    if (rp.paused || rp.ended) { g.beginPath(); g.moveTo(bx + 15, by + 10); g.lineTo(bx + 26, by + 17); g.lineTo(bx + 15, by + 24); g.closePath(); g.fill(); }
    else { g.fillRect(bx + 13, by + 10, 4, 14); g.fillRect(bx + 21, by + 10, 4, 14); }
    const sIt = { x: bx + 38, y: by + 3, w: 44, h: 28, act: () => { rp.si = (rp.si + 1) % RP_SPEEDS.length; }, noNav: true };
    if (live) UI.add(sIt);
    rrect(g, bx + 38, by + 4, 44, 26, 7); g.fillStyle = hov(sIt) ? 'rgba(255,210,74,0.3)' : 'rgba(255,255,255,0.08)'; g.fill();
    const sp = RP_SPEEDS[rp.si];
    text(g, (sp < 1 ? (sp === 0.5 ? '½' : '¼') : sp) + '×', bx + 60, by + 18, { size: 15, fill: sp === 1 ? '#fff' : '#ffd24a' });
    const px = bx + 90, pw = 250, py = by + 17;
    const total = Math.max(1, rp.inputs.length);
    if (live) UI.add({ x: px - 4, y: by, w: pw + 8, h: bh, click: lx => rpSeek(rp, Math.round(clamp((lx - 4) / pw, 0, 1) * total)), noNav: true });
    rrect(g, px, py - 4, pw, 8, 4); g.fillStyle = 'rgba(255,255,255,0.14)'; g.fill();
    const fr = clamp(G.tick / total, 0, 1);
    rrect(g, px, py - 4, Math.max(8, pw * fr), 8, 4); g.fillStyle = '#8be6ff'; g.fill();
    circ(g, px + pw * fr, py, 6.5); g.fillStyle = '#ffffff'; g.fill(); g.lineWidth = 2; g.strokeStyle = OUTL; g.stroke();
    text(g, fmtTime(Math.min(G.tick, total)) + ' / ' + fmtTime(total), bx + bw - 60, by + 18, { size: 12.5, font: UIF, weight: 800, fill: '#e0dbff' });
    text(g, T('replay') + ' · ' + (rp.rep.name || 'PLAYER') + ' · ' + fmt(rp.rep.score), W / 2, by + bh + 13, { size: 13, font: UIF, weight: 800, fill: '#ffe9a8', stroke: OUTL, lw: 4 });
    // pressed keys
    const bits = G.tick > 0 && G.tick <= rp.inputs.length ? rp.inputs[G.tick - 1] : 0;
    const keys = [[1, 'L'], [4, 'J'], [2, 'R']];
    keys.forEach(([m, kk], i) => {
      const x = W / 2 - 50 + i * 36, y = 446, on = (bits & m) !== 0;
      rrect(g, x, y, 30, 26, 6); g.fillStyle = on ? '#ffd24a' : 'rgba(12,9,28,0.75)'; g.fill(); g.lineWidth = 1.5; g.strokeStyle = 'rgba(255,255,255,0.5)'; g.stroke();
      g.fillStyle = on ? '#2a1d04' : '#cfc9f0';
      g.beginPath();
      if (kk === 'L') { g.moveTo(x + 19, y + 6); g.lineTo(x + 10, y + 13); g.lineTo(x + 19, y + 20); }
      else if (kk === 'R') { g.moveTo(x + 11, y + 6); g.lineTo(x + 20, y + 13); g.lineTo(x + 11, y + 20); }
      else { g.moveTo(x + 8, y + 18); g.lineTo(x + 15, y + 7); g.lineTo(x + 22, y + 18); }
      g.closePath(); g.fill();
    });
    if (!rp.ended) text(g, T('replayHelp'), W / 2, 434, { size: 10.5, font: UIF, weight: 700, fill: 'rgba(230,225,255,0.65)', stroke: OUTL, lw: 3 });
    if (rp.ended) {
      g.fillStyle = 'rgba(8,6,20,0.6)'; g.fillRect(0, 0, W, H);
      panel(g, 170, 150, 300, 170);
      text(g, T('endReplay'), W / 2, 180, { size: 26, fill: '#ffffff', stroke: OUTL, lw: 6 });
      text(g, fmt(gameScore(G)), W / 2, 214, { size: 30, fill: '#ffd24a', stroke: OUTL, lw: 6 });
      const okv = gameScore(G) === rp.rep.score;
      text(g, (okv ? '✓ ' : '! ') + T(okv ? 'verified' : 'desync'), W / 2, 242, { size: 12.5, font: UIF, weight: 800, fill: okv ? '#8dff6a' : '#ff8a8a' });
      button(g, T('again'), 188, 268, 128, 34, () => { Sound.sfx.select(); rpSeek(rp, 0); rp.ended = false; rp.paused = false; }, { primary: true, size: 16 });
      button(g, T('back'), 324, 268, 128, 34, exitReplay, { size: 16 });
    }
  }
};
// ===================== app controller, sessions, replays, trophies, boot =====================
const canvas = document.getElementById('game');
const ctx = canvas.getContext('2d');
const stage = document.getElementById('stage');
const appEl = document.getElementById('app');
const modalEl = document.getElementById('modal');
const STEP = 1 / 60;
const COARSE = (() => { try { return window.matchMedia('(pointer: coarse)').matches; } catch (e) { return false; } })();
const view = { cssW: 0, cssH: 0, cssScale: 1, scale: 1 };

const ACH = [
  { id: 'f10', n: ['Warm-up', 'Isınma'], d: ['Reach floor 10', '10. kata çık'], live: g => g.best >= 10 },
  { id: 'f50', n: ['Climber', 'Tırmanıcı'], d: ['Reach floor 50', '50. kata çık'], live: g => g.best >= 50 },
  { id: 'f100', n: ['Century', 'Yüzlük'], d: ['Reach floor 100', '100. kata çık'], live: g => g.best >= 100 },
  { id: 'f250', n: ['High Flyer', 'Yüksek Uçuş'], d: ['Reach floor 250', '250. kata çık'], live: g => g.best >= 250 },
  { id: 'f500', n: ['Stratosphere', 'Stratosfer'], d: ['Reach floor 500', '500. kata çık'], live: g => g.best >= 500 },
  { id: 'f1000', n: ['Top of the World', 'Dünyanın Tepesi'], d: ['Reach floor 1000', '1000. kata çık'], live: g => g.best >= 1000 }
].concat(TIERS.map((tr, i) => ({
  id: 'c' + i, n: [tr.w, tr.w], d: ['Finish a combo of ' + tr.n + '+ floors', tr.n + '+ katlık bir kombo bitir'],
  live: g => { for (let k = i; k < g.st.tiers.length; k++) if (g.st.tiers[k] > 0) return true; return false; }
}))).concat([
  { id: 'clock', n: ['Clockwork', 'Saat Gibi'], d: ['Survive until the clock breaks', 'Saat bozulana kadar dayan'], live: g => g.cam.broken },
  { id: 's10k', n: ['Five Digits', 'Beş Hane'], d: ['Score 10,000 in one game', 'Bir oyunda 10.000 puan yap'], live: g => gameScore(g) >= 10000 },
  { id: 's50k', n: ['Big Shot', 'Büyük Oyuncu'], d: ['Score 50,000 in one game', 'Bir oyunda 50.000 puan yap'], live: g => gameScore(g) >= 50000 },
  { id: 's100k', n: ['Six Digits', 'Altı Hane'], d: ['Score 100,000 in one game', 'Bir oyunda 100.000 puan yap'], live: g => gameScore(g) >= 100000 },
  { id: 'wall3', n: ['Pinball', 'Langırt'], d: ['Bounce off the walls 3 times in one jump', 'Tek zıplamada 3 kez duvardan sek'], live: g => g.st.maxAir >= 3 },
  { id: 'nml100', n: ['Purist', 'Saf Tırmanış'], d: ['Reach floor 100 without finishing a combo', 'Hiç kombo bitirmeden 100. kata çık'], live: g => g.st.combos === 0 && g.best >= 100 },
  { id: 'cc55', n: ['Quick Start', 'Hızlı Başlangıç'], d: ['Reach floor 55 before the clock first rings', 'Saat ilk kez çalmadan 55. kata çık'], live: g => g.cam.revs === 0 && g.best >= 55 },
  { id: 'js10', n: ['Metronome', 'Metronom'], d: ['Make 10 two-floor jumps in a row', 'Arka arkaya 10 kez ikişer kat zıpla'], live: g => g.st.js[1] >= 10 },
  { id: 'games25', n: ['Regular', 'Müdavim'], d: ['Play 25 games', '25 oyun oyna'], end: () => Data.stats.games >= 25 },
  { id: 'allchars', n: ['Dress-up', 'Kostüm Partisi'], d: ['Finish a game with every climber', 'Her karakterle bir oyun bitir'], end: () => Data.stats.chars.length >= 4 },
  { id: 'watch', n: ['Director’s Cut', 'Yönetmen Kurgusu'], d: ['Watch a replay', 'Bir tekrar izle'] },
  { id: 'rankC', n: ['Ranked', 'Rütbeli'], d: ['Reach rank C', 'C rütbesine ulaş'], end: () => currentRank(Data.records) >= 3 }
]);
function unlock(id) {
  if (Data.ach[id]) return;
  const a = ACH.find(x => x.id === id);
  if (!a) return;
  Data.ach[id] = Date.now();
  Data.save('ach');
  Pops.add({ t: 'toast', dur: 3.2, id });
  Sound.sfx.trophy();
  if (App.sess && App.screen === 'play') App.sess.newAch.push(id);
}
function checkAch(g, end) {
  for (const a of ACH) {
    if (Data.ach[a.id]) continue;
    if ((a.live && a.live(g)) || (end && a.end && a.end(g))) unlock(a.id);
  }
}

const App = {
  screen: 'title', time: 0, dt: 0, alpha: 0, fade: 0, titleFocus: 0,
  attract: null, sess: null, rp: null, askBox: null, flashMsg: '', flashMsgT: 0,
  go(name, opts) {
    if (NameBox.open) NameBox.commit();
    this.screen = name;
    const s = Screens[name];
    if (s && s.enter) s.enter(opts);
    this.fade = 0.5;
    this.ensureMusic();
  },
  ask(msg, yes) { this.askBox = { text: msg, yes }; UI.reset(1); Sound.sfx.move(); },
  ensureMusic() {
    if (!Sound.ready) return;
    const s = this.sess;
    const inGame = (this.screen === 'play' && s && s.state !== 'over') || this.screen === 'replay';
    if (this.screen === 'play' && s && s.state === 'over' && !s.showResults) { Sound.music.stop(); return; }
    Sound.music.start(inGame ? 'game' : 'menu');
    if (inGame) Sound.music.level(this.screen === 'replay' && this.rp ? this.rp.g.cam.level : s ? s.g.cam.level : 1);
  }
};
function flashMsg(m) { App.flashMsg = m; App.flashMsgT = 2.5; }
function setLang(l) { settings.lang = l ? 1 : 0; saveSettings(); Sound.sfx.move(); document.documentElement.lang = l ? 'tr' : 'en'; }
function isFullscreen() { return !!(document.fullscreenElement || document.webkitFullscreenElement); }
function toggleFullscreen() {
  try {
    if (isFullscreen()) { (document.exitFullscreen || document.webkitExitFullscreen).call(document); return; }
    const el = document.documentElement, req = el.requestFullscreen || el.webkitRequestFullscreen;
    if (!req) { flashMsg(T('noFs')); return; }
    const p = req.call(el);
    if (p && p.catch) p.catch(() => flashMsg(T('noFs')));
  } catch (e) { flashMsg(T('noFs')); }
}
let wakeLock = null;
function requestWakeLock() {
  try {
    if (navigator.wakeLock && !wakeLock) navigator.wakeLock.request('screen').then(l => { wakeLock = l; l.addEventListener('release', () => { wakeLock = null; }); }).catch(() => {});
  } catch (e) { /* not available */ }
}
function resetView() {
  FX.clear(); Pops.clear();
  Object.assign(View, { shake: 0, flash: 0, ringT: 0, comboPulse: 0, cheerTick: -999, shownScore: 0 });
}

// ---------- name box (HTML input over the canvas) ----------
const NameBox = (() => {
  const el = document.getElementById('nameInput');
  let onCommit = null, rect = null;
  el.addEventListener('keydown', e => {
    e.stopPropagation();
    if (e.key === 'Enter' || e.key === 'Escape') { e.preventDefault(); commit(); }
  });
  function position() {
    if (!rect || el.hidden) return;
    const [x, y, w, h] = rect;
    el.style.left = (x / W * 100) + '%'; el.style.top = (y / H * 100) + '%';
    el.style.width = (w / W * 100) + '%'; el.style.height = (h / H * 100) + '%';
    el.style.fontSize = Math.max(12, Math.round(h * 0.56 * view.cssScale)) + 'px';
  }
  function show(value, cb) {
    onCommit = cb; el.value = value || ''; el.hidden = false; position();
    setTimeout(() => { try { el.focus({ preventScroll: true }); el.select(); } catch (e) { /* ignore */ } }, 40);
  }
  function place(x, y, w, h) {
    if (rect && rect[0] === x && rect[1] === y && rect[2] === w && rect[3] === h) return;
    rect = [x, y, w, h]; position();
  }
  function close() { el.hidden = true; rect = null; try { el.blur(); } catch (e) { /* ignore */ } }
  function commit() {
    if (el.hidden) return;
    const v = el.value, cb = onCommit;
    onCommit = null; close();
    try { canvas.focus({ preventScroll: true }); } catch (e) { /* ignore */ }
    if (cb) cb(v);
  }
  return { show, place, commit, close, reposition: () => position(), get open() { return !el.hidden; } };
})();
function cleanName(n) {
  n = String(n || '').replace(/[\u0000-\u001f<>]/g, '').trim();
  n = (settings.lang === 1 ? n.toLocaleUpperCase('tr-TR') : n.toUpperCase()).slice(0, 12);
  return n || 'PLAYER';
}
function editPlayerName(y) {
  Screens.options.nameY = y;
  NameBox.show(settings.name, v => { settings.name = cleanName(v); saveSettings(); Sound.sfx.select(); });
}

// ---------- modal (import / export replay codes) ----------
const Modal = (() => {
  const title = document.getElementById('modalTitle'), txt = document.getElementById('modalText');
  const box = document.getElementById('codeBox'), ok = document.getElementById('modalOk'), cancel = document.getElementById('modalCancel');
  let onOk = null;
  function open(o) {
    title.textContent = o.title; txt.textContent = o.text; txt.className = '';
    box.value = o.code || ''; box.readOnly = !!o.readOnly;
    ok.textContent = o.ok || ''; ok.hidden = !o.ok; cancel.textContent = o.cancel;
    onOk = o.onOk || null;
    modalEl.hidden = false;
    Input.clearKeys();
    setTimeout(() => { try { box.focus(); if (o.readOnly) box.select(); } catch (e) { /* ignore */ } }, 40);
  }
  function close() { modalEl.hidden = true; onOk = null; try { canvas.focus({ preventScroll: true }); } catch (e) { /* ignore */ } }
  ok.addEventListener('click', () => { if (onOk) onOk(box.value); });
  cancel.addEventListener('click', () => { Sound.sfx.back(); close(); });
  modalEl.addEventListener('keydown', e => { e.stopPropagation(); if (e.key === 'Escape') close(); });
  modalEl.addEventListener('pointerdown', e => { if (e.target === modalEl) close(); });
  return { open, close, error(m) { txt.textContent = m; txt.className = 'err'; } };
})();
function copyReplayCode(rep, cb) {
  const code = replayToCode(rep);
  const fallback = () => { Modal.open({ title: T('exportTitle'), text: T('exportText'), code, readOnly: true, cancel: T('close') }); cb(false); };
  try {
    if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(code).then(() => { Sound.sfx.select(); cb(true); }, fallback);
    else fallback();
  } catch (e) { fallback(); }
}
function trimSaved() { while (Data.saved.length > 30) Data.saved.shift(); }
function saveReplay(rep) {
  if (!rep.id) rep.id = 'r' + Date.now().toString(36);
  Data.replays[rep.id] = rep;
  if (!Data.saved.includes(rep.id)) Data.saved.push(rep.id);
  trimSaved();
  Data.save('replays');
}
function importReplay(done) {
  Modal.open({
    title: T('importTitle'), text: T('importText'), code: '', ok: T('load'), cancel: T('cancel'),
    onOk: v => {
      try {
        const rep = replayFromCode(v);
        rep.id = 'i' + Date.now().toString(36) + Math.floor(Math.random() * 1296).toString(36);
        saveReplay(rep);
        Modal.close(); Sound.sfx.select(); done(rep);
      } catch (e) { Modal.error(T('badCode')); Sound.sfx.back(); }
    }
  });
}

// ---------- attract mode (bot plays behind the menus) ----------
function newAttract() { return { g: newGame((Math.random() * 4294967296) >>> 0, true), mem: { skill: 0.9 }, char: settings.char, deadT: 0 }; }
function tickAttract() {
  const at = App.attract, g = at.g;
  at.char = settings.char;
  stepGame(g, Bot.think(g, at.mem));
  for (const e of g.ev) onSimEvent(e, g, 'attract');
  g.ev.length = 0;
  simTickFX(g);
  if (g.state === 'dead' && ++at.deadT > 80) { App.attract = newAttract(); FX.clear(); }
}

// ---------- a game session ----------
function startGame() {
  NameBox.close();
  App.sess = {
    g: newGame((Math.random() * 4294967296) >>> 0, settings.rejump), rec: [], char: settings.char, state: 'run', deadT: 0, maskJump: true,
    id: 'g' + Date.now().toString(36) + Math.floor(Math.random() * 1296).toString(36),
    newAch: [], results: null, showResults: false, qual: [], nameDone: false, replay: null, resultsAt: 0
  };
  resetView();
  Sound.setDuck(1);
  Input.resetTouch();
  App.go('play');
  requestWakeLock();
}
function tickPlay() {
  const s = App.sess;
  if (!s || s.state === 'pause') return;
  const g = s.g;
  let bits = 0;
  if (g.state === 'play') {
    bits = Input.bits();
    if (s.maskJump) { if (bits & 4) bits &= 3; else s.maskJump = false; }
    s.rec.push(bits);
  }
  stepGame(g, bits);
  for (const e of g.ev) onSimEvent(e, g, 'live');
  g.ev.length = 0;
  simTickFX(g);
  if (g.state === 'play') { if (g.tick % 6 === 0) checkAch(g); return; }
  if (s.state === 'run') { s.state = 'over'; checkAch(g); Sound.music.stop(); Input.resetTouch(); }
  s.deadT++;
  if (s.deadT === 28) Pops.add({ t: 'gameover', dur: 60 });
  if (s.deadT >= 100 && !s.showResults) finishGame();
}
function qualifies(k, v) { const L = Data.scores[k]; return v > 0 && (L.length < 10 || v > L[L.length - 1][k]); }
function finishGame() {
  const s = App.sess, g = s.g;
  const score = gameScore(g), rankBefore = currentRank(Data.records);
  const rep = {
    v: SIM_VERSION, id: s.id, seed: g.seed, rejump: g.rejump, char: s.char, name: settings.name || 'PLAYER', date: Date.now(),
    score, floor: g.best, combo: g.st.bestCombo, ticks: s.rec.length, input: encodeInputs(s.rec)
  };
  s.replay = rep;
  Data.last = rep; Data.save('last');
  const S = Data.stats;
  S.games++; S.floors += g.best; S.jumps += g.st.jumps; S.ticks += g.tick; S.combos += g.st.combos; S.bounces += g.st.bounces;
  if (!S.chars.includes(s.char)) S.chars.push(s.char);
  const R = Data.records, newRec = [];
  const up = (k, v) => { if (v > R[k]) { R[k] = v; newRec.push(k); } };
  up('score', score); up('floor', g.best); up('combo', g.st.bestCombo); up('unfinished', g.st.unfinished); up('nml', g.st.nml); up('level', g.cam.level);
  for (let i = 0; i < 5; i++) { R.cc[i] = Math.max(R.cc[i], g.st.cc[i]); R.js[i] = Math.max(R.js[i], g.st.js[i]); }
  Data.save('stats', 'records');
  checkAch(g, true);
  s.qual = ['score', 'floor', 'combo'].filter(k => qualifies(k, k === 'score' ? score : k === 'floor' ? g.best : g.st.bestCombo));
  s.results = { score, floor: g.best, combo: g.st.bestCombo, time: g.tick, jumps: g.st.jumps, newRec, rankBefore, rankAfter: currentRank(R), name: settings.name || 'PLAYER' };
  s.showResults = true; s.resultsAt = App.time;
  Pops.clear();
  Pops.toasts.length = 0;
  UI.reset(0);
  if (s.qual.length) { Sound.sfx.fanfare(); NameBox.show(settings.name, commitHighscore); }
  App.ensureMusic();
}
function commitHighscore(v) {
  const s = App.sess;
  if (!s || s.nameDone) return;
  const name = cleanName(v);
  settings.name = name; saveSettings();
  const rep = s.replay;
  rep.name = name;
  Data.replays[rep.id] = rep;
  Data.last = rep;
  const entry = { name, score: s.results.score, floor: s.results.floor, combo: s.results.combo, date: rep.date, char: s.char, rid: rep.id, time: s.results.time };
  for (const k of s.qual) {
    const L = Data.scores[k];
    L.push(Object.assign({}, entry));
    L.sort((a, b) => b[k] - a[k] || a.date - b.date);
    if (L.length > 10) L.length = 10;
  }
  Data.save('scores', 'replays', 'last');
  s.nameDone = true; s.results.name = name;
  UI.reset(0);
  Sound.sfx.select();
}
function pauseGame() {
  const s = App.sess;
  if (!s || s.state !== 'run') return;
  s.state = 'pause';
  Sound.setDuck(0.3); Sound.sfx.select();
  UI.reset(0); Input.resetTouch();
}
function resumeGame() {
  const s = App.sess;
  if (!s || s.state !== 'pause') return;
  s.state = 'run'; s.maskJump = true;
  Sound.setDuck(1); Sound.sfx.select();
  Input.clearKeys();
}
function quitToMenu() {
  NameBox.close();
  App.sess = null;
  resetView();
  Pops.toasts.length = 0;
  Sound.setDuck(1); Sound.sfx.back();
  App.go('title');
}

// ---------- replay player ----------
function startReplay(rep, from) {
  if (!validReplay(rep)) return;
  NameBox.close();
  const g = newGame(rep.seed, rep.rejump);
  App.rp = { rep, inputs: decodeInputs(rep.input), g, snaps: [cloneGame(g)], si: 2, paused: false, ended: false, from, acc: 0 };
  resetView();
  Data.stats.watched++; Data.save('stats');
  unlock('watch');
  App.go('replay');
}
function rpStep(rp, fx) {
  const g = rp.g;
  if (g.state === 'play' && g.tick >= rp.inputs.length) { if (!rp.ended) { rp.ended = true; UI.reset(0); Pops.clear(); } return; }
  stepGame(g, g.tick < rp.inputs.length ? rp.inputs[g.tick] : 0);
  if (fx) {
    const mode = RP_SPEEDS[rp.si] <= 2 ? 'replay' : 'fast';
    for (const e of g.ev) onSimEvent(e, g, mode);
    simTickFX(g);
  }
  g.ev.length = 0;
  if (g.tick % 300 === 0 && g.tick / 300 === rp.snaps.length) rp.snaps.push(cloneGame(g));
  if (g.state === 'dead' && g.tick - g.deadTick > 100 && !rp.ended) { rp.ended = true; UI.reset(0); Pops.clear(); }
}
function rpSeek(rp, tick) {
  tick = clamp(Math.round(tick), 0, rp.inputs.length);
  const si = Math.min(rp.snaps.length - 1, Math.floor(tick / 300));
  if (tick < rp.g.tick || si * 300 > rp.g.tick) rp.g = cloneGame(rp.snaps[si]);
  while (rp.g.tick < tick && rp.g.state === 'play') rpStep(rp, false);
  rp.ended = false; rp.acc = 0;
  resetView();
  View.shownScore = gameScore(rp.g);
  Sound.music.level(rp.g.cam.level);
}
function exitReplay() {
  const rp = App.rp;
  App.rp = null;
  resetView();
  Sound.sfx.back();
  if (rp && rp.from === 'over' && App.sess && App.sess.state === 'over') App.go('play', { keep: true });
  else App.go(rp && rp.from === 'scores' ? 'scores' : 'replays');
}

// ---------- confirm box ----------
function drawAsk(g) {
  g.fillStyle = 'rgba(6,4,16,0.76)'; g.fillRect(0, 0, W, H);
  panel(g, 140, 150, 360, 170);
  const lines = wrapText(g, App.askBox.text, 310, 16, UIF, 800);
  lines.forEach((ln, i) => text(g, ln, W / 2, 190 + i * 22, { size: 16, font: UIF, weight: 800, fill: '#ffffff' }));
  button(g, T('yes'), 170, 262, 140, 38, () => { const y = App.askBox.yes; App.askBox = null; y(); });
  button(g, T('no'), 330, 262, 140, 38, () => { App.askBox = null; Sound.sfx.back(); }, { primary: true });
}

// ---------- layout ----------
function touchMode() { return settings.touch === 1 || (settings.touch === 0 && (Input.usedTouch || COARSE)); }
function layout() {
  const portrait = window.innerHeight > window.innerWidth * 1.05;
  const tm = touchMode();
  document.body.classList.toggle('portrait', tm && portrait);
  let aw = Math.max(160, appEl.clientWidth - 32);
  const ah = Math.max(120, appEl.clientHeight - 24);
  const reserve = tm && portrait ? 132 : 0;
  appEl.style.paddingBottom = reserve ? (reserve + 12) + 'px' : '';
  if (tm && !portrait && window.innerHeight < 560) aw = Math.max(160, Math.min(aw, window.innerWidth - 300));
  let w = aw, h = w * 0.75;
  const maxH = Math.max(120, ah - reserve);
  if (h > maxH) { h = maxH; w = h / 0.75; }
  w = Math.floor(w); h = Math.floor(w * 0.75);
  if (w !== view.cssW || h !== view.cssH) { stage.style.width = w + 'px'; stage.style.height = h + 'px'; view.cssW = w; view.cssH = h; }
  const dpr = Math.min(2, window.devicePixelRatio || 1);
  const bw = Math.max(1, Math.min(1600, Math.round(w * dpr))), bh = Math.max(1, Math.round(bw * 0.75));
  if (canvas.width !== bw || canvas.height !== bh) { canvas.width = bw; canvas.height = bh; }
  view.scale = bw / W; view.cssScale = w / W;
  Assets.build(view.scale);
  NameBox.reposition();
}
let touchShown = null;
function updateTouch() {
  const want = touchMode() && App.screen === 'play' && !!App.sess && App.sess.state === 'run';
  if (want !== touchShown) { touchShown = want; document.body.classList.toggle('touch-on', want); }
}

// ---------- input dispatch ----------
function dispatchKeys() {
  const q = Input.takeQueue();
  if (q.length) App.ensureMusic();
  for (const ev of q) {
    if (!modalEl.hidden) continue;
    const nav = Input.navOf(ev);
    if (App.askBox) {
      if (nav === 'back') { App.askBox = null; Sound.sfx.back(); }
      else if (nav === 'left' || nav === 'up') UI.nav('up');
      else if (nav === 'right' || nav === 'down') UI.nav('down');
      else if (nav === 'ok' && !ev.repeat) UI.nav('ok');
      continue;
    }
    if (ev.repeat && nav !== 'up' && nav !== 'down' && nav !== 'left' && nav !== 'right') continue;
    const scr = Screens[App.screen];
    if (scr && scr.key) scr.key(nav, ev);
  }
}
function toLogical(e) { const r = canvas.getBoundingClientRect(); return { x: (e.clientX - r.left) / r.width * W, y: (e.clientY - r.top) / r.height * H }; }
let downAt = null;
canvas.addEventListener('pointermove', e => {
  const p = toLogical(e);
  UI.pointerMove(p.x, p.y);
  if (e.buttons && App.screen === 'replay' && downAt && downAt.y < 44 && p.y < 60 && App.rp) {
    const it = UI.prev.find(q => q.click && q.noNav && UI.inside(q, p.x, 25));
    if (it) it.click(p.x - it.x, 0);
  }
});
canvas.addEventListener('pointerdown', e => {
  Sound.init(); App.ensureMusic();
  const p = toLogical(e);
  UI.pointerMove(p.x, p.y);
  downAt = p;
  try { canvas.focus({ preventScroll: true }); } catch (err) { /* ignore */ }
});
canvas.addEventListener('pointerup', e => {
  const p = toLogical(e);
  if (downAt && Math.abs(p.x - downAt.x) < 26 && Math.abs(p.y - downAt.y) < 26 && modalEl.hidden) UI.click(p.x, p.y);
  downAt = null;
});
canvas.addEventListener('pointerleave', () => { UI.mouse.x = -1; UI.mouse.y = -1; });
canvas.addEventListener('wheel', e => {
  const scr = Screens[App.screen];
  if (scr && scr.wheel && !App.askBox) { e.preventDefault(); if (!canvas._wt || performance.now() - canvas._wt > 60) { canvas._wt = performance.now(); scr.wheel(e.deltaY); } }
}, { passive: false });
canvas.addEventListener('contextmenu', e => e.preventDefault());
document.addEventListener('visibilitychange', () => {
  if (document.hidden) {
    if (App.screen === 'play' && App.sess && App.sess.state === 'run') pauseGame();
    if (App.rp) App.rp.paused = true;
    Input.clearKeys(); Input.resetTouch();
    Sound.suspend(true);
  } else { Sound.suspend(false); lastT = performance.now(); }
});
window.addEventListener('blur', () => { if (App.screen === 'play' && App.sess && App.sess.state === 'run') pauseGame(); });

// ---------- main loop ----------
const MENU_SCREENS = new Set(['title', 'chars', 'options', 'controls', 'scores', 'replays', 'trophies', 'help']);
let lastT = 0, acc = 0;
function frame(now) {
  requestAnimationFrame(frame);
  let dt = (now - lastT) / 1000;
  lastT = now;
  if (!(dt >= 0)) dt = 0;
  if (dt > 0.1) dt = 0.1;
  App.dt = dt; App.time += dt;
  try {
    Input.pollPad();
    dispatchKeys();
    const scr = App.screen;
    const fromPause = (scr === 'options' || scr === 'controls') && Screens.options.from === 'pause' && App.sess;
    let frozen = false;
    if (scr === 'replay' && App.rp) {
      const rp = App.rp;
      if (!rp.paused && !rp.ended) {
        rp.acc += dt * RP_SPEEDS[rp.si];
        let n = 0;
        while (rp.acc >= STEP && n < 90) { rpStep(rp, true); rp.acc -= STEP; n++; if (rp.ended) break; }
        if (n >= 90) rp.acc = 0;
      } else frozen = true;
    } else if (scr === 'play' || (MENU_SCREENS.has(scr) && !fromPause)) {
      acc += dt;
      let n = 0;
      while (acc >= STEP && n < 6) { if (scr === 'play') tickPlay(); else tickAttract(); acc -= STEP; n++; }
      if (n >= 6) acc = 0;
      App.alpha = acc / STEP;
      if (scr === 'play' && App.sess && App.sess.state === 'pause') frozen = true;
    } else frozen = true;
    if (fromPause) frozen = true;
    if (!frozen) {
      FX.update(dt); Pops.update(dt);
      View.shake = Math.max(0, View.shake - dt * 14);
      View.flash = Math.max(0, View.flash - dt * 1.6);
      View.ringT = Math.max(0, View.ringT - dt);
      View.comboPulse = Math.max(0, View.comboPulse - dt * 4);
      if (View.zb) ambientFX(dt, View.zb);
    }
    Pops.updateToasts(dt);
    App.fade = Math.max(0, App.fade - dt * 4);
    App.flashMsgT -= dt;
    render();
    updateTouch();
  } catch (err) {
    if (!frame.errs) frame.errs = 0;
    if (frame.errs++ < 5) console.error(err);
  }
}
function render() {
  const g = ctx;
  g.setTransform(view.scale, 0, 0, view.scale, 0, 0);
  g.globalAlpha = 1; g.globalCompositeOperation = 'source-over';
  UI.begin();
  const scr = Screens[App.screen];
  const keepFocus = UI.focus;
  if (App.askBox) UI.focus = -1;
  scr.draw(g, App.time, App.screen === 'replay' ? (App.rp ? clamp(App.rp.acc / STEP, 0, 1) : 0) : clamp(App.alpha, 0, 1));
  UI.focus = keepFocus;
  if (App.screen === 'options' && NameBox.open) NameBox.place(300, (Screens.options.nameY || 0) - 13, 236, 26);
  if (App.askBox) { UI.items.length = 0; drawAsk(g); }
  Pops.drawToasts(g, App.screen === 'replay' ? 62 : 10);
  if (App.fade > 0) { g.fillStyle = 'rgba(5,4,14,' + (App.fade * 0.9).toFixed(3) + ')'; g.fillRect(0, 0, W, H); }
  UI.end();
}

// ---------- boot ----------
function boot() {
  layout();
  App.attract = newAttract();
  for (let i = 0; i < 200; i++) tickAttract();
  FX.clear();
  App.go('title');
  App.fade = 0;
  window.addEventListener('resize', layout);
  if (window.ResizeObserver) new ResizeObserver(() => layout()).observe(appEl);
  try { if (document.fonts && document.fonts.load) ['32px "Lilita One"', '700 16px "Baloo 2"', '800 16px "Baloo 2"'].forEach(f => document.fonts.load(f).catch(() => {})); } catch (e) { /* fonts optional */ }
  document.documentElement.lang = settings.lang ? 'tr' : 'en';
  window.__hop = { App, Data, settings, startGame, startReplay, newGame, stepGame, Bot, gameScore, Screens, UI, Input, Sound, render, replayToCode, replayFromCode };
  requestAnimationFrame(t => { lastT = t; frame(t); });
  try { canvas.focus({ preventScroll: true }); } catch (e) { /* ignore */ }
}
boot();
})();
