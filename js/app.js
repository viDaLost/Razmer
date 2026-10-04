/* Раскладка пола — интерфейс. Ядро расчёта в js/engine.js (RazmerEngine). */
(() => {
'use strict';
const E = window.RazmerEngine;
const PF = window.RazmerPlatform || { inTG: false, tg: null, ios: false, android: false, standalone: false, ready: Promise.resolve(null), haptic() {}, version() { return false; } };
const { DEG, clamp, mod, num, mm, f1, fm2, dist, plural, hash01, area, perim, inPoly, segDist, bboxOf, centroid, centroidMany, onLine,
  CATS, catById, TONES, PATTERNS, patDef, BORDER_PATTERNS, TEMPLATES, rectWalls, defaultPat, newRoom, newId, defaultState, migrateState,
  roomGeom, wallsFromCorners, innerAngles, unitV, inwardOf, arcRadius, arcLength, sagittaFromRadius, computeGeo, adjacency, unitKeys, buildUnit, computeUnit,
  plankPts, plankOutline, mainPart, cutSpec, genBond, genHerring, genChevron, genBasket, planRemnant, randShifts, clipBy } = E;

/* ================= helpers ================= */
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const lsGet = k => { try { return localStorage.getItem(k); } catch (e) { return null; } };
const lsSet = (k, v) => { try { localStorage.setItem(k, v); return true; } catch (e) { return false; } };
const capUse = name => { try { return (window.claude && typeof window.claude.use === 'function') ? window.claude.use(name).catch(() => null) : Promise.resolve(null); } catch (e) { return Promise.resolve(null); } };
const deep = o => JSON.parse(JSON.stringify(o));
const rgb = c => 'rgb(' + c[0] + ',' + c[1] + ',' + c[2] + ')';
const mix = (a, b, t) => a.map((x, i) => Math.round(x * (1 - t) + b[i] * t));
const hashStr = s => { let h = 7; for (let i = 0; i < s.length; i++) h = Math.imul(h ^ s.charCodeAt(i), 2654435761); return h >>> 0; };
const ICON = {
  split: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M4 12h16M12 7v10"/></svg>',
  del: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M6 6l12 12M18 6L6 18"/></svg>',
  plus: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M12 5v14M5 12h14"/></svg>',
  back: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2"><path d="M15 5l-7 7 7 7"/></svg>',
  rot: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M20 12a8 8 0 11-2.3-5.7"/><path d="M20 4v5h-5"/></svg>',
  copy: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="8" y="8" width="12" height="12" rx="1"/><path d="M16 8V4H4v12h4"/></svg>',
  img: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M4 8h3l2-3h6l2 3h3v11H4z"/><circle cx="12" cy="13" r="3.5"/></svg>',
  share: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M12 3v12M8 7l4-4 4 4"/><path d="M6 11H5v10h14V11h-1"/></svg>',
  star: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M12 3l2.6 5.6 6 .7-4.5 4.1 1.2 6L12 16.4 6.7 19.4l1.2-6L3.4 9.3l6-.7z"/></svg>',
};

const KEY_DRAFT = 'raskladka.draft.v1', KEY_PROJ = 'raskladka.projects.v1', KEY_MATS = 'raskladka.mats.v1', KEY_UI = 'raskladka.ui.v2';
let S = defaultState();
const UI = { tab: 'plan', mode: 'rooms', style: 'wood', labels: true, room: 'r1', target: 'floor', matTarget: 'main', catView: 'eng', addTpl: null, addPrev: null, sel: null, hl: null, step: 10, variants: null, helpSeen: false, mapH: null, addRoom: false, delArm: null, wallFocus: -1, wall: null, open: {}, item: null, place: null, ghost: null };
/* шаг определяет, что делает палец на карте */
const MODE_OF = { plan: 'rooms', mat: 'view', pat: 'pattern', res: 'view' };
let MODEL = null;

/* ================= расчёт ================= */
let GEO_FOR_ANALYZE = null;
function computeAll() {
  const geo = computeGeo(S); GEO_FOR_ANALYZE = geo;
  const units = [];
  for (const key of unitKeys(S, geo)) { const u = buildUnit(key, S, geo); if (u) units.push(computeUnit(u, false, analyzeUnit)); }
  const byKey = {}; units.forEach(r => { byKey[r.unit.key] = r; });
  const mats = new Map();
  for (const r of units) {
    if (r.err || !r.stats) continue; const M = r.unit.mat;
    const m = mats.get(M.key) || { M, boards: 0, full: 0, cut: 0, area: 0, names: [] };
    m.boards += r.stats.boards; m.full += r.stats.nFull; m.cut += r.stats.nCut; m.area += r.stats.layA; m.names.push(r.unit.name); mats.set(M.key, m);
  }
  return { geo, units, byKey, mats: [...mats.values()], adj: adjacency(S, geo) };
}
function woodRGB(tone, idx, kind) {
  const base = (TONES[tone] || TONES.oak).c, h = hash01(idx * 2654435761 + 7);
  const f = 0.9 + h * 0.16 - (kind === 'B' ? 0.05 : 0);
  return base.map(c => clamp(Math.round(c * f), 0, 255));
}
function pathOf(poly) { const p = new Path2D(); poly.forEach((q, k) => k ? p.lineTo(q[0], q[1]) : p.moveTo(q[0], q[1])); p.closePath(); return p; }
function analyzeUnit(res) {
  const u = res.unit, M = u.mat, P = u.P, pd = patDef(P.type), thr = num(P.minEdge, 25), geo = GEO_FOR_ANALYZE, seed = hashStr(u.key) % 9973;
  const tapeRGB = [242, 183, 5], groups = new Map(), seams = new Path2D();
  let nFull = 0, nCut = 0, nBad = 0, minT = Infinity, nA = 0, nB = 0, layA = 0;
  res.pieces.forEach((p, idx) => {
    const F = p.F;
    p.rawW = p.raw.map(F.toW); p.w = p.parts.map(poly => poly.map(F.toW));
    p.path = pathOf(p.rawW); seams.addPath(p.path);
    if (p.kind === 'A') nA++; else if (p.kind === 'B') nB++;
    const base = woodRGB(M.tone, idx + seed, p.kind);
    if (p.full) { nFull++; p.col = rgb(base); return; }
    nCut++; p.bad = p.thick < thr; if (p.bad) nBad++; if (p.thick < minT) minT = p.thick;
    p.col = rgb(mix(base, tapeRGB, 0.42));
    p.spec = cutSpec(p);
    const g = groups.get(p.spec.key) || { key: p.spec.key, kind: p.kind, lines: p.spec.lines, idx: [], ext: p.spec.ext };
    g.idx.push(idx); groups.set(p.spec.key, g); p.gk = p.spec.key;
    const mp = mainPart(p), lb = bboxOf(mp);
    if (pd.group === 'bond') { const lu = lb.u1 - lb.u0, lv = lb.v1 - lb.v0; p.lab = (lu < M.L - 0.5 && lv < M.W - 0.5) ? mm(lu) + '×' + mm(lv) : lu < M.L - 0.5 ? mm(lu) : mm(lv); }
    else p.lab = mm(p.spec.ext);
    p.cen = centroid(mp.map(F.toW));
  });
  res.seams = seams;
  res.groups = [...groups.values()].sort((a, b) => b.idx.length - a.idx.length || b.ext - a.ext);
  res.clip = new Path2D();
  for (const part of u.parts) for (const r of part.regions) { let poly = r.poly; if (area(poly) < 0) poly = poly.slice().reverse(); res.clip.addPath(pathOf(poly)); layA += Math.abs(area(poly)); }
  for (const part of u.parts) for (const s of part.subtract) for (const r of part.regions) layA -= Math.abs(area(clipBy(r.poly, s)));
  // ряды
  res.rows = null;
  if (pd.group === 'bond' && u.kind !== 'border') {
    const map = new Map();
    res.pieces.forEach((p, idx) => {
      if (p.part !== 0) return;
      let v0 = Infinity, v1 = -Infinity; for (const q of p.parts) { const b = bboxOf(q); v0 = Math.min(v0, b.v0); v1 = Math.max(v1, b.v1); }
      const b = bboxOf(mainPart(p)); let r = map.get(p.row);
      if (!r) { r = { k: p.row, v0: Infinity, v1: -Infinity, items: [] }; map.set(p.row, r); }
      r.v0 = Math.min(r.v0, v0); r.v1 = Math.max(r.v1, v1);
      let len = 0; for (const q of p.parts) { const bq = bboxOf(q); len += bq.u1 - bq.u0; }
      r.items.push({ u0: b.u0, len: p.parts.length > 1 ? len : b.u1 - b.u0, full: p.full, idx, src: p.src, bad: p.bad });
    });
    res.rows = [...map.values()].sort((a, b) => a.k - b.k);
    res.rows.forEach(r => { r.items.sort((a, b) => a.u0 - b.u0); r.width = r.v1 - r.v0; });
  }
  // расход
  let boards;
  if (res.plans.length) boards = res.plans.reduce((s, p) => s + p.boards, 0);
  else {
    boards = 0; const byKind = {};
    for (const p of res.pieces) { if (p.full) { boards++; continue; } (byKind[p.kind] = byKind[p.kind] || []).push(Math.min(p.spec.ext, M.L)); }
    for (const k in byKind) {
      const list = byKind[k].sort((a, b) => b - a), bins = [];
      for (const len of list) { let placed = false; for (let i = 0; i < bins.length; i++) if (bins[i] >= len) { bins[i] -= len + M.kerf; placed = true; break; } if (!placed) bins.push(M.L - len - M.kerf); }
      boards += bins.length;
    }
  }
  res.walls = wallStats(res, geo);
  res.guides = unitGuides(res, geo);
  res.start = null;
  if (res.rows && res.rows.length && res.rows[0].items.length) {
    const F = u.parts[0].frame, r0 = res.rows[0], it = r0.items[0];
    res.start = { p: F.toW([it.u0, r0.v0]), du: F.vecW([1, 0]), dv: F.vecW([0, 1]) };
  }
  res.stats = { nFull, nCut, nBad, minT, nA, nB, boards, layA, needA: boards * M.L * M.W, waste: Math.max(0, 1 - layA / Math.max(1, boards * M.L * M.W)) };
}
function wallStats(res, geo) {
  const u = res.unit, sets = [];
  for (const rid of u.roomIds) {
    const G = geo[rid]; if (!G || G.err) continue;
    if (u.kind === 'border') sets.push({ rid, G, poly: G.lay, idx: G.g.wIdx, g: G.g, label: 'стена' });
    else if (u.kind === 'floor' || u.kind === 'room') sets.push({ rid, G, poly: G.center, idx: G.cIdx, g: G.g, label: G.inner ? 'рамка у стены' : 'стена' });
  }
  const out = [];
  for (const set of sets) {
    const n = set.g.n, Lp = set.poly.length, walls = [];
    for (let i = 0; i < n; i++) {
      const s = set.idx[i], e = i + 1 < n ? set.idx[i + 1] : Lp, segs = [], P = set.g.corners[i], Q = set.g.corners[(i + 1) % n];
      for (let k = s; k < e; k++) segs.push([set.poly[k % Lp], set.poly[(k + 1) % Lp]]);
      // участки стены, занятые проёмами: там планка не упирается в стену, а идёт дальше
      const doors = set.G.doors.filter(d => d.wall === i).map(d => [d.t0 - 1, d.t1 + 1]);
      walls.push({ rid: set.rid, i, label: set.label, segs, doors, P, u: unitV(P, Q), count: 0, minD: Infinity, maxD: 0, minT: Infinity, len: dist(P, Q), arc: Math.abs(set.g.arcs[i]) >= 0.5 });
    }
    for (const p of res.pieces) {
      if (p.full) continue;
      const F = p.F, o = p.fr.o, fx = p.fr.x, fy = p.fr.y;
      const outl = plankOutline(p.fr).map(q => F.toW([o[0] + q[0] * fx[0] + q[1] * fy[0], o[1] + q[0] * fx[1] + q[1] * fy[1]]));
      for (const w of walls) {
        let hit = false;
        for (const part of p.w) {
          for (let k = 0, m = part.length; k < m && !hit; k++) {
            const a = part[k], b = part[(k + 1) % m]; if (dist(a, b) < 0.5) continue;
            let fac = false; for (let j = 0; j < 4; j++) if (onLine(a, b, outl[j], outl[(j + 1) % 4], 0.6)) { fac = true; break; }
            if (fac) continue;
            if (w.doors.length) { const ta = (a[0] - w.P[0]) * w.u[0] + (a[1] - w.P[1]) * w.u[1], tb = (b[0] - w.P[0]) * w.u[0] + (b[1] - w.P[1]) * w.u[1]; if (w.doors.some(d => Math.min(ta, tb) >= d[0] && Math.max(ta, tb) <= d[1])) continue; }
            for (const [s0, s1] of w.segs) {
              if (!onLine(a, b, s0, s1, 0.6)) continue;
              const dx = s1[0] - s0[0], dy = s1[1] - s0[1], l = Math.hypot(dx, dy) || 1;
              const t1 = ((a[0] - s0[0]) * dx + (a[1] - s0[1]) * dy) / l, t2 = ((b[0] - s0[0]) * dx + (b[1] - s0[1]) * dy) / l;
              if (Math.max(t1, t2) > -0.5 && Math.min(t1, t2) < l + 0.5) { hit = true; break; }
            }
          }
          if (hit) break;
        }
        if (!hit) continue;
        let depth = 0;
        for (const part of p.w) for (const q of part) { let dmin = Infinity; for (const [s0, s1] of w.segs) dmin = Math.min(dmin, segDist(q[0], q[1], s0, s1)); depth = Math.max(depth, dmin); }
        w.count++; w.minD = Math.min(w.minD, depth); w.maxD = Math.max(w.maxD, depth); w.minT = Math.min(w.minT, p.thick);
      }
    }
    out.push(...walls);
  }
  return out;
}
function unitGuides(res, geo) {
  const u = res.unit; if (u.kind === 'border') return [];
  const F = u.parts[0].frame, M = u.mat, pd = patDef(u.P.type), G = geo[u.refRoom];
  const polys = u.kind === 'ins' ? [u.ins.region] : [G.center];
  const L = polys.map(p => p.map(F.toL)), cen = centroidMany(L), lines = [];
  if (pd.group === 'herring') { const per = Math.SQRT2 * (M.L + M.g); lines.push({ axis: 'v', c: Math.round(cen[1] / per) * per, name: 'ось ёлочки' }); }
  else if (pd.group === 'chevron') { const Sv = (M.L + M.g) * Math.sin(clamp(num(u.P.chevAngle, 45), 15, 75) * DEG); lines.push({ axis: 'v', c: Math.round(cen[1] / Sv) * Sv, name: 'линия вершин' }); }
  else if (pd.group === 'basket') { const B = M.L + M.g; lines.push({ axis: 'u', c: Math.round(cen[0] / B) * B, name: 'разметка' }, { axis: 'v', c: Math.round(cen[1] / B) * B, name: 'разметка' }); }
  else if (pd.id === 'grid') { const Lp = M.L + M.g, Wp = M.W + M.g; lines.push({ axis: 'u', c: Math.round(cen[0] / Lp) * Lp, name: 'шов' }, { axis: 'v', c: Math.round(cen[1] / Wp) * Wp, name: 'шов' }); }
  else if (res.rows && res.rows.length) { const r0 = res.rows.find(r => r.width > M.W * 0.5) || res.rows[0]; lines.push({ axis: 'v', c: r0.v1 + M.g / 2, name: 'край ' + (res.rows.indexOf(r0) + 1) + '-го ряда' }); }
  // расстояния до параллельных прямых стен опорной комнаты
  const g = G.g, C = g.corners.map(F.toL);
  for (const ln of lines) {
    let lo = null, hi = null;
    for (let i = 0; i < g.n; i++) {
      if (Math.abs(g.arcs[i]) >= 0.5) continue;
      const p = C[i], q = C[(i + 1) % g.n], d = [q[0] - p[0], q[1] - p[1]], l = Math.hypot(d[0], d[1]); if (l < 1) continue;
      const par = ln.axis === 'v' ? Math.abs(d[1]) / l < 0.01 : Math.abs(d[0]) / l < 0.01; if (!par) continue;
      const pos = ln.axis === 'v' ? (p[1] + q[1]) / 2 : (p[0] + q[0]) / 2, dd = Math.abs(pos - ln.c);
      if (pos < ln.c) { if (!lo || dd < lo.dist) lo = { wall: i, dist: dd }; } else { if (!hi || dd < hi.dist) hi = { wall: i, dist: dd }; }
    }
    ln.lo = lo; ln.hi = hi; ln.room = u.refRoom;
  }
  return lines;
}

/* ================= цвета и рендер ================= */
let COL = {};
function readColors() {
  const cs = getComputedStyle(document.documentElement), g = n => cs.getPropertyValue(n).trim();
  COL = { canvas: g('--canvas'), grid: g('--grid'), wall: g('--wall'), gap: g('--gapzone'), schA: g('--sch-a'), schB: g('--sch-b'), seam: g('--seam'), chalk: g('--chalk'), onChalk: g('--on-chalk'), tape: g('--tape'), tapeSoft: g('--tape-soft'), bad: g('--bad'), badSoft: g('--bad-soft'), ink: g('--ink'), muted: g('--muted'), panel: g('--panel'), line: g('--line'), mono: g('--font-mono') || 'monospace', body: g('--font-body') || 'sans-serif' };
}
const view = { s: 0.1, cx: 0, cy: 0, fitted: false };
const cv = $('#plan'); let CW = 300, CH = 300, DPR = 1;
const room = id => S.rooms.find(r => r.id === id);
const curRoom = () => room(UI.room) || S.rooms[0];
const roomName = id => (room(id) || {}).name || '';

function render(ctx, W, H, vw, opt) {
  const k = opt.k || 1;
  ctx.setTransform(k, 0, 0, k, 0, 0);
  ctx.fillStyle = COL.canvas; ctx.fillRect(0, 0, W, H);
  const s = vw.s, tx = W / 2 - vw.cx * s, ty = H / 2 - vw.cy * s, X = x => x * s + tx, Y = y => y * s + ty;
  const steps = [100, 250, 500, 1000, 2000, 5000]; const st = steps.find(v => v * s >= 28) || 5000;
  ctx.strokeStyle = COL.grid; ctx.lineWidth = 1; ctx.beginPath();
  const x0 = Math.floor((-tx / s) / st) * st, y0 = Math.floor((-ty / s) / st) * st;
  for (let x = x0; X(x) < W; x += st) { const px = Math.round(X(x)) + 0.5; ctx.moveTo(px, 0); ctx.lineTo(px, H); }
  for (let y = y0; Y(y) < H; y += st) { const py = Math.round(Y(y)) + 0.5; ctx.moveTo(0, py); ctx.lineTo(W, py); }
  ctx.stroke();
  if (!MODEL) return;
  const geo = MODEL.geo, sch = opt.style === 'scheme', live = opt.live, mode = live ? UI.mode : 'view';
  ctx.save(); ctx.transform(s, 0, 0, s, tx, ty);
  for (const r of S.rooms) { const G = geo[r.id]; if (G && G.g && !G.err) { ctx.fillStyle = COL.gap; ctx.fill(pathOf(G.g.poly)); } }
  for (const res of MODEL.units) {
    if (res.err || !res.clip) continue;
    ctx.save(); ctx.clip(res.clip);
    for (const p of res.pieces) { ctx.fillStyle = sch ? (p.full ? (p.kind === 'B' ? COL.schB : COL.schA) : (p.bad ? COL.badSoft : COL.tape)) : (p.bad ? COL.badSoft : p.col); ctx.fill(p.path); }
    if (live && UI.hl && UI.hl.key === res.unit.key) { ctx.fillStyle = 'rgba(29,107,214,.45)'; for (const p of res.pieces) if (p.gk === UI.hl.gk) ctx.fill(p.path); }
    ctx.lineWidth = clamp(s * 1.6, 0.35, 1.1) / s; ctx.strokeStyle = COL.seam; ctx.stroke(res.seams);
    ctx.restore();
  }
  // выбранная планка
  const selP = live ? selectedPiece() : null;
  if (selP) { ctx.lineWidth = 3 / s; ctx.strokeStyle = COL.chalk; for (const part of selP.p.w) ctx.stroke(pathOf(part)); }
  // рамка и вставки: тонкий контур
  ctx.lineWidth = 1.2 / s; ctx.strokeStyle = COL.wall; ctx.setLineDash([6 / s, 4 / s]);
  for (const r of S.rooms) { const G = geo[r.id]; if (!G || G.err) continue; if (G.inner) ctx.stroke(pathOf(G.inner)); for (const x of G.inserts) ctx.stroke(pathOf(x.rect)); }
  ctx.setLineDash([]);
  // ниши без пола (под шкаф) и не построенные — штриховка
  for (const r of S.rooms) {
    const G = geo[r.id]; if (!G || !G.g || !G.g.niches) continue;
    for (const nc of G.g.niches) {
      if (nc.floor && !nc.off) continue;
      const path = pathOf(nc.pts); ctx.save(); ctx.clip(path);
      ctx.fillStyle = nc.off ? COL.badSoft : COL.panel; ctx.fill(path);
      ctx.strokeStyle = nc.off ? COL.bad : COL.muted; ctx.lineWidth = 1 / s; ctx.beginPath();
      const b = bboxOf(nc.pts), step = 9 / s; for (let v = b.u0 - (b.v1 - b.v0); v < b.u1; v += step) { ctx.moveTo(v, b.v0); ctx.lineTo(v + (b.v1 - b.v0), b.v1); }
      ctx.stroke(); ctx.restore();
    }
  }
  // стены: проёмы — разрывы, ниши без пола — пунктир по краю пола
  ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  for (const r of S.rooms) {
    const G = geo[r.id]; if (!G || !G.g) continue;
    const sel = r.id === UI.room && S.rooms.length > 1 && mode === 'rooms';
    ctx.strokeStyle = G.err ? COL.bad : COL.wall; ctx.lineWidth = (sel ? 4 : 3.2) / s;
    if (G.err) ctx.setLineDash([8 / s, 6 / s]);
    const g = G.g, Lp = g.poly.length, T = Math.max(0, num(S.set.wallT, 120));
    for (let i = 0; i < g.n; i++) {
      const sIdx = g.wIdx[i], eIdx = i + 1 < g.n ? g.wIdx[i + 1] : Lp, pts = [];
      for (let kk = sIdx; kk <= eIdx; kk++) pts.push(g.poly[kk % Lp]);
      const P = g.corners[i], Q = g.corners[(i + 1) % g.n], u = unitV(P, Q), c = dist(P, Q);
      const doors = G.doors.filter(d => d.wall === i), open = (g.niches || []).filter(x => x.wall === i && (!x.floor || x.off));
      const cuts = doors.map(d => [d.t0, d.t1]).concat(open.map(x => [x.t0, x.t1]), neighborDoorCuts(r.id, i, P, u)).sort((a, b) => a[0] - b[0]);
      const tOf = q => (q[0] - P[0]) * u[0] + (q[1] - P[1]) * u[1], offL = q => Math.abs((q[0] - P[0]) * u[1] - (q[1] - P[1]) * u[0]);
      ctx.beginPath();
      for (let j = 0; j + 1 < pts.length; j++) {
        const a = pts[j], b = pts[j + 1];
        if (!cuts.length || Math.abs(g.arcs[i]) >= 0.5 || offL(a) > 0.5 || offL(b) > 0.5) { ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); continue; }
        let ta = tOf(a), tb = tOf(b); const fwd = tb >= ta; if (!fwd) [ta, tb] = [tb, ta];
        let t = ta;
        for (const [c0, c1] of cuts) { if (c1 <= t || c0 >= tb) continue; if (c0 > t) { ctx.moveTo(P[0] + u[0] * t, P[1] + u[1] * t); ctx.lineTo(P[0] + u[0] * c0, P[1] + u[1] * c0); } t = Math.max(t, c1); }
        if (t < tb) { ctx.moveTo(P[0] + u[0] * t, P[1] + u[1] * t); ctx.lineTo(P[0] + u[0] * tb, P[1] + u[1] * tb); }
      }
      ctx.stroke();
      if (doors.length) {
        ctx.save(); ctx.lineWidth = 1.5 / s;
        for (const d of doors) for (const tt of [d.t0, d.t1]) { const B = [P[0] + u[0] * tt, P[1] + u[1] * tt]; ctx.beginPath(); ctx.moveTo(B[0], B[1]); ctx.lineTo(B[0] + d.n[0] * T, B[1] + d.n[1] * T); ctx.stroke(); }
        ctx.restore();
      }
      for (const x of open) {
        ctx.beginPath(); ctx.moveTo(x.pts[0][0], x.pts[0][1]); for (const q of x.pts.slice(1)) ctx.lineTo(q[0], q[1]); ctx.stroke();
        ctx.save(); ctx.lineWidth = 1.4 / s; ctx.setLineDash([5 / s, 4 / s]); ctx.beginPath(); ctx.moveTo(x.pts[0][0], x.pts[0][1]); ctx.lineTo(x.pts[3][0], x.pts[3][1]); ctx.stroke(); ctx.restore();
      }
    }
    ctx.setLineDash([]);
  }
  ctx.restore();
  // подписи подрезок
  if (opt.labels) {
    ctx.font = '600 11px ' + COL.mono; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.lineJoin = 'round';
    const placed = [], free = (x0, y0, x1, y1) => { for (const q of placed) if (x0 < q[2] && x1 > q[0] && y0 < q[3] && y1 > q[1]) return false; placed.push([x0, y0, x1, y1]); return true; };
    for (const res of MODEL.units) {
      if (res.err) continue;
      for (const p of res.pieces) {
        if (p.full || !p.lab || !p.cen) continue;
        const b = bboxOf(p.w.length === 1 ? p.w[0] : p.w.flat()), sw = (b.u1 - b.u0) * s, sh = (b.v1 - b.v0) * s, tw = ctx.measureText(p.lab).width + 4;
        if (Math.min(sw, sh) < 13 || Math.max(sw, sh) < tw) continue;
        const cx = X(p.cen[0]), cy = Y(p.cen[1]), rot = sh > sw && sw < tw, hw = (rot ? 7 : tw / 2), hh = (rot ? tw / 2 : 7);
        if (!free(cx - hw, cy - hh, cx + hw, cy + hh)) continue;
        ctx.save(); ctx.translate(cx, cy); if (rot) ctx.rotate(-Math.PI / 2);
        ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(255,255,255,.85)'; ctx.strokeText(p.lab, 0, 0.5);
        ctx.fillStyle = p.bad ? '#a32616' : '#3b2a00'; ctx.fillText(p.lab, 0, 0.5); ctx.restore();
      }
    }
  }
  // направляющие выбранного участка
  const tres = mode === 'rooms' ? null : MODEL.byKey[UI.target];
  if (tres && !tres.err && tres.guides && tres.guides.length) {
    const F = tres.unit.parts[0].frame, big = 1e5;
    ctx.save(); ctx.setTransform(k, 0, 0, k, 0, 0); ctx.transform(s, 0, 0, s, tx, ty); ctx.clip(tres.clip);
    ctx.setLineDash([9 / s, 6 / s]); ctx.lineWidth = 2 / s; ctx.strokeStyle = COL.chalk;
    for (const gl of tres.guides) { const a = F.toW(gl.axis === 'v' ? [-big, gl.c] : [gl.c, -big]), b = F.toW(gl.axis === 'v' ? [big, gl.c] : [gl.c, big]); ctx.beginPath(); ctx.moveTo(a[0], a[1]); ctx.lineTo(b[0], b[1]); ctx.stroke(); }
    ctx.restore(); ctx.setLineDash([]);
    if (opt.labels) for (const gl of tres.guides) {
      const parts = []; if (gl.lo) parts.push(mm(gl.lo.dist) + ' от ст. ' + (gl.lo.wall + 1)); if (gl.hi) parts.push(mm(gl.hi.dist) + ' от ст. ' + (gl.hi.wall + 1));
      const L = (tres.unit.kind === 'ins' ? [tres.unit.ins.region] : [MODEL.geo[tres.unit.refRoom].center]).map(p => p.map(F.toL));
      const bb = bboxOf(L.flat()), P = gl.axis === 'v' ? [(bb.u0 + bb.u1) / 2, gl.c] : [gl.c, (bb.v0 + bb.v1) / 2], w = F.toW(P);
      const roomW = (gl.axis === 'v' ? bb.u1 - bb.u0 : bb.v1 - bb.v0) * s * 0.9;
      let txt = gl.name + (parts.length ? ': ' + parts.join(' · ') : ''); ctx.font = '600 11px ' + COL.body;
      if (ctx.measureText(txt).width + 14 > roomW) txt = [gl.lo, gl.hi].filter(Boolean).map(x => mm(x.dist)).join(' · ') || gl.name;
      if (ctx.measureText(txt).width + 14 <= Math.max(roomW, 60)) pillText(ctx, txt, X(w[0]), Y(w[1]), COL.chalk, COL.onChalk, 'center');
    }
  }
  if (tres && tres.start && live) {
    const p = tres.start.p, px = X(p[0]), py = Y(p[1]), du = tres.start.du, dv = tres.start.dv, L = 30;
    ctx.strokeStyle = COL.chalk; ctx.fillStyle = COL.chalk; ctx.lineWidth = 3;
    ctx.beginPath(); ctx.moveTo(px + du[0] * L, py + du[1] * L); ctx.lineTo(px, py); ctx.lineTo(px + dv[0] * L * 0.7, py + dv[1] * L * 0.7); ctx.stroke();
    arrowHead(ctx, px + du[0] * L, py + du[1] * L, du); ctx.beginPath(); ctx.arc(px, py, 5, 0, Math.PI * 2); ctx.fill();
    pillText(ctx, 'СТАРТ', px + du[0] * 10 + dv[0] * 20, py + du[1] * 10 + dv[1] * 20, COL.chalk, COL.onChalk, 'left');
  }
  // названия комнат на шаге «Комнаты» (под подписями стен); у выбранной — под значком переноса, если комната крупная
  if (live && mode === 'rooms' && !UI.item && !UI.place) {
    for (const r of S.rooms) {
      const G = geo[r.id]; if (!G || !G.g) continue; const c = centroid(G.g.poly), bb = bboxOf(G.g.poly), sel = r.id === UI.room;
      if (sel && (bb.v1 - bb.v0) * s < 110) continue;
      // подпись должна помещаться в комнату: иначе без площади, а если и так не влезает — не пишем
      ctx.font = '600 11px ' + COL.body; const room_w = (bb.u1 - bb.u0) * s * 0.92;
      let txt = r.name + (G.err ? ' — ошибка' : ' · ' + fm2(Math.abs(area(G.g.poly))) + ' м²');
      if (ctx.measureText(txt).width + 14 > room_w) txt = r.name;
      if (ctx.measureText(txt).width + 14 > room_w) continue;
      pillText(ctx, txt, X(c[0]), Y(c[1]) + (sel ? 30 : 0), sel ? COL.chalk : COL.ink, sel ? COL.onChalk : COL.panel, 'center');
    }
  }
  // подписи стен выбранной комнаты; у стены, к которой приставлена комната, размеры делятся по стыку
  const R = curRoom(), RG = R && geo[R.id];
  if (RG && RG.g && opt.labels !== false) {
    const g = RG.g, sgn = g.sgn, joints = (MODEL.adj || []).filter(a => a.a === R.id);
    ctx.font = '600 11px ' + COL.mono; ctx.textBaseline = 'middle';
    for (let i = 0; i < g.n; i++) {
      const P = g.corners[i], Q = g.corners[(i + 1) % g.n], c = dist(P, Q); if (c * s < 30) continue;
      const u = unitV(P, Q), n = sgn > 0 ? [u[1], -u[0]] : [-u[1], u[0]], isArc = Math.abs(g.arcs[i]) >= 0.5;
      let M = [(P[0] + Q[0]) / 2, (P[1] + Q[1]) / 2];
      if (isArc) M = [M[0] + n[0] * g.arcs[i], M[1] + n[1] * g.arcs[i]];
      const mx = X(M[0]) + n[0] * 17, my = Y(M[1]) + n[1] * 17;
      const txt = (isArc ? '⌒ ' : '') + mm(c), tw = ctx.measureText(txt).width;
      const auto = g.autoClosed && i === g.n - 1, selW = live && UI.wall && UI.wall.rid === R.id && UI.wall.i === i;
      ctx.fillStyle = auto ? COL.muted : selW ? COL.tape : COL.chalk; ctx.beginPath(); ctx.arc(mx - tw / 2 - 11, my, 9, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = selW ? '#3b2a00' : COL.onChalk; ctx.textAlign = 'center'; ctx.fillText(String(i + 1), mx - tw / 2 - 11, my + 0.5);
      ctx.textAlign = 'left'; ctx.lineWidth = 3; ctx.strokeStyle = COL.canvas; ctx.strokeText(txt, mx - tw / 2, my + 0.5); ctx.fillStyle = COL.ink; ctx.fillText(txt, mx - tw / 2, my + 0.5);
      // стыки с соседними комнатами: засечки и длины частей стены внутри комнаты
      const js = isArc || (live && (selWallOf(UI.item) === R.id + ':' + i || (UI.ghost && UI.ghost.rid === R.id && UI.ghost.i === i))) ? [] : joints.filter(a => a.i === i);
      if (!js.length) continue;
      const bps = [0, c]; for (const a of js) bps.push(a.o0, a.o1);
      bps.sort((a, b) => a - b); const br = []; for (const b of bps) if (!br.length || b - br[br.length - 1] > 5) br.push(b); else br[br.length - 1] = Math.max(br[br.length - 1], b);
      if (br.length < 3) continue;
      const inn = [-n[0], -n[1]];
      ctx.strokeStyle = COL.chalk; ctx.lineWidth = 2;
      for (const b of br.slice(1, -1)) { const q = [P[0] + u[0] * b, P[1] + u[1] * b], sx = X(q[0]), sy = Y(q[1]); ctx.beginPath(); ctx.moveTo(sx - inn[0] * 6, sy - inn[1] * 6); ctx.lineTo(sx + inn[0] * 22, sy + inn[1] * 22); ctx.stroke(); }
      for (let j = 0; j + 1 < br.length; j++) {
        const a = br[j], b = br[j + 1], len = b - a; if (len * s < 34) continue;
        const shared = js.some(x => a >= x.o0 - 3 && b <= x.o1 + 3), q = [P[0] + u[0] * (a + b) / 2, P[1] + u[1] * (a + b) / 2];
        const t2 = mm(len), sx = X(q[0]) + inn[0] * 14, sy = Y(q[1]) + inn[1] * 14;
        ctx.textAlign = 'center'; ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(255,255,255,.9)'; ctx.strokeText(t2, sx, sy + 0.5);
        ctx.fillStyle = shared ? '#1557b0' : '#17212b'; ctx.fillText(t2, sx, sy + 0.5); // поверх планок — тёмным в любой теме
      }
    }
    // ниши и выступы выбранной комнаты
    if (mode === 'rooms') for (const nc of g.niches || []) {
      const c0 = nc.pts[1], c1 = nc.pts[2], q = [(c0[0] + c1[0]) / 2, (c0[1] + c1[1]) / 2], wpx = (nc.t1 - nc.t0) * s;
      if (wpx < 40) continue;
      const txt = (nc.kind === 'box' ? 'выступ ' : nc.floor ? 'ниша ' : 'без пола ') + mm(nc.t1 - nc.t0) + '×' + mm(nc.d), out = nc.kind === 'box' ? -1 : 1;
      ctx.font = '600 10.5px ' + COL.mono; ctx.textAlign = 'center'; ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(255,255,255,.9)';
      const sx = X(q[0]) - nc.no[0] * out * 12, sy = Y(q[1]) - nc.no[1] * out * 12; ctx.strokeText(txt, sx, sy); ctx.fillStyle = nc.off ? '#a32616' : '#5a4400'; ctx.fillText(txt, sx, sy);
    }
  }
  // шаг «Комнаты»: выбранная стена, углы, перенос, поворот, новая комната
  if (live && mode === 'rooms') {
    if (RG && RG.g && UI.wall && UI.wall.rid === R.id && UI.wall.i < RG.g.n) {
      const g = RG.g, i = UI.wall.i, Lp = g.poly.length, a = g.wIdx[i], b = i + 1 < g.n ? g.wIdx[i + 1] : Lp;
      ctx.save(); ctx.strokeStyle = COL.tape; ctx.globalAlpha = 0.7; ctx.lineWidth = 10; ctx.lineCap = 'round'; ctx.beginPath();
      for (let kk = a; kk <= b; kk++) { const q = g.poly[kk % Lp]; kk === a ? ctx.moveTo(X(q[0]), Y(q[1])) : ctx.lineTo(X(q[0]), Y(q[1])); }
      ctx.stroke(); ctx.restore();
      const h = midHandle(g, i), hx = X(h[0]), hy = Y(h[1]);
      ctx.beginPath(); ctx.moveTo(hx, hy - 9); ctx.lineTo(hx + 9, hy); ctx.lineTo(hx, hy + 9); ctx.lineTo(hx - 9, hy); ctx.closePath();
      ctx.fillStyle = COL.panel; ctx.fill(); ctx.lineWidth = 2.5; ctx.strokeStyle = COL.tape; ctx.stroke();
    }
    // выбранный проём/ниша и «призрак» при установке: размеры от углов, ручки
    const ir = itemRef();
    if (ir) drawItem(ctx, ir.L, ir.type, ir.x.kind, num(ir.x.pos), num(ir.x.width), num(ir.x.depth), false, ir.x.floor === false);
    if (UI.ghost) drawItem(ctx, UI.ghost.L, UI.ghost.type, UI.ghost.kind, UI.ghost.pos, UI.ghost.width, UI.ghost.depth, true, false);
    if (RG && RG.g && !UI.addTpl && !UI.place) for (const q of RG.g.corners) { ctx.beginPath(); ctx.arc(X(q[0]), Y(q[1]), 7, 0, Math.PI * 2); ctx.fillStyle = COL.panel; ctx.fill(); ctx.lineWidth = 2.5; ctx.strokeStyle = COL.chalk; ctx.stroke(); }
    const h = !UI.addTpl && R && rotHandle(R.id);
    if (h) {
      ctx.strokeStyle = COL.chalk; ctx.lineWidth = 2; ctx.setLineDash([4, 3]); ctx.beginPath(); ctx.moveTo(h.tx, h.ty); ctx.lineTo(h.sx, h.sy + 13); ctx.stroke(); ctx.setLineDash([]);
      ctx.beginPath(); ctx.arc(h.sx, h.sy, 14, 0, Math.PI * 2); ctx.fillStyle = COL.chalk; ctx.fill();
      ctx.strokeStyle = COL.onChalk; ctx.fillStyle = COL.onChalk; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(h.sx, h.sy, 7, -Math.PI * 0.9, Math.PI * 0.55); ctx.stroke();
      const ea = Math.PI * 0.55; arrowHead(ctx, h.sx + Math.cos(ea) * 7, h.sy + Math.sin(ea) * 7, [-Math.sin(ea), Math.cos(ea)]);
      ctx.beginPath(); ctx.arc(h.cx, h.cy, 15, 0, Math.PI * 2); ctx.fillStyle = COL.panel; ctx.fill(); ctx.lineWidth = 2; ctx.strokeStyle = COL.chalk; ctx.stroke();
      ctx.fillStyle = COL.chalk; for (const d of [[1, 0], [-1, 0], [0, 1], [0, -1]]) arrowHead(ctx, h.cx + d[0] * 8, h.cy + d[1] * 8, d);
      ctx.beginPath(); ctx.moveTo(h.cx - 8, h.cy); ctx.lineTo(h.cx + 8, h.cy); ctx.moveTo(h.cx, h.cy - 8); ctx.lineTo(h.cx, h.cy + 8); ctx.strokeStyle = COL.chalk; ctx.lineWidth = 1.6; ctx.stroke();
    }
    if (UI.addPrev) {
      const [a, b] = UI.addPrev, A = [X(Math.min(a[0], b[0])), Y(Math.min(a[1], b[1]))], B = [X(Math.max(a[0], b[0])), Y(Math.max(a[1], b[1]))];
      if (UI.addTpl === 'rect') {
        ctx.fillStyle = 'rgba(29,107,214,.12)'; ctx.fillRect(A[0], A[1], B[0] - A[0], B[1] - A[1]);
        ctx.setLineDash([7, 5]); ctx.strokeStyle = COL.chalk; ctx.lineWidth = 2.5; ctx.strokeRect(A[0], A[1], B[0] - A[0], B[1] - A[1]); ctx.setLineDash([]);
        pillText(ctx, mm(Math.abs(b[0] - a[0])) + ' × ' + mm(Math.abs(b[1] - a[1])) + ' мм', (A[0] + B[0]) / 2, (A[1] + B[1]) / 2, COL.chalk, COL.onChalk, 'center');
      } else { const q = w2s(b[0], b[1]); ctx.beginPath(); ctx.arc(q[0], q[1], 9, 0, Math.PI * 2); ctx.fillStyle = COL.chalk; ctx.fill(); }
    }
  }
  // шаг «Рисунок»: опорная стена и стрелка направления
  const gz = live ? gizmo() : null;
  if (gz) {
    const rw = refWallOf(gz.u);
    if (rw) {
      ctx.save(); ctx.strokeStyle = COL.chalk; ctx.globalAlpha = 0.55; ctx.lineWidth = 9; ctx.lineCap = 'round'; ctx.beginPath(); rw.pts.forEach((q, j) => { const t = w2s(q[0], q[1]); j ? ctx.lineTo(t[0], t[1]) : ctx.moveTo(t[0], t[1]); }); ctx.stroke(); ctx.restore();
      const m = rw.pts[Math.floor(rw.pts.length / 2)], m2 = rw.pts.length === 2 ? [(rw.pts[0][0] + rw.pts[1][0]) / 2, (rw.pts[0][1] + rw.pts[1][1]) / 2] : m, t = w2s(m2[0], m2[1]);
      pillText(ctx, 'опорная стена', t[0], t[1], COL.chalk, COL.onChalk, 'center');
    }
    const { cx, cy, tx, ty, L, F } = gz, e1 = F.e1, a1 = Math.atan2(e1[1], e1[0]), a2 = Math.atan2(F.eu[1], F.eu[0]);
    ctx.save();
    ctx.globalAlpha = 0.6; ctx.fillStyle = COL.panel; ctx.beginPath(); ctx.arc(cx, cy, L + 14, 0, Math.PI * 2); ctx.fill(); ctx.globalAlpha = 1;
    ctx.strokeStyle = COL.muted; ctx.lineWidth = 1; ctx.setLineDash([3, 4]); ctx.beginPath(); ctx.arc(cx, cy, L, 0, Math.PI * 2); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(cx - e1[0] * (L + 10), cy - e1[1] * (L + 10)); ctx.lineTo(cx + e1[0] * (L + 10), cy + e1[1] * (L + 10)); ctx.stroke(); ctx.setLineDash([]);
    let da = a2 - a1; while (da <= -Math.PI) da += 2 * Math.PI; while (da > Math.PI) da -= 2 * Math.PI;
    if (Math.abs(da) > 0.01) { ctx.strokeStyle = COL.tape; ctx.lineWidth = 4; ctx.beginPath(); ctx.arc(cx, cy, L * 0.42, a1, a1 + da, da < 0); ctx.stroke(); }
    ctx.strokeStyle = COL.chalk; ctx.fillStyle = COL.chalk; ctx.lineWidth = 4; ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(cx - F.eu[0] * L * 0.55, cy - F.eu[1] * L * 0.55); ctx.lineTo(tx - F.eu[0] * 14, ty - F.eu[1] * 14); ctx.stroke();
    ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(cx - F.ev[0] * 14, cy - F.ev[1] * 14); ctx.lineTo(cx + F.ev[0] * 14, cy + F.ev[1] * 14); ctx.stroke();
    ctx.beginPath(); ctx.arc(tx, ty, 14, 0, Math.PI * 2); ctx.fill();
    ctx.strokeStyle = COL.onChalk; ctx.fillStyle = COL.onChalk; ctx.lineWidth = 2; ctx.beginPath(); ctx.arc(tx, ty, 7, -Math.PI * 0.9, Math.PI * 0.55); ctx.stroke();
    const ea = Math.PI * 0.55; arrowHead(ctx, tx + Math.cos(ea) * 7, ty + Math.sin(ea) * 7, [-Math.sin(ea), Math.cos(ea)]);
    const mid = a1 + da / 2, P = gz.u.P;
    pillText(ctx, f1(shownAngle(P)) + '°', cx + Math.cos(mid + (Math.abs(da) < 0.3 ? Math.PI : 0)) * L * 0.7, cy + Math.sin(mid + (Math.abs(da) < 0.3 ? Math.PI : 0)) * L * 0.7, COL.tape, '#3b2a00', 'center');
    ctx.restore();
  }
  // линейка
  const want = 90 / s, nice = [100, 200, 500, 1000, 2000, 5000, 10000].find(v => v >= want * 0.6) || 10000, px = nice * s, bx = W - px - 14, by = H - 12;
  ctx.strokeStyle = COL.ink; ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(bx, by - 5); ctx.lineTo(bx, by); ctx.lineTo(bx + px, by); ctx.lineTo(bx + px, by - 5); ctx.stroke();
  ctx.fillStyle = COL.ink; ctx.font = '600 11px ' + COL.mono; ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
  ctx.fillText(nice >= 1000 ? (nice / 1000) + ' м' : nice + ' мм', bx + px / 2, by - 4);
}
/* проём соседней комнаты в общей стене: разрываем и нашу стену напротив него */
function neighborDoorCuts(rid, i, P, u) {
  const out = []; if (!MODEL || !MODEL.adj) return out;
  for (const a of MODEL.adj) {
    if (a.a !== rid || a.i !== i) continue; const G = MODEL.geo[a.b]; if (!G) continue;
    for (const d of G.doors) { if (d.wall !== a.j) continue; const B1 = [d.P[0] + d.u[0] * d.t0, d.P[1] + d.u[1] * d.t0], B2 = [d.P[0] + d.u[0] * d.t1, d.P[1] + d.u[1] * d.t1], t1 = (B1[0] - P[0]) * u[0] + (B1[1] - P[1]) * u[1], t2 = (B2[0] - P[0]) * u[0] + (B2[1] - P[1]) * u[1]; out.push([Math.min(t1, t2), Math.max(t1, t2)]); }
  }
  return out;
}
const selWallOf = it => { const ref = it && itemRef(it); return ref ? ref.r.id + ':' + (ref.x.wall | 0) : ''; };
function drawItem(ctx, L, type, kind, pos, width, depth, ghost, noFloor) {
  const sh = itemShape(L, pos, width, depth, type, kind), P = sh.pts.map(q => w2s(q[0], q[1])), inn = [-L.no[0], -L.no[1]];
  ctx.save(); ctx.lineJoin = 'round';
  ctx.beginPath(); P.forEach((q, k) => k ? ctx.lineTo(q[0], q[1]) : ctx.moveTo(q[0], q[1])); ctx.closePath();
  ctx.fillStyle = type === 'door' ? 'rgba(239,179,0,.55)' : noFloor ? 'rgba(239,179,0,.18)' : 'rgba(239,179,0,.3)'; ctx.fill();
  ctx.strokeStyle = COL.tape; ctx.lineWidth = 3; if (ghost) ctx.setLineDash([6, 4]); ctx.stroke(); ctx.setLineDash([]);
  // засечки по краям и размеры: от угла, ширина, до угла
  const A = w2s(sh.A[0], sh.A[1]), B = w2s(sh.B[0], sh.B[1]), s = view.s;
  ctx.strokeStyle = COL.tape; ctx.lineWidth = 2;
  for (const q of [A, B]) { ctx.beginPath(); ctx.moveTo(q[0] - inn[0] * 6, q[1] - inn[1] * 6); ctx.lineTo(q[0] + inn[0] * 26, q[1] + inn[1] * 26); ctx.stroke(); }
  ctx.font = '600 11px ' + COL.mono; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.lineJoin = 'round';
  const lab = (t0, t1, txt) => { if ((t1 - t0) * s < 28) return; const m = [L.P[0] + L.u[0] * (t0 + t1) / 2, L.P[1] + L.u[1] * (t0 + t1) / 2], q = w2s(m[0], m[1]), x = q[0] + inn[0] * 16, y = q[1] + inn[1] * 16; ctx.lineWidth = 3; ctx.strokeStyle = 'rgba(255,255,255,.92)'; ctx.strokeText(txt, x, y + 0.5); ctx.fillStyle = '#17212b'; ctx.fillText(txt, x, y + 0.5); };
  lab(0, sh.t0, mm(sh.t0)); lab(sh.t1, L.c, mm(L.c - sh.t1));
  const mq = w2s((sh.A[0] + sh.B[0]) / 2, (sh.A[1] + sh.B[1]) / 2);
  pillText(ctx, mm(sh.t1 - sh.t0) + (type === 'niche' ? '×' + mm(depth) : ''), mq[0] + inn[0] * 34 - 0, mq[1] + inn[1] * 34, COL.tape, '#3b2a00', 'center');
  if (!ghost) {
    for (const q of [A, B]) { ctx.beginPath(); ctx.arc(q[0], q[1], 8, 0, Math.PI * 2); ctx.fillStyle = COL.panel; ctx.fill(); ctx.lineWidth = 3; ctx.strokeStyle = COL.tape; ctx.stroke(); }
    if (type === 'niche') { const b = w2s(sh.back[0], sh.back[1]); ctx.beginPath(); ctx.moveTo(b[0], b[1] - 9); ctx.lineTo(b[0] + 9, b[1]); ctx.lineTo(b[0], b[1] + 9); ctx.lineTo(b[0] - 9, b[1]); ctx.closePath(); ctx.fillStyle = COL.panel; ctx.fill(); ctx.lineWidth = 2.5; ctx.strokeStyle = COL.tape; ctx.stroke(); }
  }
  ctx.restore();
}
function midHandle(g, i) { const P = g.corners[i], Q = g.corners[(i + 1) % g.n], u = unitV(P, Q), n = g.sgn > 0 ? [u[1], -u[0]] : [-u[1], u[0]], h = g.arcs[i] || 0; return [(P[0] + Q[0]) / 2 + n[0] * h, (P[1] + Q[1]) / 2 + n[1] * h]; }
function arrowHead(ctx, x, y, d) { const a = Math.atan2(d[1], d[0]); ctx.beginPath(); ctx.moveTo(x + Math.cos(a) * 8, y + Math.sin(a) * 8); ctx.lineTo(x + Math.cos(a + 2.5) * 8, y + Math.sin(a + 2.5) * 8); ctx.lineTo(x + Math.cos(a - 2.5) * 8, y + Math.sin(a - 2.5) * 8); ctx.closePath(); ctx.fill(); }
function pillText(ctx, text, x, y, bg, fg, align) {
  ctx.font = '600 11px ' + COL.body; const w = ctx.measureText(text).width + 14, h = 20, bx = align === 'left' ? x : x - w / 2;
  ctx.fillStyle = bg; ctx.beginPath(); const r = 10; ctx.moveTo(bx + r, y - h / 2); ctx.arcTo(bx + w, y - h / 2, bx + w, y + h / 2, r); ctx.arcTo(bx + w, y + h / 2, bx, y + h / 2, r); ctx.arcTo(bx, y + h / 2, bx, y - h / 2, r); ctx.arcTo(bx, y - h / 2, bx + w, y - h / 2, r); ctx.closePath(); ctx.fill();
  ctx.fillStyle = fg; ctx.textAlign = 'left'; ctx.textBaseline = 'middle'; ctx.fillText(text, bx + 7, y + 0.5);
}

function resizeCanvas() {
  const r = cv.getBoundingClientRect(); DPR = window.devicePixelRatio || 1;
  CW = Math.max(50, r.width); CH = Math.max(50, r.height);
  cv.width = Math.round(CW * DPR); cv.height = Math.round(CH * DPR);
  if (!view.fitted) fitView(); draw();
}
function floorBBox() { const pts = []; for (const r of S.rooms) { const G = MODEL && MODEL.geo[r.id]; const g = G && G.g ? G.g : roomGeom(r); pts.push(...g.poly); } return pts.length ? bboxOf(pts) : null; }
function fitView() {
  const b = floorBBox(); if (!b) return;
  // сверху запас под ручку поворота комнаты
  const m = CW < 560 ? 44 : 56, top = 22, w = Math.max(1, b.u1 - b.u0), h = Math.max(1, b.v1 - b.v0);
  view.s = Math.min((CW - 2 * m) / w, (CH - 2 * m - top) / h); view.cx = (b.u0 + b.u1) / 2; view.cy = (b.v0 + b.v1) / 2 - top / 2 / view.s; view.fitted = true;
}
let drawQueued = false;
function draw() { if (drawQueued) return; drawQueued = true; requestAnimationFrame(() => { drawQueued = false; render(cv.getContext('2d'), CW, CH, view, { k: DPR, style: UI.style, labels: UI.labels, live: true }); }); }

/* ================= пересчёт и сохранение черновика ================= */
let computeQueued = false, panelTimer = 0, saveTimer = 0;
function recompute() { MODEL = computeAll(); fixTargets(); draw(); renderStatus(); renderPieceInfo(); }
function invalidate(opts) {
  opts = opts || {};
  if (!computeQueued) { computeQueued = true; requestAnimationFrame(() => { computeQueued = false; recompute(); }); }
  clearTimeout(panelTimer); panelTimer = setTimeout(() => { refreshLight(); if (UI.tab === 'res') renderResults(); }, opts.fast ? 0 : 220);
  clearTimeout(saveTimer); saveTimer = setTimeout(() => lsSet(KEY_DRAFT, JSON.stringify(S)), 600);
}
function refreshLight() { renderRoomList(); renderRoomKV(); renderClosure(); renderWallHints(); renderRoomSums(); renderSums(); }
/* краткие итоги в заголовках свёрнутых разделов */
function renderSums() {
  const set = (id, t) => { const el = $('#' + id); if (el) el.textContent = t; };
  const m = curMat(false); set('plankSum', mm(num(m.L)) + '×' + mm(num(m.W)) + (num(m.T) ? '×' + f1(num(m.T)) : '') + ' мм');
  set('mountSum', 'зазор ' + mm(num(S.set.gap)) + ' мм · запас ' + f1(num(S.set.reserve)) + '%');
  const P = curP(), kind = targetKind(UI.target);
  set('dirSum', kind === 'ins' ? f1(shownAngle(P)) + '°' : 'стена ' + ((num(P.refWall) | 0) + 1) + ' · ' + f1(shownAngle(P)) + '°');
  set('offSum', kind === 'border' ? mm(num(P.offA)) + ' мм' : mm(num(P.offB)) + ' / ' + mm(num(P.offA)) + ' мм');
  set('rulesSum', 'узкая < ' + mm(num(P.minEdge, 25)) + ' мм');
}

/* ================= участки: что настраиваем ================= */
function unitName(key) {
  const r = MODEL && MODEL.byKey[key]; if (r) return r.unit.name;
  if (key === 'floor') return 'Общий рисунок';
  const [k, rid, iid] = key.split(':'), rr = room(rid); if (!rr) return key;
  if (k === 'room') return rr.name + ': свой рисунок'; if (k === 'border') return rr.name + ': рамка';
  return rr.name + ': вставка ' + ((rr.inserts || []).findIndex(x => x.id === iid) + 1);
}
function availTargets() { const geo = MODEL ? MODEL.geo : computeGeo(S); return unitKeys(S, geo); }
function fixTargets() {
  if (!room(UI.room)) UI.room = S.rooms[0] && S.rooms[0].id;
  const keys = availTargets();
  if (!keys.includes(UI.target)) UI.target = keys[0] || 'floor';
  const mk = matKeys(); if (!mk.includes(UI.matTarget)) UI.matTarget = 'main';
}
function patOf(key) {
  if (key === 'floor') return S.floorPat;
  const [k, rid, iid] = key.split(':'), r = room(rid); if (!r) return S.floorPat;
  if (k === 'room') return r.pat; if (k === 'border') return r.border.pat;
  const ins = (r.inserts || []).find(x => x.id === iid); return ins ? ins.pat : S.floorPat;
}
const curP = () => patOf(UI.target);
const targetKind = key => key === 'floor' ? 'floor' : key.split(':')[0];
function matKeys() {
  const out = ['main'];
  for (const r of S.rooms) { if (r.own) out.push('room:' + r.id); if (r.border && r.border.on) out.push('border:' + r.id); for (const x of r.inserts || []) out.push('ins:' + r.id + ':' + x.id); }
  return out;
}
function matHolder(key) {
  if (key === 'main') return null; const [k, rid, iid] = key.split(':'), r = room(rid); if (!r) return null;
  if (k === 'room') return r; if (k === 'border') return r.border; return (r.inserts || []).find(x => x.id === iid) || null;
}
function curMat(createOwn) {
  if (UI.matTarget === 'main') return S.mat; const h = matHolder(UI.matTarget); if (!h) return S.mat;
  if (!h.mat && createOwn) h.mat = deep(S.mat);
  return h.mat || S.mat;
}
function matForKey(key) { if (key === 'floor') return S.mat; const h = matHolder(key); return (h && h.mat) || S.mat; }
function matKeyName(key) { if (key === 'main') return 'Основное'; const [k, rid, iid] = key.split(':'), r = room(rid); if (!r) return key; if (k === 'room') return r.name; if (k === 'border') return 'Рамка: ' + r.name; return 'Вставка ' + ((r.inserts || []).findIndex(x => x.id === iid) + 1) + ': ' + r.name; }

/* ================= строка состояния и сообщения ================= */
let msgTimer = 0;
function say(text, kind, sticky) { const el = $('#msg'); el.textContent = text; el.className = 'msg' + (kind ? ' ' + kind : ''); clearTimeout(msgTimer); if (!sticky) msgTimer = setTimeout(modeHint, clamp(3000 + text.length * 50, 4000, 12000)); }
const MODE_HINT = {
  rooms: 'Нажмите на комнату — выберу её, на стену — проём, ниша, дуга. Выбранную комнату тяните пальцем, круглая ручка — поворот.',
  view: 'Нажмите на доску — покажу, как её пилить. Карту двигайте пальцем, масштаб — двумя пальцами.',
  pattern: 'Тяните рисунок пальцем, карту — двумя пальцами. Ручка на стрелке поворачивает рисунок, касание стены — рисунок вдоль неё.',
};
function modeHint() { const el = $('#msg'); el.className = 'msg'; el.textContent = MODE_HINT[UI.mode] || ''; }
function renderStatus() {
  const el = $('#status'); if (!MODEL) { el.innerHTML = ''; return; }
  const errs = S.rooms.filter(r => MODEL.geo[r.id] && MODEL.geo[r.id].err), parts = [];
  const res = MODEL.byKey[UI.target] || MODEL.units[0];
  if (errs.length) parts.push('<span class="pill bad">Ошибка: ' + esc(errs.map(r => r.name).join(', ')) + '</span>');
  const ov = overlaps(); if (ov) parts.push('<span class="pill bad">Наложились: ' + esc(ov) + '</span>');
  if (UI.mode === 'rooms') {
    let A = 0; for (const r of S.rooms) { const G = MODEL.geo[r.id]; if (G && G.g && !G.err) A += Math.abs(area(G.g.poly)); }
    parts.push('<span class="pill">' + S.rooms.length + ' ' + plural(S.rooms.length, 'комната', 'комнаты', 'комнат') + ' · ' + fm2(A) + ' м²</span>');
    const nd = S.rooms.reduce((t, r) => t + MODEL.geo[r.id].doors.length, 0); if (nd) parts.push('<span class="pill">' + nd + ' ' + plural(nd, 'проём', 'проёма', 'проёмов') + '</span>');
  }
  if (res) {
    if (UI.mode === 'pattern' && MODEL.units.length > 1) parts.push('<span class="pill info">' + esc(res.unit.name) + '</span>');
    if (res.err) parts.push('<span class="pill bad">' + esc(res.err) + '</span>');
    else if (UI.mode !== 'rooms' || !errs.length) {
      const st = res.stats, tot = MODEL.mats.reduce((t, m) => t + m.boards, 0);
      if (UI.mode !== 'rooms') parts.push('<span class="pill">Целых ' + st.nFull + '</span>', '<span class="pill warn">Подрезок ' + st.nCut + '</span>');
      if (st.nCut && UI.mode !== 'rooms') parts.push('<span class="pill ' + (st.nBad ? 'bad' : 'ok') + '">' + (st.nBad ? 'Узких ' + st.nBad + ' · ' + mm(st.minT) + ' мм' : 'Мин. ' + mm(st.minT) + ' мм') + '</span>');
      parts.push('<span class="pill">Нужно ' + tot + ' шт</span>');
    }
  }
  el.innerHTML = parts.join(''); fadeMore(el);
}

function overlaps() {
  const ok = S.rooms.map(r => [r, MODEL.geo[r.id]]).filter(([, G]) => G && G.g && !G.err);
  for (let i = 0; i < ok.length; i++) for (let j = i + 1; j < ok.length; j++) {
    const A = ok[i][1].lay, B = ok[j][1].lay, ba = bboxOf(A), bb = bboxOf(B);
    if (ba.u1 <= bb.u0 + 1 || bb.u1 <= ba.u0 + 1 || ba.v1 <= bb.v0 + 1 || bb.v1 <= ba.v0 + 1) continue;
    const inside = (P, Q) => P.some(q => inPoly(q[0], q[1], Q) && E.minEdgeDist(q[0], q[1], Q) > 1) || inPoly(...centroid(P), Q);
    if (inside(A, B) || inside(B, A)) return ok[i][0].name + ' и ' + ok[j][0].name;
  }
  return '';
}

/* ================= карточка подрезки (в панели) ================= */
function selectedPiece() {
  if (!UI.sel || !MODEL) return null; const res = MODEL.byKey[UI.sel.key]; if (!res || res.err) return null;
  const idx = res.pieces.findIndex(p => p.id === UI.sel.id); return idx < 0 ? null : { res, p: res.pieces[idx], idx };
}
function renderPieceInfo() {
  const el = $('#pieceInfo'), sp = selectedPiece();
  if (!sp) { el.hidden = true; syncTgBack(); return; }
  const { res, p } = sp, u = res.unit, spec = p.spec || cutSpec(p), grp = p.gk ? res.groups.find(g => g.key === p.gk) : null;
  const kindName = p.kind === 'A' ? (patDef(u.P.type).group === 'basket' ? 'вдоль' : 'тип A (левая)') : p.kind === 'B' ? (patDef(u.P.type).group === 'basket' ? 'поперёк' : 'тип B (правая)') : '';
  let rowInfo = ''; if (res.rows) { const ri = res.rows.findIndex(x => x.k === p.row); if (ri >= 0) rowInfo = 'ряд ' + (ri + 1) + ' из ' + res.rows.length; }
  const src = p.src === 'pool' ? 'из обрезка' : p.src === 'new' ? 'от новой планки' : '';
  el.innerHTML = '<header><b>' + (p.full ? 'Целая планка' : 'Подрезка') + (kindName ? ' <span class="tag">' + kindName + '</span>' : '') + '</b>' +
    '<button class="icon" type="button" data-act="piece-close" aria-label="Закрыть">' + ICON.del + '</button></header>' +
    '<canvas id="pieceCv"></canvas><ul>' + spec.lines.map(l => '<li>' + esc(l) + '</li>').join('') + '</ul>' +
    '<div class="meta">' + [esc(u.name), rowInfo, src, (!p.full ? 'самое узкое место ≈ ' + mm(p.thick) + ' мм' : ''), grp && grp.idx.length > 1 ? 'таких же: ' + grp.idx.length + ' шт' : ''].filter(Boolean).join(' · ') + '</div>' +
    (grp && grp.idx.length > 1 ? '<button class="btn small" type="button" data-act="piece-hl">' + (UI.hl && UI.hl.gk === p.gk ? 'Снять подсветку' : 'Показать все такие на плане') + '</button>' : '');
  el.hidden = false;
  drawPlank($('#pieceCv'), p, u.mat); syncTgBack();
}
function drawPlank(c, p, M) {
  const dpr = window.devicePixelRatio || 1, w = c.clientWidth || 300, h = c.clientHeight || 112; c.width = w * dpr; c.height = h * dpr;
  const ctx = c.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, w, h);
  const fr = p.fr, out = plankOutline(fr), partsP = p.parts.map(q => plankPts(p, q)), b = bboxOf(out.concat(...partsP));
  const pad = 24, s = Math.min((w - 2 * pad) / (b.u1 - b.u0), (h - 2 * pad) / (b.v1 - b.v0));
  const ox = (w - (b.u1 - b.u0) * s) / 2 - b.u0 * s, oy = (h - (b.v1 - b.v0) * s) / 2 - b.v0 * s, P = q => [q[0] * s + ox, q[1] * s + oy];
  const poly = arr => { ctx.beginPath(); arr.forEach((q, i) => { const r = P(q); i ? ctx.lineTo(r[0], r[1]) : ctx.moveTo(r[0], r[1]); }); ctx.closePath(); };
  ctx.setLineDash([4, 4]); ctx.strokeStyle = COL.muted; ctx.lineWidth = 1; poly(out); ctx.stroke(); ctx.setLineDash([]);
  for (const pts of partsP) {
    ctx.fillStyle = p.full ? p.col : rgb(mix((TONES[M.tone] || TONES.oak).c, [242, 183, 5], 0.35)); poly(pts); ctx.fill();
    ctx.strokeStyle = COL.wall; ctx.lineWidth = 1.2; poly(pts); ctx.stroke();
    ctx.strokeStyle = COL.bad; ctx.lineWidth = 2.5;
    for (let i = 0, n = pts.length; i < n; i++) {
      const a = pts[i], q = pts[(i + 1) % n]; let fac = false;
      for (let k = 0; k < 4; k++) if (onLine(a, q, out[k], out[(k + 1) % 4], 0.6)) { fac = true; break; }
      if (fac || dist(a, q) < 1) continue;
      const A = P(a), B = P(q); ctx.beginPath(); ctx.moveTo(A[0], A[1]); ctx.lineTo(B[0], B[1]); ctx.stroke();
    }
  }
  const pts = plankPts(p, mainPart(p));
  ctx.font = '600 11px ' + COL.mono; ctx.fillStyle = COL.ink; ctx.textAlign = 'center';
  const edgeExt = y0 => { let lo = Infinity, hi = -Infinity; for (let i = 0, n = pts.length; i < n; i++) { const a = pts[i], q = pts[(i + 1) % n]; if (Math.abs(a[1] - y0) < 0.6 && Math.abs(q[1] - y0) < 0.6) { lo = Math.min(lo, a[0], q[0]); hi = Math.max(hi, a[0], q[0]); } } return hi > lo + 0.5 ? [lo, hi] : null; };
  const e0 = edgeExt(0), e1 = edgeExt(fr.W);
  if (e0) { const A = P([e0[0], 0]), B = P([e0[1], 0]); ctx.textBaseline = 'bottom'; ctx.fillText(mm(e0[1] - e0[0]), (A[0] + B[0]) / 2, Math.min(A[1], B[1]) - 4); }
  if (e1) { const A = P([e1[0], fr.W]), B = P([e1[1], fr.W]); ctx.textBaseline = 'top'; ctx.fillText(mm(e1[1] - e1[0]), (A[0] + B[0]) / 2, Math.max(A[1], B[1]) + 4); }
  const yb = bboxOf(pts); if (yb.v1 - yb.v0 < fr.W - 0.6) { const A = P([yb.u1, yb.v0]), B = P([yb.u1, yb.v1]); ctx.textAlign = 'left'; ctx.textBaseline = 'middle'; ctx.fillText(mm(yb.v1 - yb.v0), Math.max(A[0], B[0]) + 5, (A[1] + B[1]) / 2); }
}

/* ================= работа с картой ================= */
const ptrs = new Map(); let gest = null;
const s2w = (x, y) => [(x - CW / 2) / view.s + view.cx, (y - CH / 2) / view.s + view.cy];
const w2s = (x, y) => [(x - view.cx) * view.s + CW / 2, (y - view.cy) * view.s + CH / 2];
const rot2 = (p, c, a) => { const cs = Math.cos(a), sn = Math.sin(a), dx = p[0] - c[0], dy = p[1] - c[1]; return [c[0] + dx * cs - dy * sn, c[1] + dx * sn + dy * cs]; };
function roomAt(w) { for (let i = S.rooms.length - 1; i >= 0; i--) { const G = MODEL && MODEL.geo[S.rooms[i].id]; if (G && G.g && inPoly(w[0], w[1], G.g.poly)) return S.rooms[i].id; } return null; }
function roomCenter(r) { const G = MODEL && MODEL.geo[r.id], g = G && G.g ? G.g : roomGeom(r); return centroid(g.poly); }
function rotHandle(rid) {
  const G = MODEL && MODEL.geo[rid]; if (!G || !G.g) return null;
  // ручка поворота над комнатой, правее середины — там, где не стоит подпись длины стены
  const b = bboxOf(G.g.poly), C = centroid(G.g.poly), top = w2s(C[0], b.v0), c = w2s(C[0], C[1]), right = w2s(b.u1, b.v0)[0];
  const x = Math.max(top[0], Math.min(right - 6, top[0] + 70));
  return { C, sx: x, sy: top[1] - 36, tx: x, ty: top[1], cx: c[0], cy: c[1] };
}
function rotateRoomBy(r, deg) { const C = roomCenter(r), p = rot2([num(r.x0), num(r.y0)], C, deg * DEG); r.x0 = Math.round(p[0]); r.y0 = Math.round(p[1]); r.a0 = mod(num(r.a0) + deg, 360); }
/* углы прилипают к 90°, 45° и 15° */
function snapAngle(a) { for (const [step, tol] of [[90, 5], [45, 3], [15, 2]]) { const k = Math.round(a / step) * step; if (Math.abs(a - k) < tol) return k; } return Math.round(a); }
/* точка прилипает к углам других комнат с учётом толщины стены */
function snapPoint(w, skipRid) {
  const T = Math.max(0, num(S.set.wallT, 120)), th = 14 / view.s; let bx = null, by = null;
  for (const o of S.rooms) {
    if (o.id === skipRid) continue; const G = MODEL && MODEL.geo[o.id]; if (!G || !G.g) continue;
    for (const c of G.g.corners) for (const kk of [0, T, -T]) {
      const sx = c[0] + kk - w[0], sy = c[1] + kk - w[1];
      if (Math.abs(sx) < th && (bx === null || Math.abs(sx) < Math.abs(bx))) bx = sx;
      if (Math.abs(sy) < th && (by === null || Math.abs(sy) < Math.abs(by))) by = sy;
    }
  }
  return [Math.round(bx !== null ? w[0] + bx : Math.round(w[0] / 10) * 10), Math.round(by !== null ? w[1] + by : Math.round(w[1] / 10) * 10)];
}
/* направление рисунка: стрелка на карте и поворот вокруг центра области */
function dirRegion(u) { return u.kind === 'ins' ? u.ins.region : MODEL.geo[u.refRoom].center; }
function dirCtx(key) {
  const res = MODEL && MODEL.byKey[key]; if (!res || res.err || res.unit.kind === 'border') return null;
  const u = res.unit, F = u.parts[0].frame, C = centroid(dirRegion(u)), L = F.toL(C);
  return { A: F.A, e1: F.e1, e2: F.e2, C, cu: L[0], cv: L[1] };
}
const fullAngle = P => mod(E.dirDeg(P) + (P.flipU ? 180 : 0), 360);
function shownAngle(P) { const g = patDef(P.type).group, a = fullAngle(P); return g === 'bond' || g === 'basket' ? mod(a, 180) : a; }
/* θ — куда смотрит стрелка относительно опорной стены; рисунок поворачивается вокруг центра комнаты */
function setDirection(P, theta, c) {
  let rho = mod((P.flipU ? theta - 180 : theta) + 180, 360) - 180; rho = Math.round(rho * 10) / 10;
  P.dir = Math.abs(rho) < 0.05 ? 'along' : Math.abs(rho - 90) < 0.05 ? 'across' : Math.abs(rho - 45) < 0.05 ? 'diag' : 'custom';
  if (P.dir === 'custom') P.angle = rho;
  if (!c) return;
  const F1 = E.makeFrame(c.A, c.e1, c.e2, Object.assign({}, P, { offA: 0, offB: 0 }));
  const O = [c.C[0] - (c.cu * F1.eu[0] + c.cv * F1.ev[0]), c.C[1] - (c.cu * F1.eu[1] + c.cv * F1.ev[1])];
  P.offA = Math.round((O[0] - c.A[0]) * c.e1[0] + (O[1] - c.A[1]) * c.e1[1]);
  P.offB = Math.round((O[0] - c.A[0]) * c.e2[0] + (O[1] - c.A[1]) * c.e2[1]);
}
function gizmo() {
  if (!MODEL || UI.mode !== 'pattern') return null;
  const res = MODEL.byKey[UI.target]; if (!res || res.err || res.unit.kind === 'border') return null;
  const u = res.unit, F = u.parts[0].frame, C = centroid(dirRegion(u)), c = w2s(C[0], C[1]), L = Math.round(clamp(Math.min(CW, CH) * 0.17, 38, 62));
  return { res, u, F, C, cx: c[0], cy: c[1], tx: c[0] + F.eu[0] * L, ty: c[1] + F.eu[1] * L, L };
}
function refWallOf(u) {
  if (!u || u.kind === 'ins' || u.kind === 'border') return null;
  const G = MODEL.geo[u.refRoom]; if (!G || !G.g) return null;
  const g = G.g, i = clamp(num(u.P.refWall) | 0, 0, g.n - 1), Lp = g.poly.length, s = g.wIdx[i], e = i + 1 < g.n ? g.wIdx[i + 1] : Lp, pts = [];
  for (let k = s; k <= e; k++) pts.push(g.poly[k % Lp]);
  return { pts, i, rid: u.refRoom };
}
function wallAt(sx, sy, rids) {
  let best = 16, hit = null;
  for (const rid of rids) {
    const G = MODEL.geo[rid]; if (!G || !G.g) continue; const g = G.g;
    for (let i = 0; i < g.n; i++) { if (Math.abs(g.arcs[i]) >= 0.5) continue; const a = w2s(g.corners[i][0], g.corners[i][1]), q = g.corners[(i + 1) % g.n], b = w2s(q[0], q[1]), d = segDist(sx, sy, a, b); if (d < best) { best = d; hit = { rid, i }; } }
  }
  return hit;
}
/* ================= проёмы и ниши на карте: поставить, двигать, менять размер ================= */
const DOOR_MIN = 300, NICHE_MIN = 100;
function wallLine(g, i) { const P = g.corners[i], Q = g.corners[(i + 1) % g.n], u = unitV(P, Q); return { P, Q, u, c: dist(P, Q), no: g.sgn > 0 ? [u[1], -u[0]] : [-u[1], u[0]] }; }
const straightWall = (g, i) => i >= 0 && i < g.n && Math.abs(g.arcs[i]) < 0.5 && dist(g.corners[i], g.corners[(i + 1) % g.n]) >= 200;
/* выбранный проём или ниша: { type, rid, id } → данные и геометрия */
function itemRef(it) {
  it = it || UI.item; if (!it || !MODEL) return null;
  const r = room(it.rid); if (!r) return null;
  const x = ((it.type === 'door' ? r.doors : r.niches) || []).find(q => q.id === it.id); if (!x) return null;
  const G = MODEL.geo[r.id]; if (!G || !G.g || !straightWall(G.g, x.wall | 0)) return null;
  return { r, x, G, g: G.g, type: it.type, L: wallLine(G.g, x.wall | 0) };
}
/* контур на стене: A–B по линии стены, для ниши и выступа — прямоугольник вглубь или внутрь */
function itemShape(L, pos, width, depth, type, kind) {
  const t0 = clamp(pos, 0, L.c), t1 = clamp(pos + width, t0, L.c), at = (t, e) => [L.P[0] + L.u[0] * t + L.no[0] * e, L.P[1] + L.u[1] * t + L.no[1] * e];
  const T = Math.max(0, num(S.set.wallT, 120)), k = type === 'door' ? T : kind === 'box' ? -depth : depth;
  return { t0, t1, A: at(t0, 0), B: at(t1, 0), pts: [at(t0, 0), at(t0, k), at(t1, k), at(t1, 0)], back: at((t0 + t1) / 2, k) };
}
const shapeOf = ref => itemShape(ref.L, num(ref.x.pos), num(ref.x.width), num(ref.x.depth), ref.type, ref.x.kind);
/* что под пальцем: проём (любой комнаты) или ниша/выступ */
function itemHit(sx, sy) {
  let best = 14, hit = null;
  for (const r of S.rooms) {
    const G = MODEL.geo[r.id]; if (!G || !G.g) continue;
    for (const d of r.doors || []) {
      const ref = itemRef({ type: 'door', rid: r.id, id: d.id }); if (!ref) continue; const sh = shapeOf(ref);
      const a = w2s(sh.A[0], sh.A[1]), b = w2s(sh.B[0], sh.B[1]), e = w2s(sh.pts[2][0], sh.pts[2][1]), f = w2s(sh.pts[1][0], sh.pts[1][1]);
      const dd = inPoly(sx, sy, [a, b, e, f]) ? 0 : Math.min(segDist(sx, sy, a, b), segDist(sx, sy, f, e));
      if (dd < best) { best = dd; hit = { type: 'door', rid: r.id, id: d.id }; }
    }
    for (const x of r.niches || []) {
      const ref = itemRef({ type: 'niche', rid: r.id, id: x.id }); if (!ref) continue; const sh = shapeOf(ref), sp = sh.pts.map(q => w2s(q[0], q[1]));
      let dd = inPoly(sx, sy, sp) ? 0 : Infinity; for (let k = 0; k < 3; k++) dd = Math.min(dd, segDist(sx, sy, sp[k], sp[k + 1]));
      if (dd < best || (dd === 0 && best === 0)) { best = dd; hit = { type: 'niche', rid: r.id, id: x.id }; }
    }
  }
  return hit;
}
/* ручки выбранного: края (ширина) и задняя стенка ниши (глубина) */
function itemHandles() {
  const ref = itemRef(); if (!ref) return null; const sh = shapeOf(ref);
  return { ref, sh, ends: [w2s(sh.A[0], sh.A[1]), w2s(sh.B[0], sh.B[1])], depth: ref.type === 'niche' ? w2s(sh.back[0], sh.back[1]) : null };
}
/* ближайшая прямая стена к точке (в пикселях экрана); rid — только эта комната */
function nearestWall(w, rid, maxPx) {
  let best = null;
  for (const r of S.rooms) {
    if (rid && r.id !== rid) continue; const G = MODEL.geo[r.id]; if (!G || !G.g) continue;
    for (let i = 0; i < G.g.n; i++) {
      if (!straightWall(G.g, i)) continue; const L = wallLine(G.g, i), t = clamp((w[0] - L.P[0]) * L.u[0] + (w[1] - L.P[1]) * L.u[1], 0, L.c);
      const X = [L.P[0] + L.u[0] * t, L.P[1] + L.u[1] * t], d = dist(w, X) * view.s - (r.id === UI.room ? 2 : 0);
      if (d < (maxPx || 1e9) && (!best || d < best.d)) best = { rid: r.id, i, t, d, L };
    }
  }
  return best;
}
/* прилипание: к углам, к середине стены и к краям общей стены с соседней комнатой */
function snapPos(rid, i, L, pos, width) {
  const th = 12 / view.s, cands = [0, L.c - width, (L.c - width) / 2];
  for (const a of MODEL.adj || []) if (a.a === rid && a.i === i) cands.push(a.o0, a.o1 - width, (a.o0 + a.o1 - width) / 2);
  let best = null; for (const c of cands) { const d = Math.abs(c - pos); if (d < th && (best === null || d < Math.abs(best - pos))) best = c; }
  return clamp(best !== null ? best : Math.round(pos / 10) * 10, 0, Math.max(0, L.c - width));
}
function snapEdge(rid, i, L, t) {
  const th = 12 / view.s, cands = [0, L.c, L.c / 2];
  for (const a of MODEL.adj || []) if (a.a === rid && a.i === i) cands.push(a.o0, a.o1);
  let best = null; for (const c of cands) { const d = Math.abs(c - t); if (d < th && (best === null || d < Math.abs(best - t))) best = c; }
  return clamp(best !== null ? best : Math.round(t / 10) * 10, 0, L.c);
}
/* проём после переноса: в общей стене с соседом — ведёт к нему (и не шире общей части), иначе — наружу */
function doorLink(r, d) {
  const geo = computeGeo(S), list = adjacency(S, geo).filter(a => a.a === r.id && a.i === (d.wall | 0)), mid = num(d.pos) + num(d.width) / 2;
  const a = list.find(x => mid >= x.o0 && mid <= x.o1);
  if (a) {
    const span = a.o1 - a.o0; d.width = Math.min(num(d.width), Math.floor(span)); d.pos = Math.round(clamp(num(d.pos), a.o0, a.o1 - d.width));
    d.to = a.b; d.auto = true; if (d.width >= span - 1) d.full = true; else delete d.full;
    S.noDoor = (S.noDoor || []).filter(k => k !== pairKey(r.id, a.b));
  } else {
    const old = d.to; delete d.to; delete d.auto; delete d.full;
    if (old && !S.rooms.some(o => (o.doors || []).some(q => q !== d && (q.to === old || (o.id === old && q.to === r.id))))) { S.noDoor = S.noDoor || []; const k = pairKey(r.id, old); if (!S.noDoor.includes(k)) S.noDoor.push(k); }
  }
}
function itemText(ref) {
  const x = ref.x, p = num(x.pos), w = num(x.width), rest = ref.L.c - p - w;
  const name = ref.type === 'door' ? (x.full ? 'Проход' : 'Проём') : x.kind === 'box' ? 'Выступ' : 'Ниша';
  return name + ' ' + mm(w) + (ref.type === 'niche' ? '×' + mm(x.depth) : '') + ' мм на стене ' + ((x.wall | 0) + 1) + ': от угла ' + mm(p) + ', до угла ' + mm(Math.max(0, rest)) + ' мм';
}
function selectItem(it, quiet) {
  UI.item = it; UI.wall = null; UI.delArm = null; UI.room = it.rid; UI.open[it.type === 'door' ? 'doors' : 'niches'] = true;
  renderPlanTab(); renderCtxbar(); draw(); PF.haptic('select');
  const row = $('.orow[data-item="' + it.id + '"]'); if (row && row.scrollIntoView) row.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  const ref = itemRef(); if (ref && !quiet) say(itemText(ref) + '. Тяните его по стене, за кружки на краях — ширина' + (ref.type === 'niche' ? ', за ромб — глубина' : '') + '.');
}
/* стена под пальцем (любая комната, дуги тоже); t — место касания вдоль стены */
function wallHit(sx, sy) {
  let best = 18, hit = null;
  for (const r of S.rooms) {
    const G = MODEL.geo[r.id]; if (!G || !G.g) continue; const g = G.g, Lp = g.poly.length;
    for (let i = 0; i < g.n; i++) {
      const a0 = g.wIdx[i], b0 = i + 1 < g.n ? g.wIdx[i + 1] : Lp;
      for (let kk = a0; kk < b0; kk++) { const A = w2s(g.poly[kk % Lp][0], g.poly[kk % Lp][1]), B = w2s(g.poly[(kk + 1) % Lp][0], g.poly[(kk + 1) % Lp][1]), d = segDist(sx, sy, A, B) - (r.id === UI.room ? 3 : 0); if (d < best) { best = d; hit = { rid: r.id, i }; } }
    }
  }
  if (hit) { const g = MODEL.geo[hit.rid].g, P = g.corners[hit.i], Q = g.corners[(hit.i + 1) % g.n], w = s2w(sx, sy), u = unitV(P, Q); hit.t = Math.round(clamp((w[0] - P[0]) * u[0] + (w[1] - P[1]) * u[1], 0, dist(P, Q))); }
  return hit;
}
function wallText(r, i) {
  const G = MODEL && MODEL.geo[r.id], g = G && G.g; if (!g || i >= g.n) return '';
  const c = dist(g.corners[i], g.corners[(i + 1) % g.n]), js = (MODEL.adj || []).filter(a => a.a === r.id && a.i === i);
  let t = 'Стена ' + (i + 1) + ' · ' + mm(c) + ' мм';
  if (js.length) t += ': ' + jointSegs(c, js).map(sg => mm(sg.len) + (sg.to ? ' общая с «' + roomName(sg.to) + '»' : '')).join(' + ');
  return t;
}
/* части стены между стыками с соседними комнатами */
function jointSegs(c, js) {
  const bps = [0, c]; for (const a of js) bps.push(a.o0, a.o1);
  bps.sort((a, b) => a - b); const br = []; for (const b of bps) if (!br.length || b - br[br.length - 1] > 5) br.push(b); else br[br.length - 1] = Math.max(br[br.length - 1], b);
  const out = []; for (let j = 0; j + 1 < br.length; j++) { const a = br[j], b = br[j + 1], x = js.find(q => a >= q.o0 - 3 && b <= q.o1 + 3); out.push({ a, b, len: b - a, to: x ? x.b : null }); }
  return out;
}
function selectWall(wh) {
  const r = room(wh.rid); if (!r) return;
  UI.room = wh.rid; UI.wall = wh; UI.item = null; UI.wallFocus = wh.i; UI.open.walls = true; UI.delArm = null; UI.addRoom = false;
  renderPlanTab(); renderCtxbar(); draw(); saveUI(); PF.haptic('select');
  const c = $('.wcard[data-wi="' + wh.i + '"]'); if (c && c.scrollIntoView) c.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  say(wallText(r, wh.i) + '. Под картой: проём, ниша, выступ, дуга. Ромб на стене выгибает её.');
}
function startGesture() {
  const pts = [...ptrs.values()];
  if (pts.length >= 2) { const a = pts[0], b = pts[1], mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2; gest = { type: 'pinch', d0: Math.hypot(a.x - b.x, a.y - b.y) || 1, s0: view.s, w: s2w(mx, my), moved: true }; UI.addPrev = null; return; }
  const p = pts[0], R = curRoom(), RG = R && MODEL && MODEL.geo[R.id];
  gest = { type: 'pan', sx: p.x, sy: p.y, moved: false, cx: view.cx, cy: view.cy };
  if (UI.mode === 'pattern') {
    const gz = gizmo();
    if (gz && Math.hypot(p.x - gz.tx, p.y - gz.ty) < 26) { Object.assign(gest, { type: 'prot', c: dirCtx(UI.target), P: curP() }); return; }
    const res = MODEL && MODEL.byKey[UI.target];
    if (res && !res.err) { const P = curP(), F = res.unit.parts[0].frame; Object.assign(gest, { type: 'pattern', P, F, offA: num(P.offA), offB: num(P.offB), kind: res.unit.kind }); }
  } else if (UI.mode === 'rooms') {
    if (UI.addTpl) { Object.assign(gest, { type: 'add', w0: snapPoint(s2w(p.x, p.y), null) }); return; }
    // ставим проём или нишу: ведём пальцем по стене, отпускаем — встаёт
    if (UI.place) { UI.ghost = ghostAt(s2w(p.x, p.y)); Object.assign(gest, { type: 'place' }); if (UI.ghost) say(ghostText(UI.ghost), null, true); draw(); return; }
    const h = R && rotHandle(R.id);
    if (h && Math.hypot(p.x - h.sx, p.y - h.sy) < 26) { const w = s2w(p.x, p.y); Object.assign(gest, { type: 'rrot', rid: R.id, C: h.C, x0: num(R.x0), y0: num(R.y0), a0: num(R.a0), phi0: Math.atan2(w[1] - h.C[1], w[0] - h.C[0]) }); return; }
    // ручки выбранного проёма или ниши: края — ширина, ромб — глубина
    const ih = itemHandles();
    if (ih) {
      // маленький на экране проём: за край берём, только если палец ближе к краю, чем к середине
      const len = Math.hypot(ih.ends[1][0] - ih.ends[0][0], ih.ends[1][1] - ih.ends[0][1]), rad = clamp(len * 0.35, 8, 20);
      const mid = [(ih.ends[0][0] + ih.ends[1][0]) / 2, (ih.ends[0][1] + ih.ends[1][1]) / 2], dm = Math.hypot(p.x - mid[0], p.y - mid[1]);
      for (const k of [0, 1]) { const de = Math.hypot(p.x - ih.ends[k][0], p.y - ih.ends[k][1]); if (de < rad && de < dm) { Object.assign(gest, { type: 'item-end', end: k, it: UI.item }); return; } }
      if (ih.depth) { const dd = Math.hypot(p.x - ih.depth[0], p.y - ih.depth[1]); if (dd < 20 && dd < dm) { Object.assign(gest, { type: 'item-depth', it: UI.item }); return; } }
    }
    // углы выбранной комнаты
    if (RG && RG.g) { let best = 22, ci = -1; RG.g.corners.forEach((q, i) => { const sc = w2s(q[0], q[1]), d = Math.hypot(sc[0] - p.x, sc[1] - p.y); if (d < best) { best = d; ci = i; } }); if (ci >= 0 && !(ih && itemHit(p.x, p.y))) { Object.assign(gest, { type: 'corner', i: ci, rid: R.id, g: RG.g }); return; } }
    // проём или ниша под пальцем — тянем вдоль стены (у выбранной комнаты или уже выбранный)
    const hit = itemHit(p.x, p.y), href = hit && itemRef(hit);
    if (href && (hit.rid === UI.room || (UI.item && UI.item.id === hit.id) || (hit.type === 'door' && href.x.to === UI.room))) {
      const w = s2w(p.x, p.y), t = (w[0] - href.L.P[0]) * href.L.u[0] + (w[1] - href.L.P[1]) * href.L.u[1];
      Object.assign(gest, { type: 'item-move', it: hit, grab: t - num(href.x.pos) }); return;
    }
    // ромб выбранной стены (дуга)
    if (RG && RG.g) {
      const g = RG.g; let best = 22, hit = null;
      g.corners.forEach((q, i) => { const sc = w2s(q[0], q[1]), d = Math.hypot(sc[0] - p.x, sc[1] - p.y); if (d < best) { best = d; hit = { type: 'corner', i }; } });
      if (UI.wall && UI.wall.rid === R.id && UI.wall.i < g.n) { const hh = midHandle(g, UI.wall.i), sc = w2s(hh[0], hh[1]), d = Math.hypot(sc[0] - p.x, sc[1] - p.y); if (d < Math.min(best, 24)) hit = { type: 'bend', i: UI.wall.i }; }
      if (hit) { Object.assign(gest, hit, { rid: R.id, g }); return; }
    }
    // двигается только выбранная комната: иначе по плану из комнат карту не сдвинуть
    const rid = roomAt(s2w(p.x, p.y));
    if (rid && rid === UI.room) {
      const r = room(rid), others = [];
      for (const o of S.rooms) if (o.id !== rid) { const G = MODEL.geo[o.id]; if (G && G.g) others.push(...G.g.corners); }
      Object.assign(gest, { type: 'room', rid, x0: num(r.x0), y0: num(r.y0), mine: MODEL.geo[rid].g.corners.map(q => q.slice()), others });
    }
  }
}
cv.addEventListener('pointerdown', e => { cv.setPointerCapture(e.pointerId); const r = cv.getBoundingClientRect(); ptrs.set(e.pointerId, { x: e.clientX - r.left, y: e.clientY - r.top }); startGesture(); });
cv.addEventListener('pointermove', e => {
  if (!ptrs.has(e.pointerId) || !gest) return;
  const r = cv.getBoundingClientRect(); ptrs.set(e.pointerId, { x: e.clientX - r.left, y: e.clientY - r.top });
  if (gest.type === 'pinch') {
    const pts = [...ptrs.values()]; if (pts.length < 2) return;
    const a = pts[0], b = pts[1], d = Math.hypot(a.x - b.x, a.y - b.y), mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
    view.s = clamp(gest.s0 * d / gest.d0, 0.005, 20); view.cx = gest.w[0] - (mx - CW / 2) / view.s; view.cy = gest.w[1] - (my - CH / 2) / view.s; draw(); return;
  }
  const p = ptrs.get(e.pointerId), dx = p.x - gest.sx, dy = p.y - gest.sy;
  if (!gest.moved && Math.hypot(dx, dy) < 5) return;
  gest.moved = true;
  const wx = dx / view.s, wy = dy / view.s;
  if (gest.type === 'pan') { view.cx = gest.cx - wx; view.cy = gest.cy - wy; draw(); }
  else if (gest.type === 'pattern') {
    const F = gest.F;
    gest.P.offA = Math.round(gest.offA + wx * F.e1[0] + wy * F.e1[1]);
    if (gest.kind !== 'border') gest.P.offB = Math.round(gest.offB + wx * F.e2[0] + wy * F.e2[1]);
    syncPatInputs(); clearVariantMark(); invalidate();
  } else if (gest.type === 'prot' && gest.c) {
    const w = s2w(p.x, p.y), c = gest.c, d = [w[0] - c.C[0], w[1] - c.C[1]];
    const th = snapAngle(Math.atan2(d[0] * c.e2[0] + d[1] * c.e2[1], d[0] * c.e1[0] + d[1] * c.e1[1]) / DEG);
    if (th % 15 === 0 && th !== gest.lastSnap) PF.haptic('select'); gest.lastSnap = th;
    setDirection(gest.P, th, c); syncPatInputs(); syncPatternUI(); clearVariants();
    say('Угол к опорной стене: ' + f1(shownAngle(gest.P)) + '°. У 0°, 45° и 90° стрелка прилипает.', null, true); invalidate();
  } else if (gest.type === 'corner') {
    const w = s2w(p.x, p.y), g = gest.g, pts = g.corners.map(q => q.slice()), n = pts.length, i = gest.i, snap = 10 / view.s;
    let x = Math.round(w[0] / 5) * 5, y = Math.round(w[1] / 5) * 5;
    for (const nb of [pts[(i - 1 + n) % n], pts[(i + 1) % n]]) { if (Math.abs(x - nb[0]) < snap) x = nb[0]; if (Math.abs(y - nb[1]) < snap) y = nb[1]; }
    pts[i] = [x, y]; Object.assign(room(gest.rid), wallsFromCorners(pts, g.arcs)); invalidate();
  } else if (gest.type === 'bend') {
    const w = s2w(p.x, p.y), g = gest.g, i = gest.i, P = g.corners[i], Q = g.corners[(i + 1) % g.n], u = unitV(P, Q), n = g.sgn > 0 ? [u[1], -u[0]] : [-u[1], u[0]];
    let h = (w[0] - (P[0] + Q[0]) / 2) * n[0] + (w[1] - (P[1] + Q[1]) / 2) * n[1]; h = Math.round(h / 10) * 10; if (Math.abs(h) < 40) h = 0;
    h = clamp(h, -dist(P, Q) * 0.49, dist(P, Q));
    const r = room(gest.rid);
    if (i >= r.walls.length) Object.assign(r, wallsFromCorners(g.corners, g.arcs));
    r.walls[i].arc = h; say('Стена ' + (i + 1) + (h ? ': прогиб ' + mm(Math.abs(h)) + ' мм ' + (h > 0 ? 'наружу' : 'внутрь') + ', радиус ≈ ' + mm(arcRadius(dist(P, Q), h)) + ' мм' : ': прямая'), null, true); invalidate();
  } else if (gest.type === 'room') {
    let ddx = wx, ddy = wy; const T = Math.max(0, num(S.set.wallT, 120)), th = 14 / view.s;
    let bx = null, by = null;
    for (const c of gest.mine) for (const o of gest.others) for (const kk of [0, T, -T]) {
      const sx = o[0] + kk - (c[0] + wx), sy = o[1] + kk - (c[1] + wy);
      if (Math.abs(sx) < th && (bx === null || Math.abs(sx) < Math.abs(bx))) bx = sx;
      if (Math.abs(sy) < th && (by === null || Math.abs(sy) < Math.abs(by))) by = sy;
    }
    if (bx !== null) ddx += bx; else ddx = Math.round(ddx / 10) * 10;
    if (by !== null) ddy += by; else ddy = Math.round(ddy / 10) * 10;
    const r = room(gest.rid); r.x0 = Math.round(gest.x0 + ddx); r.y0 = Math.round(gest.y0 + ddy); invalidate();
  } else if (gest.type === 'rrot') {
    const w = s2w(p.x, p.y), phi = Math.atan2(w[1] - gest.C[1], w[0] - gest.C[0]);
    const na = snapAngle(gest.a0 + (phi - gest.phi0) / DEG), delta = na - gest.a0;
    const r = room(gest.rid), q = rot2([gest.x0, gest.y0], gest.C, delta * DEG);
    r.x0 = Math.round(q[0]); r.y0 = Math.round(q[1]); r.a0 = mod(na, 360);
    if (na % 15 === 0 && na !== gest.lastSnap) PF.haptic('select'); gest.lastSnap = na;
    say('Поворот: стена 1 под ' + mm(mod(na, 360)) + '° к горизонтали. У 0°, 45° и 90° комната прилипает.', null, true); invalidate();
  } else if (gest.type === 'place') {
    UI.ghost = ghostAt(s2w(p.x, p.y)); say(UI.ghost ? ghostText(UI.ghost) : 'Ведите пальцем по стене.', null, true); draw();
  } else if (gest.type === 'item-move') {
    const ref = itemRef(gest.it); if (!ref) return; const w = s2w(p.x, p.y), x = ref.x;
    let L = ref.L, i = x.wall | 0, t = (w[0] - L.P[0]) * L.u[0] + (w[1] - L.P[1]) * L.u[1];
    // перенос на другую стену той же комнаты: палец ближе к ней
    const nw = nearestWall(w, ref.r.id, 48), dCur = segDist(w[0], w[1], L.P, L.Q) * view.s;
    if (nw && nw.i !== i && nw.d + 8 < dCur) { x.wall = i = nw.i; L = nw.L; t = nw.t; gest.grab = Math.min(num(x.width), L.c) / 2; if (UI.wallFocus >= 0) UI.wallFocus = i; }
    if (num(x.width) > L.c) x.width = Math.floor(L.c);
    x.pos = Math.round(snapPos(ref.r.id, i, L, t - gest.grab, num(x.width))); if (ref.type === 'door') delete x.full;
    const r2 = itemRef(gest.it); if (r2) say(itemText(r2), null, true); invalidate();
  } else if (gest.type === 'item-end') {
    const ref = itemRef(gest.it); if (!ref) return; const w = s2w(p.x, p.y), x = ref.x, L = ref.L, i = x.wall | 0, minW = ref.type === 'door' ? DOOR_MIN : NICHE_MIN;
    const t = snapEdge(ref.r.id, i, L, (w[0] - L.P[0]) * L.u[0] + (w[1] - L.P[1]) * L.u[1]), t0 = num(x.pos), t1 = t0 + num(x.width);
    if (gest.end === 0) { x.pos = Math.round(clamp(t, 0, t1 - minW)); x.width = Math.round(t1 - x.pos); } else x.width = Math.round(clamp(t, t0 + minW, L.c) - t0);
    if (ref.type === 'door') delete x.full; say(itemText(ref), null, true); invalidate();
  } else if (gest.type === 'item-depth') {
    const ref = itemRef(gest.it); if (!ref) return; const w = s2w(p.x, p.y), L = ref.L, e = (w[0] - L.P[0]) * L.no[0] + (w[1] - L.P[1]) * L.no[1];
    ref.x.depth = clamp(Math.round((ref.x.kind === 'box' ? -e : e) / 10) * 10, 20, 3000); say(itemText(ref), null, true); invalidate();
  } else if (gest.type === 'add') {
    const w1 = snapPoint(s2w(p.x, p.y), null); UI.addPrev = [gest.w0, w1];
    say(UI.addTpl === 'rect' ? 'Комната ' + mm(Math.abs(w1[0] - gest.w0[0])) + ' × ' + mm(Math.abs(w1[1] - gest.w0[1])) + ' мм' : 'Отпустите, где поставить комнату.', null, true); draw();
  }
});
function placeRoomAt(tplId, w) {
  const t = TEMPLATES.find(x => x.id === tplId) || TEMPLATES[0];
  const walls = tplId === 'rect' ? rectWalls(4200, 3600) : t.make(), g = roomGeom({ x0: 0, y0: 0, a0: 0, walls }), b = bboxOf(g.poly);
  const r = newRoom(tplId === 'rect' ? 'Комната ' + (S.rooms.length + 1) : t.name, walls, Math.round(w[0] - (b.u0 + b.u1) / 2), Math.round(w[1] - (b.v0 + b.v1) / 2));
  finishAdd(r);
}
function finishAdd(r) {
  PF.haptic('medium');
  S.rooms.push(r); UI.room = r.id; UI.addTpl = null; UI.addPrev = null; UI.wall = null;
  const msg = syncAutoDoors([r.id]); recomputeNow(); selectNewDoor();
  afterRooms(msg || 'Комната «' + r.name + '» добавлена. Тяните её пальцем к соседней — прилипнет, и появится проём. Круглая ручка сверху — поворот.');
  renderCtxbar();
}
function endPointer(e) {
  if (!ptrs.has(e.pointerId)) return;
  const g = gest, last = ptrs.get(e.pointerId), wasTap = g && !g.moved && g.type !== 'pinch' && ptrs.size === 1;
  ptrs.delete(e.pointerId);
  if (g && g.type === 'add' && ptrs.size === 0) {
    UI.addPrev = null;
    if (!g.moved) placeRoomAt(UI.addTpl, g.w0);
    else {
      const w1 = snapPoint(s2w(last.x, last.y), null);
      if (UI.addTpl !== 'rect') placeRoomAt(UI.addTpl, w1);
      else {
        const W = Math.abs(w1[0] - g.w0[0]), H = Math.abs(w1[1] - g.w0[1]);
        if (W < 500 || H < 500) { say('Слишком маленькая комната: тяните дальше (не меньше 500 × 500 мм) или просто нажмите на карту.', 'bad'); draw(); }
        else finishAdd(newRoom('Комната ' + (S.rooms.length + 1), rectWalls(W, H), Math.min(g.w0[0], w1[0]), Math.min(g.w0[1], w1[1])));
      }
    }
    gest = null; return;
  }
  if (g && g.type === 'place' && ptrs.size === 0) { placeGhost(); gest = null; return; }
  if (wasTap && g.type !== 'prot' && g.type !== 'rrot') selectAt(g.sx, g.sy);
  if (ptrs.size) startGesture(); else gest = null;
  if (g && g.moved && ['corner', 'bend', 'room', 'rrot'].includes(g.type)) {
    const msg = g.type === 'bend' ? '' : syncAutoDoors([g.rid]);
    recomputeNow(); if (g.type === 'room') selectNewDoor(); renderPlanTab(); renderCtxbar(); invalidate({ fast: true });
    if (msg) { say(msg, 'ok'); PF.haptic('ok'); }
  }
  if (g && g.moved && (g.type === 'pattern' || g.type === 'prot')) { renderCtxbar(); invalidate({ fast: true }); }
  if (g && g.moved && ['item-move', 'item-end', 'item-depth'].includes(g.type)) {
    const ref = itemRef(g.it); if (ref && ref.type === 'door') doorLink(ref.r, ref.x);
    UI.item = g.it; UI.room = g.it.rid; recomputeNow(); renderPlanTab(); renderCtxbar(); invalidate({ fast: true });
    const r2 = itemRef(g.it); if (r2) say(itemText(r2) + (r2.type === 'door' ? (r2.x.to ? ' — проём в «' + roomName(r2.x.to) + '».' : ' — проём наружу (соседней комнаты за стеной нет).') : '.'), 'ok');
  }
}
/* «призрак» при установке: ближайшая стена под пальцем, по центру пальца */
function ghostAt(w) {
  const nw = nearestWall(w, null, 56); if (!nw) return null;
  const kind = UI.place, door = kind === 'door', pr = door ? { width: 900, depth: 0, kind: 'door' } : (NICHE_PRESET[kind] || NICHE_PRESET.radiator);
  let width = Math.min(pr.width, Math.max(door ? DOOR_MIN : NICHE_MIN, Math.floor(nw.L.c - 100))), pos = nw.t - width / 2;
  if (door) { const a = (MODEL.adj || []).find(x => x.a === nw.rid && x.i === nw.i && nw.t >= x.o0 && nw.t <= x.o1); if (a) { width = Math.min(width, Math.floor(a.o1 - a.o0)); pos = clamp(pos, a.o0, a.o1 - width); } }
  pos = snapPos(nw.rid, nw.i, nw.L, pos, width);
  return { rid: nw.rid, i: nw.i, pos, width, depth: pr.depth, type: door ? 'door' : 'niche', kind: pr.kind, L: nw.L };
}
function ghostText(gh) { const name = gh.type === 'door' ? 'Проём ' + mm(gh.width) : (gh.kind === 'box' ? 'Выступ ' : 'Ниша ') + mm(gh.width) + '×' + mm(gh.depth); return name + ' мм, «' + roomName(gh.rid) + '», стена ' + (gh.i + 1) + ': от угла ' + mm(gh.pos) + ', до угла ' + mm(Math.max(0, gh.L.c - gh.pos - gh.width)) + ' мм. Отпустите — встанет здесь.'; }
function placeGhost() {
  const gh = UI.ghost; UI.ghost = null;
  if (!gh) { say('Ведите пальцем по стене — ' + (UI.place === 'door' ? 'проём' : 'ниша') + ' встанет там, где отпустите.', 'bad'); draw(); return; }
  const r = room(gh.rid); let it;
  if (gh.type === 'door') { const d = { id: newId('d'), wall: gh.i, pos: Math.round(gh.pos), width: Math.round(gh.width) }; r.doors = r.doors || []; r.doors.push(d); doorLink(r, d); it = { type: 'door', rid: r.id, id: d.id }; }
  else { const pr = NICHE_PRESET[UI.place] || NICHE_PRESET.radiator, x = { id: newId('n'), kind: pr.kind, wall: gh.i, pos: Math.round(gh.pos), width: Math.round(gh.width), depth: pr.depth, floor: true, name: pr.name }; r.niches = r.niches || []; r.niches.push(x); it = { type: 'niche', rid: r.id, id: x.id }; }
  UI.place = null; recomputeNow(); selectItem(it, true); invalidate({ fast: true }); PF.haptic('ok');
  const ref = itemRef(it); say((ref ? itemText(ref) : 'Готово') + '. Тяните по стене, кружки на краях — ширина' + (gh.type === 'niche' ? ', ромб — глубина' : '') + '.', 'ok');
}
cv.addEventListener('pointerup', endPointer);
cv.addEventListener('pointercancel', endPointer);
cv.addEventListener('wheel', e => {
  e.preventDefault(); const r = cv.getBoundingClientRect(), mx = e.clientX - r.left, my = e.clientY - r.top, w = s2w(mx, my);
  view.s = clamp(view.s * Math.exp(-e.deltaY * (e.ctrlKey ? 0.01 : 0.0015)), 0.005, 20);
  view.cx = w[0] - (mx - CW / 2) / view.s; view.cy = w[1] - (my - CH / 2) / view.s; draw();
}, { passive: false });
function selectAt(x, y) {
  if (!MODEL) return; const w = s2w(x, y);
  if (UI.mode === 'rooms') {
    const ih = itemHit(x, y); if (ih) { selectItem(ih); return; }
    const hadItem = !!UI.item; UI.item = null;
    const wh = wallHit(x, y); if (wh) { selectWall(wh); return; }
    const rid = roomAt(w), had = !!UI.wall || hadItem; UI.wall = null; UI.delArm = null;
    if (hadItem) renderRoomEditor();
    if (rid && rid !== UI.room) { UI.room = rid; renderPlanTab(); saveUI(); say('Выбрана «' + roomName(rid) + '». Тяните её пальцем, круглая ручка — поворот, кружки — углы.'); }
    else if (had) modeHint();
    renderCtxbar(); draw(); return;
  }
  if (UI.mode === 'pattern') {
    const res = MODEL.byKey[UI.target], u = res && !res.err ? res.unit : null;
    const hit = u && (u.kind === 'floor' || u.kind === 'room') ? wallAt(x, y, u.roomIds) : null;
    if (hit) {
      const P = curP(); P.refWall = hit.i; if (u.kind === 'floor') P.refRoom = hit.rid; P.dir = 'along';
      clearVariants(); recomputeNow(); centerTarget(UI.target, true); syncPatInputs(); syncPatternUI(); renderRefSelects(); renderCtxbar(); invalidate({ fast: true });
      say('Рисунок пошёл вдоль стены ' + (hit.i + 1) + (S.rooms.length > 1 ? ' (' + roomName(hit.rid) + ')' : '') + '. «Поперёк» и стрелка меняют угол.', 'ok');
      return;
    }
  }
  const rid = roomAt(w);
  if (rid && rid !== UI.room) { UI.room = rid; renderPlanTab(); renderCtxbar(); if (UI.tab === 'pat') renderPatTab(); }
  let found = null;
  for (let ui = MODEL.units.length - 1; ui >= 0 && !found; ui--) {
    const res = MODEL.units[ui]; if (res.err) continue;
    for (const p of res.pieces) { for (const part of p.w) { const b = bboxOf(part); if (w[0] < b.u0 || w[0] > b.u1 || w[1] < b.v0 || w[1] > b.v1) continue; if (inPoly(w[0], w[1], part)) { found = { key: res.unit.key, id: p.id }; break; } } if (found) break; }
  }
  if (UI.mode === 'pattern' && found && found.key !== UI.target) {
    UI.target = found.key; UI.variants = null; syncPatInputs(); syncPatternUI(); renderCtxbar(); renderStatus(); if (UI.tab === 'pat') renderPatTab();
    say('Двигаю: ' + unitName(found.key).toLowerCase() + '.', 'ok'); draw(); return;
  }
  UI.sel = found && !(UI.sel && UI.sel.key === found.key && UI.sel.id === found.id) ? found : null;
  renderPieceInfo(); draw();
}
/* полоса действий у карты: зависит от шага и от того, что выбрано */
const BTN = (act, label, attrs, cls) => '<button class="btn small' + (cls ? ' ' + cls : '') + '" type="button" data-act="' + act + '"' + (attrs || '') + '>' + label + '</button>';
function wallOk() { const w = UI.wall; if (!w || !MODEL) return null; const r = room(w.rid), G = r && MODEL.geo[r.id]; if (!G || !G.g || w.i >= G.g.n) return null; return { r, G, g: G.g, i: w.i, t: w.t || 0 }; }
function renderCtxbar() {
  const el = $('#ctxbar'); if (!el) return; let h = '';
  if (UI.mode === 'rooms') {
    const W = wallOk(), IR = itemRef();
    const PLACE_KINDS = [['door', 'Проём'], ['radiator', 'Ниша под батарею'], ['wardrobe', 'Ниша под шкаф'], ['box', 'Выступ, короб']];
    if (UI.place) {
      h = '<span class="ctx-t"><b>Ведите пальцем по стене</b> — отпустите, где нужно</span>' +
        PLACE_KINDS.map(([k, t]) => '<button class="chip" type="button" data-act="place-kind" data-v="' + k + '" aria-pressed="' + (UI.place === k) + '">' + t + '</button>').join('') + BTN('place-cancel', 'Отмена');
    } else if (IR) {
      const x = IR.x, door = IR.type === 'door', box = x.kind === 'box', shared = door && (MODEL.adj || []).some(a => a.a === IR.r.id && a.i === (x.wall | 0));
      const cin = (label, f, v) => '<label class="inp ctxin"><span>' + label + '</span><input data-itf="' + f + '" inputmode="decimal" value="' + mm(v) + '" aria-label="' + label + '"><i>мм</i></label>';
      h = BTN('item-back', ICON.back, ' aria-label="Готово" title="Готово"', 'ghost') +
        (door ? '<span class="ctx-t"><b>' + (x.full ? 'Проход' : 'Проём') + '</b></span>' : '<div class="seg mini" role="group" aria-label="Ниша или выступ"><button type="button" data-act="item-kind" data-v="niche" aria-pressed="' + !box + '">Ниша</button><button type="button" data-act="item-kind" data-v="box" aria-pressed="' + box + '">Выступ</button></div>') +
        cin('шир.', 'width', x.width) + (door ? '' : cin(box ? 'выступ' : 'глуб.', 'depth', x.depth)) + cin('от угла', 'pos', x.pos) +
        (shared ? '<button class="chip" type="button" data-act="item-full" aria-pressed="' + !!x.full + '">Во всю стену</button>' : '') +
        (!door && !box ? '<button class="chip" type="button" data-act="item-floor" aria-pressed="' + (x.floor === false) + '">Без пола</button>' : '') +
        BTN('item-del', 'Удалить', '', 'danger');
    } else if (UI.addTpl) {
      h = '<span class="ctx-t"><b>Нажмите на карту</b>' + (UI.addTpl === 'rect' ? ' или нарисуйте пальцем' : '') + '</span>' +
        TEMPLATES.map(t => '<button class="chip" type="button" data-act="add-tpl" data-tpl="' + t.id + '" aria-pressed="' + (UI.addTpl === t.id) + '">' + esc(t.name) + '</button>').join('') +
        BTN('add-cancel', 'Отмена');
    } else if (W) {
      const c = dist(W.g.corners[W.i], W.g.corners[(W.i + 1) % W.g.n]), isArc = Math.abs(W.g.arcs[W.i]) >= 0.5;
      h = BTN('wall-back', ICON.back, ' aria-label="Назад к комнате" title="Назад к комнате"', 'ghost') + '<span class="ctx-t">Стена <b>' + (W.i + 1) + '</b> · ' + mm(c) + '</span>' +
        (isArc ? '' : BTN('wall-door', ICON.plus + 'Проём') + BTN('wall-niche', ICON.plus + 'Ниша') + BTN('wall-box', ICON.plus + 'Выступ')) +
        BTN('wall-arc', isArc ? 'Сделать прямой' : '⌒ Дуга') + (isArc ? '' : BTN('wall-cut', 'Угол здесь', ' title="Разделить стену в месте касания"'));
    } else {
      const r = curRoom();
      h = BTN('add-start', ICON.plus + 'Комната', '', 'primary') + BTN('place-start', ICON.plus + 'Проём', ' data-v="door" title="Поставить проём: ведите пальцем по стене"') + BTN('place-start', ICON.plus + 'Ниша', ' data-v="radiator" title="Поставить нишу или выступ: ведите пальцем по стене"') + (r ? '<span class="ctx-sep"></span>' + BTN('room-rotr', ICON.rot + '90°', ' title="Повернуть «' + esc(r.name) + '» на 90°"') + BTN('room-dup', ICON.copy + 'Копия', ' title="Копия «' + esc(r.name) + '»"') +
        (S.rooms.length > 1 ? BTN('room-del', UI.delArm === 'room:' + r.id ? 'Точно удалить?' : 'Удалить', '', 'danger') : '') : '');
    }
  } else if (UI.mode === 'pattern') {
    const kind = targetKind(UI.target), P = curP();
    if (kind === 'border') h = '<span class="ctx-t">Рамка идёт вдоль стен. Стрелки ◀ ▶ под картой сдвигают стыки.</span>' + BTN('optimize', ICON.star + 'Подобрать', '', 'primary');
    else {
      const g = patDef(P.type).group, axis = g === 'herring' || g === 'chevron';
      h = BTN('optimize', ICON.star + 'Подобрать', '', 'primary') +
        '<div class="seg mini" role="group" aria-label="Направление"><button type="button" data-act="dir" data-v="along" aria-pressed="' + (P.dir === 'along') + '">' + (axis ? 'Ось вдоль' : 'Вдоль') + '</button><button type="button" data-act="dir" data-v="across" aria-pressed="' + (P.dir === 'across') + '">Поперёк</button><button type="button" data-act="dir" data-v="diag" aria-pressed="' + (P.dir === 'diag') + '">45°</button></div>' +
        BTN('rot-step', '↺ 15°', ' data-v="-15" title="Повернуть рисунок на 15° против часовой"') + BTN('rot-step', '↻ 15°', ' data-v="15" title="Повернуть рисунок на 15° по часовой"') +
        '<label class="inp ang" title="Угол к опорной стене"><input id="ctxAngle" inputmode="decimal" value="' + f1(shownAngle(P)) + '" aria-label="Угол рисунка к опорной стене"><i>°</i></label>' +
        BTN('flipU', '⇄ Развернуть', ' title="Развернуть рисунок в обратную сторону"');
    }
  } else if (UI.tab === 'res') {
    h = BTN('export-img', ICON.img + 'Фото проекта', '', 'primary') + BTN('export-share', ICON.share + 'Отправить текстом') + BTN('export-copy', 'Скопировать');
  } else {
    const M = S.mat, c = catById(M.cat);
    h = '<span class="ctx-t">Покрытие: <b>' + esc(c.name.toLowerCase()) + ' ' + mm(num(M.L)) + '×' + mm(num(M.W)) + '</b> · ' + esc(patDef(S.floorPat.type).name.toLowerCase()) + '</span>';
  }
  el.innerHTML = h; el.hidden = !h; el.scrollLeft = 0; fadeMore(el); syncTgBack();
}
/* полоса прокручивается вбок: справа мягкое затухание, пока есть что листать */
function fadeMore(el) { if (!el) return; requestAnimationFrame(() => { el.classList.toggle('more', el.scrollWidth - el.clientWidth - el.scrollLeft > 4); }); }
document.addEventListener('scroll', e => { const t = e.target; if (t && t.classList && (t.classList.contains('ctxbar') || t.classList.contains('pills'))) fadeMore(t); }, true);
window.addEventListener('resize', () => { fadeMore($('#ctxbar')); fadeMore($('#status')); });

/* ================= панель: вкладки и поля ================= */
function setTab(t) {
  if (!MODE_OF[t]) t = 'plan';
  const changed = UI.tab !== t; UI.tab = t; UI.mode = MODE_OF[t];
  if (changed) { UI.addTpl = null; UI.addPrev = null; UI.wall = null; UI.item = null; UI.place = null; UI.ghost = null; UI.delArm = null; if (t === 'plan') { UI.sel = null; UI.hl = null; renderPieceInfo(); } }
  $$('.tab').forEach(b => b.setAttribute('aria-selected', String(b.dataset.tab === t)));
  $$('.tabbody').forEach(b => { b.hidden = b.dataset.body !== t; });
  if (t === 'plan') renderPlanTab(); if (t === 'mat') renderMatTab(); if (t === 'pat') renderPatTab(); if (t === 'res') renderResults();
  if (changed) { $('#panel').scrollTop = 0; syncToolbar(); renderStatus(); modeHint(); draw(); }
  saveUI(); syncTgBack();
}
/* раскрывающиеся разделы: открытые запоминаем */
const ACC_DEF = { shape: true, walls: false, doors: false, niches: false, own: false, pos: false, kv: false, floor: false, plank: true, mount: false, dir: false, offs: false, comp: false, rules: false };
const accOpen = k => k in UI.open ? !!UI.open[k] : !!ACC_DEF[k];
const acc = (k, title, sum, body, sid) => '<details class="acc" data-acc="' + k + '"' + (accOpen(k) ? ' open' : '') + '><summary><b>' + title + '</b><small' + (sid ? ' id="' + sid + '"' : '') + '>' + sum + '</small></summary><div class="accb">' + body + '</div></details>';
function applyAcc() { $$('details.acc[data-acc]').forEach(d => { const o = accOpen(d.dataset.acc); if (d.open !== o) d.open = o; }); }
document.addEventListener('toggle', e => { const d = e.target; if (d && d.matches && d.matches('details.acc[data-acc]')) { if (UI.open[d.dataset.acc] !== d.open) { UI.open[d.dataset.acc] = d.open; saveUI(); } } }, true);
$$('.tab').forEach(b => b.addEventListener('click', () => setTab(b.dataset.tab)));
function getK(path) { return path.split('.').reduce((o, k) => o == null ? o : o[k], S); }
function setK(path, val) { const ks = path.split('.'); let o = S; for (let i = 0; i < ks.length - 1; i++) o = o[ks[i]]; o[ks[ks.length - 1]] = val; }
const fmtIn = v => v === undefined || v === null ? '' : typeof v === 'number' ? String(Math.round(v * 100) / 100).replace('.', ',') : v;
function setIn(el, v) { if (el === document.activeElement) return; if (el.type === 'checkbox') el.checked = !!v; else el.value = fmtIn(v); }
function syncInputs() {
  $$('[data-k]').forEach(el => setIn(el, getK(el.dataset.k)));
  const m = curMat(false); $$('[data-mk]').forEach(el => setIn(el, m[el.dataset.mk]));
  syncPatInputs();
  setIn($('#projName'), S.name || '');
}
function syncPatInputs() { const P = curP(); $$('[data-pk]').forEach(el => setIn(el, P[el.dataset.pk])); const ca = $('#ctxAngle'); if (ca) setIn(ca, Math.round(shownAngle(P) * 10) / 10); renderSums(); }
function readIn(t) { if (t.type === 'checkbox') return t.checked; if ('num' in t.dataset) { if (String(t.value).trim() === '') return undefined; const v = num(t.value, NaN); return Number.isFinite(v) ? v : undefined; } return t.value; }
document.addEventListener('input', e => {
  const t = e.target; if (!(t instanceof HTMLElement) || !t.closest('.app')) return;
  if (t.id === 'projName') { S.name = t.value; invalidate(); return; }
  if (t.id === 'matUseMain') return;
  if (t.id === 'ctxAngle') { const v = num(t.value, NaN), c = dirCtx(UI.target); if (!Number.isFinite(v) || !c) return; setDirection(curP(), v + (shownAngle(curP()) !== fullAngle(curP()) && fullAngle(curP()) >= 180 ? 180 : 0), c); clearVariants(); syncPatternUI(); invalidate(); return; }
  if (t.dataset.k) { const v = readIn(t); if (v === undefined) return; setK(t.dataset.k, v); invalidate(); return; }
  if (t.dataset.mk) { const v = readIn(t); if (v === undefined) return; const m = curMat(true); m[t.dataset.mk] = v; m.item = null; const tk = UI.matTarget === 'main' ? 'floor' : UI.matTarget; if (t.dataset.mk === 'shape' && v === 'chevron' && targetKind(tk) !== 'border') setPatternType(patOf(tk), 'chevron'); renderSizes(); invalidate(); return; }
  if (t.dataset.pk) { const v = readIn(t); if (v === undefined) return; const P = curP(); P[t.dataset.pk] = v; clearVariantMark(); if (['refRoom', 'refWall'].includes(t.dataset.pk)) { renderRefSelects(); recomputeNow(); centerTarget(UI.target, true); } if (t.dataset.pk === 'chevAngle') renderPatList(); invalidate(); return; }
  if (t.dataset.rk) { const r = curRoom(); const v = t.dataset.rk === 'name' ? t.value : readIn(t); if (v === undefined) return; r[t.dataset.rk] = v; invalidate(); return; }
  if (t.dataset.w !== undefined) { onWallInput(t); return; }
  if (t.dataset.itf) {
    const ref = itemRef(); if (!ref) return; const v = num(t.value, NaN); if (!Number.isFinite(v)) return; const x = ref.x, f = t.dataset.itf;
    if (f === 'width') x.width = clamp(v, ref.type === 'door' ? DOOR_MIN : NICHE_MIN, ref.L.c); else if (f === 'pos') x.pos = clamp(v, 0, Math.max(0, ref.L.c - num(x.width))); else if (f === 'depth') x.depth = clamp(v, 20, 3000);
    if (ref.type === 'door') delete x.full; invalidate(); return;
  }
  if (t.dataset.rect) { const r = curRoom(), v = num(t.value, NaN); if (!(v >= 300) || !isRect(r)) return; (t.dataset.rect === 'L' ? [0, 2] : [1, 3]).forEach(i => { r.walls[i].len = v; }); invalidate(); return; }
  if (t.dataset.n !== undefined) { const x = (curRoom().niches || [])[+t.dataset.n]; if (!x) return; const f = t.dataset.nf, v = readIn(t); if (v === undefined) return; x[f] = f === 'wall' ? (v | 0) : v; if (f === 'floor' || f === 'wall') renderRoomEditor(); invalidate(); return; }
  if (t.dataset.d !== undefined) { const d = curRoom().doors[+t.dataset.d]; if (!d) return; const v = readIn(t); if (v === undefined) return; d[t.dataset.df] = t.dataset.df === 'wall' ? (v | 0) : v; delete d.full; invalidate(); return; }
  if (t.dataset.ins !== undefined) { const ins = curRoom().inserts[+t.dataset.ins]; if (!ins) return; const v = readIn(t); if (v === undefined) return; ins[t.dataset.f] = v; invalidate(); return; }
  if (t.dataset.bf) { const B = curRoom().border, v = readIn(t); if (v === undefined) return; B[t.dataset.bf] = v; invalidate(); return; }
});
function recomputeNow() { MODEL = computeAll(); fixTargets(); }
/* после правки размеров комнаты: проёмы к соседям появляются и подстраиваются.
   Панель перерисовываем только когда палец ушёл из неё — иначе пропадёт поле, в которое как раз переходят */
let editorDirty = false, ptrDown = 0; const afterTap = [];
/* пока палец на экране, кнопки не пересоздаём: иначе нажатие на них потеряется */
function whenFree(fn) { if (ptrDown) afterTap.push(fn); else fn(); }
document.addEventListener('pointerdown', () => { ptrDown++; }, true);
const ptrUp = () => { ptrDown = Math.max(0, ptrDown - 1); if (!ptrDown && afterTap.length) setTimeout(() => { const list = afterTap.splice(0); list.forEach(f => f()); }, 0); };
document.addEventListener('pointerup', ptrUp, true); document.addEventListener('pointercancel', ptrUp, true);
function editorLater() { setTimeout(() => whenFree(() => { const ed = $('#roomEditor'); if (ed && ed.contains(document.activeElement)) editorDirty = true; else { editorDirty = false; renderRoomEditor(); applyAcc(); } }), 0); }
document.addEventListener('change', e => {
  const t = e.target; if (!(t instanceof HTMLElement) || !t.closest('#roomEditor')) return;
  if (t.dataset.w !== undefined || t.dataset.rect || ['x0', 'y0', 'a0'].includes(t.dataset.rk)) { const msg = syncAutoDoors([curRoom().id]); recomputeNow(); renderRoomList(); renderRoomSums(); invalidate({ fast: true }); if (msg) { say(msg, 'ok'); whenFree(renderCtxbar); editorLater(); } }
});
document.addEventListener('change', e => {
  const t = e.target; if (!(t instanceof HTMLElement) || !t.dataset.itf) return;
  const ref = itemRef(); if (ref && ref.type === 'door') doorLink(ref.r, ref.x);
  recomputeNow(); invalidate({ fast: true }); whenFree(() => { renderRoomEditor(); applyAcc(); }); const r2 = itemRef(); if (r2) say(itemText(r2), 'ok');
});
document.addEventListener('focusout', e => { if (editorDirty && e.target.closest && e.target.closest('#roomEditor')) editorLater(); });

/* ================= 1. Комнаты: план, стены, проёмы, ниши ================= */
function roomSize(g) { const b = bboxOf(g.poly); return mm(b.u1 - b.u0) + '×' + mm(b.v1 - b.v0); }
function renderRoomList() {
  const el = $('#roomList'); if (!el) return;
  let total = 0;
  const info = S.rooms.map(r => { const G = MODEL && MODEL.geo[r.id], ok = G && G.g && !G.err, a = ok ? Math.abs(area(G.g.poly)) : 0; total += a; return { r, ok, txt: ok ? fm2(a) + ' м²' + (r.own ? ' · свой' : '') : 'ошибка' }; });
  // те же комнаты — меняем только текст: кнопки не пересоздаём, чтобы не терялись нажатия
  const cards = $$('.rcard[data-room]', el);
  if (cards.length === info.length && cards.every((c, i) => c.dataset.room === info[i].r.id)) {
    cards.forEach((c, i) => { const x = info[i]; c.setAttribute('aria-pressed', String(x.r.id === UI.room)); c.querySelector('b').textContent = x.r.name; const sm = c.querySelector('small'); sm.textContent = x.txt; sm.className = x.ok ? '' : 'err'; });
    const add = $('.rcard.add', el); if (add) add.setAttribute('aria-expanded', String(!!UI.addRoom));
  } else el.innerHTML = info.map(x => '<button class="rcard" type="button" data-act="room-select" data-room="' + x.r.id + '" aria-pressed="' + (x.r.id === UI.room) + '"><b>' + esc(x.r.name) + '</b><small' + (x.ok ? '' : ' class="err"') + '>' + x.txt + '</small></button>').join('') +
    '<button class="rcard add" type="button" data-act="room-add-open" aria-expanded="' + !!UI.addRoom + '">' + ICON.plus + '<span>Комната</span></button>';
  $('#floorSum').textContent = S.rooms.length + ' ' + plural(S.rooms.length, 'комната', 'комнаты', 'комнат') + ' · ' + fm2(total) + ' м²';
  const wt = $('#wallTSum'); if (wt) wt.textContent = mm(num(S.set.wallT, 120)) + ' мм';
}
function renderTplChips() { $('#tplNew').innerHTML = TEMPLATES.filter(t => t.id !== 'rect').map(t => '<button class="chip" type="button" data-act="room-add-tpl" data-tpl="' + t.id + '">' + esc(t.name) + '</button>').join(''); }
function renderPlanTab() { renderRoomList(); renderRoomEditor(); $('#addRoomBox').hidden = !UI.addRoom; applyAcc(); }
const innerOf = turn => 180 - turn;
const isRect = r => r.walls.length === 4 && r.walls.every((w, i) => Math.abs(num(w.arc)) < 0.5 && (i === 0 || Math.abs(num(w.turn) - 90) < 0.01)) && Math.abs(num(r.walls[0].len) - num(r.walls[2].len)) < 0.5 && Math.abs(num(r.walls[1].len) - num(r.walls[3].len)) < 0.5;
function wallCard(r, i, g, joints) {
  const w = r.walls[i], arc = num(w.arc), isArc = Math.abs(arc) >= 0.5, c = num(w.len);
  const js = isArc ? [] : joints.filter(a => a.i === i);
  const items = [];
  (r.doors || []).forEach(d => { if ((d.wall | 0) === i) items.push((d.full ? 'проход ' : 'проём ') + mm(d.width) + ' (от угла ' + mm(d.pos) + ')'); });
  (r.niches || []).forEach(x => { if ((x.wall | 0) === i) items.push((x.kind === 'box' ? 'выступ ' : 'ниша ') + mm(x.width) + '×' + mm(x.depth) + (x.kind !== 'box' && x.floor === false ? ', без пола' : '')); });
  return '<div class="wcard' + (i === UI.wallFocus ? ' sel' : '') + '" data-wi="' + i + '">' +
    '<div class="whead"><span class="wn">' + (i + 1) + '</span><b>Стена ' + (i + 1) + '</b>' +
    '<div class="seg mini" role="group" aria-label="Форма стены ' + (i + 1) + '"><button type="button" data-act="wall-shape" data-w="' + i + '" data-v="straight" aria-pressed="' + !isArc + '">Прямая</button><button type="button" data-act="wall-shape" data-w="' + i + '" data-v="arc" aria-pressed="' + isArc + '">Дуга</button></div>' +
    '<button class="icon" type="button" data-act="wall-split" data-w="' + i + '" title="Разделить стену пополам (добавить угол)" aria-label="Разделить стену ' + (i + 1) + '"' + (isArc ? ' disabled' : '') + '>' + ICON.split + '</button>' +
    '<button class="icon" type="button" data-act="wall-del" data-w="' + i + '" title="Удалить стену" aria-label="Удалить стену ' + (i + 1) + '"' + (r.walls.length <= 2 ? ' disabled' : '') + '>' + ICON.del + '</button></div>' +
    '<div class="wrow"><label class="fld"><span>' + (isArc ? 'Длина по хорде' : 'Длина') + '</span><span class="inp"><input id="w' + i + 'len" data-w="' + i + '" data-wf="len" inputmode="decimal" value="' + mm(c) + '"><i>мм</i></span></label>' +
    (isArc ? '<label class="fld"><span>Прогиб дуги</span><span class="inp"><input id="w' + i + 'arc" data-w="' + i + '" data-wf="arc" inputmode="decimal" value="' + mm(Math.abs(arc)) + '"><i>мм</i></span></label>' +
      '<label class="fld"><span>или радиус</span><span class="inp"><input id="w' + i + 'rad" data-w="' + i + '" data-wf="rad" inputmode="decimal" value="' + mm(arcRadius(c, arc)) + '"><i>мм</i></span></label>' : '') + '</div>' +
    (isArc ? '<div class="wrow"><div class="seg mini" role="group" aria-label="Куда выгнута стена"><button type="button" data-act="wall-side" data-w="' + i + '" data-v="out" aria-pressed="' + (arc > 0) + '">Наружу</button><button type="button" data-act="wall-side" data-w="' + i + '" data-v="in" aria-pressed="' + (arc < 0) + '">Внутрь</button></div><span class="hint" id="w' + i + 'hint">длина по дуге ≈ ' + mm(arcLength(c, arc)) + ' мм</span></div>' : '') +
    (js.length ? '<div class="wjoin">По стыкам: ' + jointSegs(dist(g.corners[i], g.corners[(i + 1) % g.n]), js).map(sg => '<span' + (sg.to ? ' class="sh"' : '') + '>' + mm(sg.len) + '</span>' + (sg.to ? ' общая с «' + esc(roomName(sg.to)) + '»' : '')).join(' ') + '</div>' : '') +
    (items.length ? '<div class="wjoin">' + esc(items.join(' · ')) + '</div>' : '') +
    '</div>';
}
function cornerRow(r, i) {
  const ang = innerOf(num(r.walls[i].turn)), v = Math.round(ang * 10) / 10;
  const chips = [[90, 'обычный'], [270, 'выступ'], [135, ''], [180, 'прямо']].map(([a, t]) => '<button class="chip" type="button" data-act="corner-set" data-w="' + i + '" data-v="' + a + '" aria-pressed="' + (Math.abs(v - a) < 0.05) + '" title="' + (t || a + '°') + '">' + a + '°' + (t ? ' ' + t : '') + '</button>').join('');
  return '<div class="corner">Угол между стенами ' + i + ' и ' + (i + 1) + ': ' + chips + '<span class="inp"><input id="c' + i + 'ang" data-w="' + i + '" data-wf="ang" inputmode="decimal" value="' + f1(v) + '" aria-label="Угол между стенами ' + i + ' и ' + (i + 1) + '"><i>°</i></span></div>';
}
const fldIn = (label, attrs, val, unit) => '<label class="fld"><span>' + label + '</span><span class="inp"><input ' + attrs + ' inputmode="decimal" value="' + val + '">' + (unit ? '<i>' + unit + '</i>' : '') + '</span></label>';
function wallSelect(attrs, cur, g, onlyStraight) {
  let o = ''; for (let i = 0; i < g.n; i++) { if (onlyStraight && Math.abs(g.arcs[i]) >= 0.5) continue; o += '<option value="' + i + '"' + (i === cur ? ' selected' : '') + '>' + (i + 1) + ' · ' + mm(dist(g.corners[i], g.corners[(i + 1) % g.n])) + '</option>'; }
  return '<label class="fld"><span>Стена</span><span class="inp"><select ' + attrs + ' data-num>' + o + '</select></span></label>';
}
function roomSums(r, G, g) {
  return {
    shape: roomSize(g) + ' мм',
    walls: g.n + ' ' + plural(g.n, 'стена', 'стены', 'стен') + (g.arcs.some(a => Math.abs(a) >= 0.5) ? ', есть дуга' : ''),
    doors: (r.doors || []).length ? (r.doors.length + ' шт') : 'нет',
    niches: (r.niches || []).length ? (r.niches.length + ' шт') : 'нет',
    own: r.own ? 'свой' : 'общий',
    pos: mm(r.x0) + ', ' + mm(r.y0) + (num(r.a0) ? ' · ' + f1(mod(num(r.a0), 360)) + '°' : ''),
    kv: G && G.g && !G.err ? fm2(Math.abs(area(G.g.poly))) + ' м²' : '—',
  };
}
function renderRoomSums() {
  const r = curRoom(); if (!r) return; const G = MODEL && MODEL.geo[r.id], g = G && G.g ? G.g : roomGeom(r), sm = roomSums(r, G, g);
  for (const k in sm) { const el = $('#sum-' + k); if (el) el.textContent = sm[k]; }
}
function renderRoomEditor() {
  const el = $('#roomEditor'), r = curRoom(); if (!r) { el.innerHTML = ''; return; }
  const G = MODEL && MODEL.geo[r.id], g = G && G.g ? G.g : roomGeom(r), joints = MODEL && MODEL.adj ? MODEL.adj.filter(a => a.a === r.id) : [], sm = roomSums(r, G, g);
  const walls = r.walls.map((w, i) => (i > 0 ? cornerRow(r, i) : '') + wallCard(r, i, g, joints)).join('');
  const rect = isRect(r), b = bboxOf(g.poly);
  const doors = (r.doors || []).map((d, j) => {
    const adjW = joints.filter(a => a.i === (d.wall | 0)), to = d.to && room(d.to) ? d.to : adjW[0] && adjW[0].b;
    return '<div class="orow' + (UI.item && UI.item.id === d.id ? ' sel' : '') + '" data-item="' + d.id + '"><div class="whead"><b>Проём ' + (j + 1) + (to ? ' → «' + esc(roomName(to)) + '»' : '') + '</b>' +
      '<button class="chip" type="button" data-act="item-pick" data-type="door" data-id="' + d.id + '">На карте</button>' +
      (adjW.length ? '<button class="chip" type="button" data-act="door-full" data-d="' + j + '" aria-pressed="' + !!d.full + '">Во всю стену</button>' : '') +
      '<button class="icon" type="button" data-act="door-del" data-d="' + j + '" aria-label="Удалить проём ' + (j + 1) + '">' + ICON.del + '</button></div>' +
      '<div class="ofields">' + wallSelect('id="d' + j + 'wall" data-d="' + j + '" data-df="wall"', d.wall | 0, g, true) + fldIn('От угла', 'id="d' + j + 'pos" data-d="' + j + '" data-df="pos" data-num', mm(d.pos), 'мм') + fldIn('Ширина', 'id="d' + j + 'w" data-d="' + j + '" data-df="width" data-num', mm(d.width), 'мм') + '</div></div>';
  }).join('');
  const niches = (r.niches || []).map((x, j) => {
    const ng = (g.niches || []).find(q => q.niche === x), box = x.kind === 'box';
    const state = !ng ? '<p class="note warn">Не помещается на стене ' + ((x.wall | 0) + 1) + ': проверьте «от угла» и ширину.</p>' : ng.off ? '<p class="note bad">Так не построить: два выступа в одном углу, выступ во всю стену или рядом с дугой.</p>' : '';
    return '<div class="orow' + (UI.item && UI.item.id === x.id ? ' sel' : '') + '" data-item="' + x.id + '"><div class="whead"><b>' + (box ? 'Выступ ' : 'Ниша ') + (j + 1) + (x.name ? ' · ' + esc(x.name) : '') + '</b>' +
      '<button class="chip" type="button" data-act="item-pick" data-type="niche" data-id="' + x.id + '">На карте</button>' +
      '<div class="seg mini" role="group" aria-label="Ниша или выступ"><button type="button" data-act="niche-kind" data-n="' + j + '" data-v="niche" aria-pressed="' + !box + '">Ниша</button><button type="button" data-act="niche-kind" data-n="' + j + '" data-v="box" aria-pressed="' + box + '">Выступ</button></div>' +
      '<button class="icon" type="button" data-act="niche-del" data-n="' + j + '" aria-label="Удалить ' + (box ? 'выступ' : 'нишу') + ' ' + (j + 1) + '">' + ICON.del + '</button></div>' +
      '<div class="ofields">' + wallSelect('id="n' + j + 'wall" data-n="' + j + '" data-nf="wall"', x.wall | 0, g, true) + fldIn('От угла', 'id="n' + j + 'pos" data-n="' + j + '" data-nf="pos" data-num', mm(x.pos), 'мм') +
      fldIn('Ширина', 'id="n' + j + 'w" data-n="' + j + '" data-nf="width" data-num', mm(x.width), 'мм') + fldIn(box ? 'Выступает на' : 'Глубина', 'id="n' + j + 'd" data-n="' + j + '" data-nf="depth" data-num', mm(x.depth), 'мм') + '</div>' +
      (box ? '' : '<label class="check"><input type="checkbox" id="n' + j + 'fl" data-n="' + j + '" data-nf="floor"' + (x.floor !== false ? ' checked' : '') + '> Кладём пол в нише</label>') + state + '</div>';
  }).join('');
  el.innerHTML =
    '<div class="sec"><div class="rhead"><label class="fld"><span>Название комнаты</span><span class="inp"><input class="txt" id="rName" data-rk="name" value="' + esc(r.name) + '" maxlength="40"></span></label></div>' +
    '<div class="row-btns"><button class="btn small" type="button" data-act="room-rotr">' + ICON.rot + 'Повернуть 90°</button><button class="btn small" type="button" data-act="room-dup">' + ICON.copy + 'Копия</button>' +
    (S.rooms.length > 1 ? '<button class="btn small danger" type="button" data-act="room-del">' + (UI.delArm === 'room:' + r.id ? 'Точно удалить?' : 'Удалить') + '</button>' : '') + '</div>' +
    (G && G.err ? '<p class="note bad">' + esc(G.err) + '</p>' : '') + (G && G.warn ? '<p class="note warn">' + esc(G.warn) + '</p>' : '') + '</div>' +
    acc('shape', 'Размер и форма', sm.shape,
      '<div class="grid2">' + fldIn('Длина', 'id="rL" data-rect="L"', mm(rect ? num(r.walls[0].len) : b.u1 - b.u0), 'мм') + fldIn('Ширина', 'id="rW" data-rect="W"', mm(rect ? num(r.walls[1].len) : b.v1 - b.v0), 'мм') + '</div>' +
      (rect ? '<p class="note">Прямоугольная комната: размеры меняются сразу. Для сложной формы выберите шаблон или правьте стены ниже.</p>' : '<button class="btn" type="button" data-act="room-rect">Сделать прямоугольником</button>') +
      '<div class="chips">' + TEMPLATES.filter(t => t.id !== 'rect').map(t => '<button class="chip" type="button" data-act="room-tpl" data-tpl="' + t.id + '">' + esc(t.name) + '</button>').join('') + '</div>', 'sum-shape') +
    acc('walls', 'Стены и углы', sm.walls,
      '<p class="note">Идите вдоль стен по часовой стрелке и вписывайте длины. Угол 90° — обычный, 270° — выступ внутрь комнаты. Стену можно сделать дугой. На карте нажмите на стену — появятся кнопки для неё.</p>' +
      '<div class="walls" id="walls">' + walls + '</div>' +
      '<button class="btn" type="button" data-act="wall-add">' + ICON.plus + 'Добавить стену</button><p class="note" id="closureNote"></p>', 'sum-walls') +
    acc('doors', 'Проёмы', sm.doors,
      (doors ? '<div class="olist">' + doors + '</div>' : '<p class="note">Проёмов нет. Поставьте соседнюю комнату вплотную — проём появится сам.</p>') +
      '<div class="row-btns"><button class="btn primary" type="button" data-act="place-start" data-v="door">' + ICON.plus + 'Поставить на карте</button><button class="btn" type="button" data-act="door-add">' + ICON.plus + 'Добавить цифрами</button></div>' +
      '<p class="note"><b>Поставить на карте:</b> ведите пальцем по стене — проём едет следом и показывает расстояния до углов, отпустите там, где нужно. Готовый проём тяните по стене (можно на другую стену), кружки на краях меняют ширину.</p>' +
      '<p class="note">Через проём рисунок идёт в соседнюю комнату без порога. «Во всю стену» — проход на всю общую стену, тогда стена считается до угла соседней комнаты.</p>', 'sum-doors') +
    acc('niches', 'Ниши и выступы', sm.niches,
      (niches ? '<div class="olist">' + niches + '</div>' : '') +
      '<p class="note"><b>Поставить на карте</b> — ведите пальцем по стене и отпустите там, где нужно:</p>' +
      '<div class="chips"><button class="chip add" type="button" data-act="place-start" data-v="radiator">+ Ниша под батарею</button><button class="chip add" type="button" data-act="place-start" data-v="wardrobe">+ Ниша под шкаф</button><button class="chip add" type="button" data-act="place-start" data-v="box">+ Выступ, короб</button></div>' +
      '<p class="note">Готовую нишу тяните по стене (можно на другую стену), кружки на краях — ширина, ромб на задней стенке — глубина. Ниша уходит в стену, пол в неё заходит (снимите галочку, если под шкафом пол не кладут). Выступ — короб, колонна или стояк: пол его обходит. «От угла» — от начала стены по часовой стрелке.</p>', 'sum-niches') +
    acc('own', 'Рисунок в комнате', sm.own,
      '<div class="seg" role="group" aria-label="Рисунок в комнате"><button type="button" data-act="own-set" data-v="0" aria-pressed="' + !r.own + '">Общий, сквозной</button><button type="button" data-act="own-set" data-v="1" aria-pressed="' + !!r.own + '">Свой</button></div>' +
      '<p class="note">' + (r.own ? 'У комнаты свой рисунок и своё положение. Настройте его на шаге «Рисунок», покрытие — на шаге «Покрытие».' : 'Рисунок продолжается из соседних комнат без сдвига — как при укладке без порогов.') + '</p>', 'sum-own') +
    acc('pos', 'Положение на плане', sm.pos,
      '<div class="grid3">' + fldIn('X угла 1', 'id="rX" data-rk="x0" data-num', mm(r.x0), 'мм') + fldIn('Y угла 1', 'id="rY" data-rk="y0" data-num', mm(r.y0), 'мм') + fldIn('Поворот', 'id="rA" data-rk="a0" data-num', f1(mod(num(r.a0), 360)), '°') + '</div>' +
      '<p class="note">Проще двигать комнату пальцем на карте: она прилипает к соседним через стену.</p>', 'sum-pos') +
    acc('kv', 'Итог по комнате', sm.kv, '<dl class="kv" id="roomKV"></dl>', 'sum-kv');
  renderClosure(); renderRoomKV();
}
function renderClosure() {
  const el = $('#closureNote'), r = curRoom(); if (!el || !r) return;
  const g = roomGeom(r);
  if (g.autoClosed) {
    const a = g.corners[g.n - 1], b = g.corners[0];
    el.className = 'note warn';
    el.innerHTML = 'Стены не сходятся на <b>' + mm(g.closure) + ' мм</b>. Карта замыкает комнату серой стеной ' + g.n + ' длиной ' + mm(dist(a, b)) + ' мм. Проверьте размеры или <button class="btn small" type="button" data-act="close-auto">добавьте её как стену</button>';
  } else { el.className = 'note'; el.textContent = 'Комната замкнута: ' + g.n + ' ' + plural(g.n, 'стена', 'стены', 'стен') + '. Последний угол получился ' + f1(innerAngles(g)[0]) + '°.'; }
}
function renderWallHints() {
  const r = curRoom(); if (!r) return;
  r.walls.forEach((w, i) => { const h = $('#w' + i + 'hint'); if (h) h.textContent = 'длина по дуге ≈ ' + mm(arcLength(num(w.len), num(w.arc))) + ' мм'; const rad = $('#w' + i + 'rad'); if (rad && rad !== document.activeElement && Math.abs(num(w.arc)) >= 0.5) rad.value = mm(arcRadius(num(w.len), num(w.arc))); const ar = $('#w' + i + 'arc'); if (ar && ar !== document.activeElement && Math.abs(num(w.arc)) >= 0.5) ar.value = mm(Math.abs(num(w.arc))); });
}
function renderRoomKV() {
  const el = $('#roomKV'), r = curRoom(); if (!el || !r) return;
  const G = MODEL && MODEL.geo[r.id]; if (!G || !G.g || G.err) { el.innerHTML = '<dt>Площадь</dt><dd>—</dd>'; return; }
  const g = G.g, ang = innerAngles(g), odd = ang.map((a, i) => ({ a, i })).filter(x => Math.abs(x.a - 90) > 0.4 && Math.abs(x.a - 270) > 0.4);
  el.innerHTML = '<dt>Площадь пола</dt><dd>' + fm2(Math.abs(area(g.poly))) + ' м²</dd><dt>Периметр</dt><dd>' + f1(perim(g.poly) / 1000) + ' м</dd><dt>Габарит</dt><dd>' + roomSize(g) + ' мм</dd>' +
    '<dt>Под укладку (без зазора)</dt><dd>' + fm2(Math.abs(area(G.lay))) + ' м²</dd><dt>Углы не 90°</dt><dd>' + (odd.length ? odd.map(x => (x.i + 1) + ': ' + f1(x.a) + '°').join(', ') : 'нет') + '</dd>';
}
function onWallInput(t) {
  const r = curRoom(), i = +t.dataset.w, w = r.walls[i]; if (!w) return;
  const v = num(t.value, NaN); if (!Number.isFinite(v)) return;
  const f = t.dataset.wf;
  if (f === 'len') { if (v <= 0) return; w.len = v; }
  else if (f === 'ang') { w.turn = 180 - v; $$('[data-act="corner-set"][data-w="' + i + '"]').forEach(b => b.setAttribute('aria-pressed', String(Math.abs(num(b.dataset.v) - v) < 0.05))); }
  else if (f === 'arc') { const sg = num(w.arc) < 0 ? -1 : 1; w.arc = sg * Math.max(1, Math.abs(v)); }
  else if (f === 'rad') { const h = sagittaFromRadius(num(w.len), v); if (!Number.isFinite(h)) { say('Радиус меньше половины хорды (' + mm(num(w.len) / 2) + ' мм) — так дугу не построить.', 'bad'); return; } const sg = num(w.arc) < 0 ? -1 : 1; w.arc = sg * Math.max(1, h); }
  renderClosure(); renderWallHints(); invalidate();
}
/* новая комната встаёт вплотную к выбранной (справа, снизу, слева или сверху) — там, где свободно */
function placeAttached(walls, a0) {
  const T = Math.max(0, num(S.set.wallT, 120)), cur = curRoom(), G = cur && MODEL && MODEL.geo[cur.id];
  const nb = bboxOf(roomGeom({ x0: 0, y0: 0, a0: num(a0), walls }).poly), W = nb.u1 - nb.u0, H = nb.v1 - nb.v0;
  const busy = (x, y) => S.rooms.some(o => { const og = MODEL && MODEL.geo[o.id]; if (!og || !og.g) return false; const ob = bboxOf(og.g.poly); return x < ob.u1 - 1 && x + W > ob.u0 + 1 && y < ob.v1 - 1 && y + H > ob.v0 + 1; });
  if (G && G.g && !G.err) {
    const b = bboxOf(G.g.poly);
    for (const [x, y] of [[b.u1 + T, b.v0], [b.u0, b.v1 + T], [b.u0 - T - W, b.v0], [b.u0, b.v0 - T - H]]) if (!busy(x, y)) return [Math.round(x - nb.u0), Math.round(y - nb.v0)];
  }
  const fb = floorBBox(); return fb ? [Math.round(fb.u1 + 1000 - nb.u0), Math.round(fb.v0 - nb.v0)] : [0, 0];
}
/* проёмы между приставленными комнатами: появляются сами, держатся в пределах общей стены */
const pairKey = (a, b) => [a, b].sort().join('|');
function doorWidthFor(span) { return span >= 1100 ? 900 : span >= 700 ? Math.round((span - 200) / 10) * 10 : Math.floor(span); }
/* новый проём выделяем, только когда комнату приставили (перетащили или добавили) — не при повороте */
let NEW_DOOR = null;
function selectNewDoor() { if (NEW_DOOR && itemRef(NEW_DOOR)) { UI.item = NEW_DOOR; UI.wall = null; } NEW_DOOR = null; }
function syncAutoDoors(changed) {
  NEW_DOOR = null; const set = new Set(changed), geo = computeGeo(S), adj = adjacency(S, geo), made = [], idx = id => S.rooms.findIndex(r => r.id === id);
  S.noDoor = S.noDoor || [];
  for (const r of S.rooms) {
    r.doors = (r.doors || []).filter(d => {
      if (!d.auto || !(set.has(r.id) || (d.to && set.has(d.to)))) return true;
      const list = adj.filter(a => a.a === r.id && a.i === (d.wall | 0)); if (!list.length) return false;
      const mid = num(d.pos) + num(d.width) / 2, a = list.find(x => mid >= x.o0 && mid <= x.o1) || list.slice().sort((x, y) => (y.o1 - y.o0) - (x.o1 - x.o0))[0], span = a.o1 - a.o0;
      d.to = a.b;
      if (d.full) { d.pos = Math.round(a.o0); d.width = Math.floor(span); }
      else { d.width = Math.min(num(d.width), Math.floor(span)); d.pos = Math.round(clamp(num(d.pos), a.o0, a.o1 - d.width)); }
      return true;
    });
  }
  for (const a of adj) {
    if (!set.has(a.a) && !set.has(a.b)) continue;
    const ownA = set.has(a.b) && !set.has(a.a) ? true : set.has(a.a) && !set.has(a.b) ? false : idx(a.a) < idx(a.b);
    if (!ownA || S.noDoor.includes(pairKey(a.a, a.b))) continue;
    const ra = room(a.a), rb = room(a.b);
    const between = (r, o) => (r.doors || []).some(d => d.to === o);
    if (between(ra, a.b) || between(rb, a.a)) continue;
    if ((ra.doors || []).some(d => (d.wall | 0) === a.i && num(d.pos) < a.o1 && num(d.pos) + num(d.width) > a.o0)) continue;
    if ((rb.doors || []).some(d => (d.wall | 0) === a.j && num(d.pos) < a.p1 && num(d.pos) + num(d.width) > a.p0)) continue;
    const span = a.o1 - a.o0, w = doorWidthFor(span), full = w >= span - 1;
    const d = { id: newId('d'), wall: a.i, pos: Math.round(a.o0 + (span - w) / 2), width: w, auto: true, to: a.b }; if (full) d.full = true;
    ra.doors = ra.doors || []; ra.doors.push(d); made.push({ ra, rb, d });
  }
  if (!made.length) return '';
  const m = made[made.length - 1]; NEW_DOOR = { type: 'door', rid: m.ra.id, id: m.d.id };
  return 'Комнаты «' + m.ra.name + '» и «' + m.rb.name + '» соединены: ' + (m.d.full ? 'проход во всю общую стену' : 'проём ' + mm(m.d.width) + ' мм') + '. Проём можно тянуть по стене, кружки на краях — ширина. Размеры стены делятся по стыку.';
}
function doorFull(r, d) {
  const geo = computeGeo(S), list = adjacency(S, geo).filter(a => a.a === r.id && a.i === (d.wall | 0)); if (!list.length) return;
  const mid = num(d.pos) + num(d.width) / 2, a = list.find(x => mid >= x.o0 && mid <= x.o1) || list[0], span = a.o1 - a.o0;
  if (!d.full) { d.full = true; d.pos = Math.round(a.o0); d.width = Math.floor(span); }
  else { delete d.full; d.width = doorWidthFor(span) >= span - 1 ? Math.floor(span) : Math.min(900, doorWidthFor(span)); d.pos = Math.round(a.o0 + (span - d.width) / 2); }
  d.to = a.b;
}
function removeDoor(r, d) {
  const geo = computeGeo(S), a = adjacency(S, geo).find(x => x.a === r.id && x.i === (d.wall | 0) && num(d.pos) < x.o1 && num(d.pos) + num(d.width) > x.o0), to = d.to || (a && a.b);
  r.doors = (r.doors || []).filter(x => x !== d);
  if (to) { S.noDoor = S.noDoor || []; const k = pairKey(r.id, to); if (!S.noDoor.includes(k)) S.noDoor.push(k); }
  if (UI.item && UI.item.id === d.id) UI.item = null;
}
function addDoorOn(r, i, t) {
  const g = (MODEL.geo[r.id] || {}).g || roomGeom(r), c = dist(g.corners[i], g.corners[(i + 1) % g.n]);
  const a = (MODEL.adj || []).find(x => x.a === r.id && x.i === i && (t === undefined || (t >= x.o0 - 1 && t <= x.o1 + 1)));
  let pos, w;
  if (a) { const span = a.o1 - a.o0; w = doorWidthFor(span); pos = a.o0 + (span - w) / 2; if (t !== undefined && span > w + 50) pos = clamp(t - w / 2, a.o0, a.o1 - w); S.noDoor = (S.noDoor || []).filter(k => k !== pairKey(r.id, a.b)); }
  else { w = Math.min(900, Math.max(300, c - 200)); pos = t === undefined ? (c - w) / 2 : clamp(t - w / 2, 0, c - w); }
  const d = { id: newId('d'), wall: i, pos: Math.round(pos), width: Math.round(w) }; if (a) { d.to = a.b; d.auto = true; if (w >= a.o1 - a.o0 - 1) d.full = true; }
  r.doors = r.doors || []; r.doors.push(d); UI.item = { type: 'door', rid: r.id, id: d.id }; UI.wall = null; return d;
}
function setArc(r, i, on) {
  const w = r.walls[i]; if (!w) return;
  if (on) { if (Math.abs(num(w.arc)) < 0.5) w.arc = Math.round(num(w.len) * 0.12 / 10) * 10 || 100; r.doors = (r.doors || []).filter(d => (d.wall | 0) !== i); r.niches = (r.niches || []).filter(x => (x.wall | 0) !== i); }
  else w.arc = 0;
}
/* разделить прямую стену в точке t: появляется угол 180°, его можно тянуть */
function splitWall(r, i, t) {
  const w = r.walls[i]; if (!w) return; const c = num(w.len);
  r.walls.splice(i, 1, { len: t, turn: w.turn, arc: 0 }, { len: c - t, turn: 0, arc: 0 });
  const fix = list => (list || []).map(d => { if (d.wall > i) d.wall++; else if (d.wall === i && num(d.pos) >= t - 1) { d.wall = i + 1; d.pos = Math.max(0, num(d.pos) - t); } return d; });
  r.doors = fix(r.doors); r.niches = fix(r.niches);
}
function focusLast(sec) { setTimeout(() => { const list = $$('details[data-acc="' + sec + '"] .orow'), el = list[list.length - 1]; if (el && el.scrollIntoView) el.scrollIntoView({ block: 'nearest', behavior: 'smooth' }); }, 60); }
const NICHE_PRESET = { radiator: { kind: 'niche', width: 1200, depth: 120, name: 'под батарею' }, wardrobe: { kind: 'niche', width: 1500, depth: 600, name: 'под шкаф' }, box: { kind: 'box', width: 400, depth: 300, name: 'короб' } };
function addNicheOn(r, i, t, preset) {
  const g = (MODEL.geo[r.id] || {}).g || roomGeom(r), c = dist(g.corners[i], g.corners[(i + 1) % g.n]), p = NICHE_PRESET[preset] || NICHE_PRESET.radiator;
  const width = Math.min(p.width, Math.max(100, Math.round(c - 100))); let pos;
  if (t === undefined) pos = p.kind === 'box' ? 0 : (c - width) / 2;
  else { pos = clamp(t - width / 2, 0, c - width); if (p.kind === 'box') { if (t < 600) pos = 0; else if (c - t < 600) pos = c - width; } }
  const x = { id: newId('n'), kind: p.kind, wall: i, pos: Math.round(pos), width, depth: p.depth, floor: true, name: p.name };
  r.niches = r.niches || []; r.niches.push(x); UI.item = { type: 'niche', rid: r.id, id: x.id }; UI.wall = null; return x;
}

/* ================= действия (клики) ================= */
const ACT = {
  'go': b => setTab(b.dataset.v),
  'room-select': b => { UI.room = b.dataset.room; UI.delArm = null; UI.wallFocus = -1; UI.wall = null; UI.item = null; UI.place = null; renderPlanTab(); renderCtxbar(); draw(); saveUI(); },
  'room-add-open': () => { UI.addRoom = !UI.addRoom; $('#addRoomBox').hidden = !UI.addRoom; renderRoomList(); if (UI.addRoom) { const el = $('#newL'); if (el) el.focus(); } },
  'room-add-rect': () => { const L = num($('#newL').value), W = num($('#newW').value); if (!(L >= 300 && W >= 300)) { say('Впишите длину и ширину новой комнаты в миллиметрах.', 'bad'); return; } addRoom(rectWalls(L, W), 'Комната ' + (S.rooms.length + 1)); },
  'room-add-tpl': b => { const t = TEMPLATES.find(x => x.id === b.dataset.tpl); if (t) addRoom(t.make(), t.name); },
  'room-dup': () => { const r = curRoom(), c = deep(r); c.id = newId('r'); c.name = r.name + ' (копия)'; c.doors = []; [c.x0, c.y0] = placeAttached(c.walls, c.a0); S.rooms.push(c); UI.room = c.id; UI.wall = null; const msg = syncAutoDoors([c.id]); recomputeNow(); selectNewDoor(); view.fitted = false; afterRooms(msg || 'Копия добавлена рядом.'); fitView(); draw(); },
  'room-rot': () => ACT['room-rotr'](),
  'room-rotr': () => { const r = curRoom(); rotateRoomBy(r, 90); const msg = syncAutoDoors([r.id]); afterRooms(msg || 'Комната повёрнута на 90° по часовой стрелке.'); },
  'add-start': () => { UI.addTpl = 'rect'; UI.wall = null; UI.item = null; UI.place = null; renderCtxbar(); draw(); say('Нажмите на карту, где поставить комнату, или нарисуйте прямоугольник пальцем. У соседней стены комната прилипнет, и появится проём.', null, true); },
  'add-tpl': b => { UI.addTpl = b.dataset.tpl; renderCtxbar(); say('Нажмите на карту, где поставить «' + (TEMPLATES.find(t => t.id === b.dataset.tpl) || {}).name + '».', null, true); },
  'add-cancel': () => { UI.addTpl = null; UI.addPrev = null; renderCtxbar(); modeHint(); draw(); },
  'rot-step': b => { const c = dirCtx(UI.target); if (!c) return; const P = curP(); setDirection(P, fullAngle(P) + num(b.dataset.v), c); clearVariants(); syncPatInputs(); syncPatternUI(); renderCtxbar(); invalidate({ fast: true }); say('Угол к опорной стене: ' + f1(shownAngle(P)) + '°.'); },
  'room-del': () => { const r = curRoom(); if (UI.delArm !== 'room:' + r.id) { UI.delArm = 'room:' + r.id; renderRoomEditor(); renderCtxbar(); return; } S.rooms = S.rooms.filter(x => x.id !== r.id); for (const o of S.rooms) o.doors = (o.doors || []).filter(d => d.to !== r.id || !d.auto); UI.delArm = null; UI.wall = null; UI.item = null; UI.room = S.rooms[0].id; afterRooms('Комната удалена.'); },
  'room-rect': () => { const L = num($('#rL').value), W = num($('#rW').value); if (!(L >= 300 && W >= 300)) { say('Впишите длину и ширину в миллиметрах.', 'bad'); return; } const r = curRoom(); r.walls = rectWalls(L, W); r.doors = (r.doors || []).filter(d => d.wall < 4); r.niches = (r.niches || []).filter(x => x.wall < 4); const msg = syncAutoDoors([r.id]); afterRooms(msg); },
  'room-tpl': b => { const t = TEMPLATES.find(x => x.id === b.dataset.tpl); if (!t) return; const r = curRoom(); r.walls = t.make(); r.doors = []; r.niches = []; UI.wall = null; const msg = syncAutoDoors([r.id]); afterRooms(msg || 'Форма «' + t.name + '»: поправьте длины стен под свою комнату.'); },
  'wall-shape': b => { setArc(curRoom(), +b.dataset.w, b.dataset.v === 'arc'); UI.wallFocus = +b.dataset.w; renderRoomEditor(); renderCtxbar(); invalidate({ fast: true }); },
  'wall-side': b => { const w = curRoom().walls[+b.dataset.w]; if (!w) return; w.arc = (b.dataset.v === 'in' ? -1 : 1) * Math.abs(num(w.arc)); renderRoomEditor(); invalidate({ fast: true }); },
  'wall-split': b => { const r = curRoom(), i = +b.dataset.w, w = r.walls[i]; if (!w || Math.abs(num(w.arc)) >= 0.5) return; splitWall(r, i, num(w.len) / 2); UI.wallFocus = i + 1; renderRoomEditor(); invalidate({ fast: true }); say('Стена разделена. Впишите новые длины и угол между частями.'); },
  'wall-del': b => { const r = curRoom(), i = +b.dataset.w; if (r.walls.length <= 2) return; r.walls.splice(i, 1); if (i === 0 && r.walls[0]) r.walls[0].turn = 0; const fix = list => (list || []).filter(d => (d.wall | 0) !== i).map(d => d.wall > i ? Object.assign(d, { wall: d.wall - 1 }) : d); r.doors = fix(r.doors); r.niches = fix(r.niches); UI.wall = null; renderRoomEditor(); renderCtxbar(); invalidate({ fast: true }); },
  'wall-add': () => { const r = curRoom(); r.walls.push({ len: 1000, turn: 90, arc: 0 }); UI.wallFocus = r.walls.length - 1; UI.open.walls = true; renderRoomEditor(); invalidate({ fast: true }); const el = $('#w' + (r.walls.length - 1) + 'len'); if (el) { el.focus(); el.select(); } },
  'corner-set': b => { const r = curRoom(), w = r.walls[+b.dataset.w]; if (!w) return; w.turn = 180 - num(b.dataset.v); renderRoomEditor(); invalidate({ fast: true }); },
  'close-auto': () => { const r = curRoom(), g = roomGeom(r); Object.assign(r, wallsFromCorners(g.corners, g.arcs)); renderRoomEditor(); invalidate({ fast: true }); },
  // стена, выбранная на карте
  'wall-back': () => { UI.wall = null; renderCtxbar(); draw(); modeHint(); },
  'wall-door': () => { const W = wallOk(); if (!W) return; const d = addDoorOn(W.r, W.i, W.t); UI.open.doors = true; UI.wall = null; afterRooms((d.full ? 'Проход во всю общую стену' : 'Проём ' + mm(d.width) + ' мм') + ' на стене ' + (W.i + 1) + (d.to ? ' в «' + roomName(d.to) + '»' : '') + '. Точное место и ширина — в разделе «Проёмы».'); },
  'wall-niche': () => { const W = wallOk(); if (!W) return; const x = addNicheOn(W.r, W.i, W.t, 'radiator'); UI.open.niches = true; afterRooms('Ниша ' + mm(x.width) + '×' + mm(x.depth) + ' мм на стене ' + (W.i + 1) + '. Размеры, «под шкаф» и пол в нише — в разделе «Ниши и выступы».'); focusLast('niches'); },
  'wall-box': () => { const W = wallOk(); if (!W) return; const x = addNicheOn(W.r, W.i, W.t, 'box'); UI.open.niches = true; afterRooms('Выступ ' + mm(x.width) + '×' + mm(x.depth) + ' мм на стене ' + (W.i + 1) + (x.pos === 0 ? ', в углу' : '') + '. Размеры — в разделе «Ниши и выступы».'); focusLast('niches'); },
  'wall-arc': () => { const W = wallOk(); if (!W) return; setArc(W.r, W.i, Math.abs(W.g.arcs[W.i]) < 0.5); afterRooms(Math.abs(num(W.r.walls[W.i].arc)) >= 0.5 ? 'Стена ' + (W.i + 1) + ' — дуга. Тяните ромб на стене или впишите прогиб в разделе «Стены».' : 'Стена ' + (W.i + 1) + ' снова прямая.'); },
  'wall-cut': () => { const W = wallOk(); if (!W) return; const c = num(W.r.walls[W.i] && W.r.walls[W.i].len), t = Math.round(clamp(W.t, 100, c - 100) / 10) * 10; if (!(c > 300)) return; splitWall(W.r, W.i, t); UI.wall = null; UI.open.walls = true; UI.wallFocus = W.i + 1; afterRooms('Стена разделена: ' + mm(t) + ' + ' + mm(c - t) + ' мм. Тяните новый угол на карте или впишите угол в разделе «Стены».'); },
  'door-full': b => { const ref = { r: curRoom(), d: curRoom().doors[+b.dataset.d] }; if (!ref.d) return; doorFull(ref.r, ref.d); ref.d.auto = true; afterRooms(ref.d.full ? 'Проход во всю общую стену: ' + mm(ref.d.width) + ' мм. Стена считается до угла соседней комнаты.' : 'Обычный проём ' + mm(ref.d.width) + ' мм по центру общей стены.'); },
  // проём и ниша, которые человек ставит сам
  'place-start': b => { UI.place = b.dataset.v || 'door'; UI.item = null; UI.wall = null; UI.addTpl = null; renderCtxbar(); draw(); say('Ведите пальцем по стене: ' + (UI.place === 'door' ? 'проём' : 'ниша') + ' едет следом и показывает расстояния до углов. Отпустите — встанет там.', null, true); syncTgBack(); },
  'place-kind': b => { UI.place = b.dataset.v; renderCtxbar(); say('Ведите пальцем по стене и отпустите там, где нужно.', null, true); },
  'place-cancel': () => { UI.place = null; UI.ghost = null; renderCtxbar(); modeHint(); draw(); syncTgBack(); },
  'item-pick': b => { const it = { type: b.dataset.type, rid: curRoom().id, id: b.dataset.id }; if (!itemRef(it)) { say('Он на стене-дуге или за пределами стены — поправьте цифры.', 'bad'); return; } selectItem(it); },
  'item-back': () => { UI.item = null; renderCtxbar(); renderRoomEditor(); applyAcc(); draw(); modeHint(); syncTgBack(); },
  'item-del': () => { const ref = itemRef(); if (!ref) return; if (ref.type === 'door') removeDoor(ref.r, ref.x); else ref.r.niches = ref.r.niches.filter(q => q !== ref.x); UI.item = null; afterRooms(ref.type === 'door' ? 'Проём удалён.' + (ref.x.to ? ' Стена между комнатами глухая — рисунок в соседнюю комнату не идёт.' : '') : 'Удалено.'); },
  'item-full': () => { const ref = itemRef(); if (!ref || ref.type !== 'door') return; doorFull(ref.r, ref.x); ref.x.auto = true; afterRooms(ref.x.full ? 'Проход во всю общую стену: ' + mm(ref.x.width) + ' мм. Стена считается до угла соседней комнаты.' : 'Обычный проём ' + mm(ref.x.width) + ' мм по центру общей стены.'); },
  'item-kind': b => { const ref = itemRef(); if (!ref) return; ref.x.kind = b.dataset.v; afterRooms(b.dataset.v === 'box' ? 'Теперь это выступ: пол его обходит.' : 'Теперь это ниша: пол заходит в неё.'); },
  'item-floor': () => { const ref = itemRef(); if (!ref) return; ref.x.floor = ref.x.floor === false; afterRooms(ref.x.floor === false ? 'В нише пол не кладём (например, под встроенным шкафом).' : 'Пол заходит в нишу.'); },
  'door-add': () => { const r = curRoom(), g = roomGeom(r); let wi = UI.wallFocus >= 0 && UI.wallFocus < g.n && Math.abs(g.arcs[UI.wallFocus]) < 0.5 ? UI.wallFocus : -1; if (wi < 0) { const a = (MODEL.adj || []).find(x => x.a === r.id); if (a) wi = a.i; } if (wi < 0) { let best = 0; for (let i = 0; i < g.n; i++) { const c = dist(g.corners[i], g.corners[(i + 1) % g.n]); if (Math.abs(g.arcs[i]) < 0.5 && c > best && c > 600) { best = c; wi = i; } } } if (wi < 0) { say('Нужна прямая стена длиннее 600 мм.', 'bad'); return; } const d = addDoorOn(r, wi); afterRooms('Проём ' + mm(d.width) + ' мм на стене ' + (wi + 1) + (d.to ? ' в «' + roomName(d.to) + '»' : '. Поставьте соседнюю комнату вплотную — рисунок пройдёт через проём.')); },
  'door-del': b => { const r = curRoom(), d = r.doors[+b.dataset.d]; if (!d) return; removeDoor(r, d); afterRooms('Проём удалён.'); },
  'niche-add': b => { const r = curRoom(), g = roomGeom(r); let wi = UI.wallFocus >= 0 && UI.wallFocus < g.n && Math.abs(g.arcs[UI.wallFocus]) < 0.5 ? UI.wallFocus : -1; if (wi < 0) for (let i = 0; i < g.n; i++) if (Math.abs(g.arcs[i]) < 0.5 && !(MODEL.adj || []).some(a => a.a === r.id && a.i === i)) { wi = i; break; } if (wi < 0) wi = 0; const x = addNicheOn(r, wi, undefined, b.dataset.v); afterRooms((x.kind === 'box' ? 'Выступ' : 'Ниша') + ' ' + mm(x.width) + '×' + mm(x.depth) + ' мм на стене ' + (wi + 1) + '. Поправьте стену и «от угла».'); focusLast('niches'); },
  'niche-del': b => { const r = curRoom(); r.niches.splice(+b.dataset.n, 1); afterRooms('Удалено.'); },
  'niche-kind': b => { const x = curRoom().niches[+b.dataset.n]; if (!x) return; x.kind = b.dataset.v; renderRoomEditor(); invalidate({ fast: true }); },
  'own-set': b => { const r = curRoom(); r.own = b.dataset.v === '1'; if (r.own) { r.pat = Object.assign(deep(S.floorPat), { refRoom: r.id, refWall: 0 }); UI.target = 'room:' + r.id; } afterRooms(r.own ? 'У комнаты «' + r.name + '» теперь свой рисунок — настройте его на шаге «Рисунок».' : 'Комната снова в общем рисунке.'); if (r.own) { recomputeNow(); centerTarget(UI.target, true); invalidate({ fast: true }); } },
  // покрытие
  'mat-target': b => { UI.matTarget = b.dataset.key; const m = curMat(false); if (m && m.cat) UI.catView = m.cat; renderMatTab(); },
  'cat': b => { UI.catView = b.dataset.cat; renderCats(); renderSizes(); },
  'item': b => { const cat = catById(UI.catView), it = allItems(cat).find(x => x.id === b.dataset.item); if (it) applyItem(cat, it); },
  'tone': b => { const m = curMat(true); m.tone = b.dataset.tone; renderTones(); invalidate(); if (UI.tab === 'pat') renderPatList(); },
  'save-custom': () => saveCustom(),
  // рисунок
  'pat-target': b => { UI.target = b.dataset.key; UI.variants = null; renderPatTab(); renderCtxbar(); renderStatus(); draw(); },
  'pat': b => { const P = curP(); setPatternType(P, b.dataset.pat); clearVariants(); recomputeNow(); centerTarget(UI.target, true); renderPatTab(); renderCtxbar(); invalidate({ fast: true }); },
  'dir': b => { const P = curP(); P.dir = b.dataset.v; P.flipU = false; clearVariants(); recomputeNow(); centerTarget(UI.target, true); syncPatternUI(); renderCtxbar(); invalidate({ fast: true }); },
  'center': () => { recomputeNow(); centerTarget(UI.target, false); clearVariants(); invalidate({ fast: true }); },
  'corner0': () => { const P = curP(); P.offA = 0; P.offB = 0; syncPatInputs(); clearVariants(); invalidate({ fast: true }); },
  'optimize': () => optimize(),
  'variant': b => { const v = UI.variants && UI.variants.list[+b.dataset.i]; if (!v) return; const P = curP(); P.offA = v.offA; P.offB = v.offB; UI.variants.cur = +b.dataset.i; syncPatInputs(); renderVariants(); invalidate({ fast: true }); },
  'flipV': () => { const P = curP(); P.flipV = !P.flipV; clearVariants(); invalidate({ fast: true }); },
  'flipU': () => { const P = curP(), c = dirCtx(UI.target), th = fullAngle(P); P.flipU = !P.flipU; if (c) setDirection(P, th + 180, c); clearVariants(); syncPatInputs(); renderCtxbar(); invalidate({ fast: true }); },
  'shuffle': () => { const P = curP(); P.seed = (num(P.seed, 1) | 0) + 1; invalidate({ fast: true }); },
  'border-toggle': () => { const r = curRoom(); r.border.on = !r.border.on; if (r.border.on) UI.target = 'border:' + r.id; afterRooms(r.border.on ? 'Рамка включена. Ниже выберите рисунок рамки, центр настраивается отдельно.' : 'Рамка выключена.'); },
  'border-type': b => { const r = curRoom(); r.border.pat.type = b.dataset.v; renderComposite(); invalidate({ fast: true }); },
  'border-tone': b => { const r = curRoom(); if (!r.border.mat) r.border.mat = deep(S.mat); r.border.mat.tone = b.dataset.tone; renderComposite(); invalidate({ fast: true }); },
  'ins-add': () => { const r = curRoom(), G = MODEL.geo[r.id]; if (!G || G.err) return; const b = bboxOf(G.center); const ins = { id: newId('i'), w: Math.round((b.u1 - b.u0) * 0.55 / 10) * 10, h: Math.round((b.v1 - b.v0) * 0.55 / 10) * 10, dx: 0, dy: 0, rot: 0, pat: defaultPat('basket'), mat: null }; r.inserts = r.inserts || []; r.inserts.push(ins); UI.target = 'ins:' + r.id + ':' + ins.id; recomputeNow(); centerTarget(UI.target, true); renderPatTab(); invalidate({ fast: true }); say('Вставка добавлена в центр комнаты. Задайте её размер и рисунок.'); },
  'ins-del': b => { const r = curRoom(); r.inserts.splice(+b.dataset.ins, 1); afterRooms('Вставка удалена.'); },
  'ins-rot': b => { const ins = curRoom().inserts[+b.dataset.ins]; if (!ins) return; ins.rot = num(b.dataset.v); renderComposite(); invalidate({ fast: true }); },
  'ins-edit': b => { UI.target = b.dataset.key; renderPatTab(); renderStatus(); draw(); },
  // расчёт
  'res-target': b => { UI.target = b.dataset.key; renderResults(); renderStatus(); draw(); },
  'grp': b => { const key = b.dataset.key, gk = b.dataset.gk; UI.hl = UI.hl && UI.hl.gk === gk && UI.hl.key === key ? null : { key, gk }; $$('.grp').forEach(x => x.setAttribute('aria-pressed', String(!!UI.hl && x.dataset.gk === UI.hl.gk && x.dataset.key === UI.hl.key))); draw(); },
  'export-img': () => exportImage(), 'export-copy': () => copyReport(), 'export-file': () => exportProject(), 'export-share': () => shareReport(),
  'install': () => { if (!deferredPrompt) return; deferredPrompt.prompt(); deferredPrompt.userChoice.then(c => { if (c && c.outcome === 'accepted') { UI.installOff = true; saveUI(); } deferredPrompt = null; renderInstall(); }).catch(() => {}); },
  'install-off': () => { UI.installOff = true; saveUI(); renderInstall(); },
  'piece-close': () => { UI.sel = null; UI.hl = null; renderPieceInfo(); draw(); },
  'piece-hl': () => { const sp = selectedPiece(); if (!sp) return; UI.hl = UI.hl && UI.hl.gk === sp.p.gk ? null : { key: sp.res.unit.key, gk: sp.p.gk }; renderPieceInfo(); draw(); },
};
$('.app').addEventListener('click', e => { const b = e.target.closest('[data-act]'); if (!b || b.disabled) return; const f = ACT[b.dataset.act]; if (f) f(b); });
document.addEventListener('focusin', e => { const c = e.target.closest && e.target.closest('.wcard'); if (c) { const i = +c.dataset.wi; if (i !== UI.wallFocus) { UI.wallFocus = i; $$('.wcard').forEach(x => x.classList.toggle('sel', +x.dataset.wi === i)); } } });
function addRoom(walls, name) {
  const [x, y] = placeAttached(walls, 0), r = newRoom(name, walls, x, y); S.rooms.push(r); UI.room = r.id; UI.addRoom = false; UI.wall = null;
  const msg = syncAutoDoors([r.id]); recomputeNow(); selectNewDoor();
  view.fitted = false; afterRooms(msg || 'Комната «' + name + '» добавлена. Тяните её на карте к соседней — прилипнет, и появится проём.'); recomputeNow(); fitView(); draw();
}
function afterRooms(msg) { recomputeNow(); renderPlanTab(); renderCtxbar(); if (UI.tab === 'pat') renderPatTab(); if (UI.tab === 'mat') renderMatTab(); invalidate({ fast: true }); if (msg) say(msg); }

/* ================= 2. Покрытие ================= */
function allItems(cat) { return cat.id === 'custom' ? Store.mats.map(m => Object.assign({}, m, { id: 'c:' + m.id })) : cat.items.map((it, i) => Object.assign({}, it, { id: cat.id + ':' + i })); }
function renderMatTab() {
  const keys = matKeys();
  $('#matTargets').innerHTML = keys.map(k => '<button class="chip" type="button" data-act="mat-target" data-key="' + k + '" aria-pressed="' + (k === UI.matTarget) + '">' + esc(matKeyName(k)) + '</button>').join('');
  const h = UI.matTarget === 'main' ? null : matHolder(UI.matTarget), useMain = !!h && !h.mat;
  $('#matUseMainFld').hidden = UI.matTarget === 'main'; $('#matUseMain').checked = useMain;
  $('#matEditor').hidden = useMain;
  $('#matTargetNote').textContent = UI.matTarget === 'main' ? (keys.length > 1 ? 'Основное покрытие — для общего рисунка. Рамку, вставки и комнаты со своим рисунком можно сделать из другого покрытия.' : 'Покрытие для всего этажа.') : useMain ? 'Используется основное покрытие. Снимите галочку, чтобы выбрать другое.' : 'Своё покрытие для «' + matKeyName(UI.matTarget) + '».';
  renderCats(); renderSizes(); renderTones(); syncInputs(); renderSums();
}
$('#matUseMain').addEventListener('change', e => { const h = matHolder(UI.matTarget); if (!h) return; h.mat = e.target.checked ? null : deep(S.mat); renderMatTab(); invalidate({ fast: true }); });
function renderCats() { $('#catChips').innerHTML = CATS.map(c => '<button class="chip" type="button" data-act="cat" data-cat="' + c.id + '" aria-pressed="' + (UI.catView === c.id) + '">' + esc(c.name) + '</button>').join(''); }
function renderSizes() {
  const cat = catById(UI.catView), items = allItems(cat), m = curMat(false);
  $('#sizesTitle').textContent = cat.name + ' — размеры';
  $('#sizesNote').textContent = cat.id === 'custom' ? (items.length ? 'Ваши сохранённые размеры.' : 'Здесь появятся ваши размеры. Впишите длину и ширину ниже и нажмите «В свои размеры».') : 'Типовые размеры. Если у вашей планки другие — впишите их ниже, расчёт обновится сразу.';
  $('#sizeList').innerHTML = items.map(it => {
    const sel = m.item === it.id || (!m.item && m.cat === cat.id && Math.abs(num(m.L) - it.L) < 0.5 && Math.abs(num(m.W) - it.W) < 0.5 && (m.shape || 'plank') === (it.shape || 'plank'));
    return '<button class="size" type="button" data-act="item" data-item="' + it.id + '" aria-pressed="' + sel + '"><b>' + mm(it.L) + '×' + mm(it.W) + '</b><span>' + esc([it.name, it.note, it.T ? it.T + ' мм' : ''].filter(Boolean).join(' · ')) + '</span></button>';
  }).join('');
}
function renderTones() { const m = curMat(false); $('#tones').innerHTML = Object.entries(TONES).map(([k, t]) => '<button class="tone" type="button" data-act="tone" data-tone="' + k + '" title="' + t.n + '" aria-label="' + t.n + '" aria-pressed="' + ((m.tone || 'oak') === k) + '" style="background:' + rgb(t.c) + '"></button>').join(''); }
function applyItem(cat, it) {
  const m = curMat(true);
  Object.assign(m, { cat: cat.id, item: it.id, L: it.L, W: it.W, T: it.T || '', shape: it.shape || 'plank', joint: it.joint !== undefined ? it.joint : (cat.joint || 0), tone: it.tone || cat.tone });
  const tk = UI.matTarget === 'main' ? 'floor' : UI.matTarget;
  if (UI.matTarget === 'main') { S.set.gap = cat.gap; S.set.kerf = cat.kerf; }
  if (targetKind(tk) !== 'border') {
    const P = patOf(tk), pid = it.shape === 'chevron' ? 'chevron' : (it.pat || cat.pat);
    setPatternType(P, pid);
    P.minPiece = Math.min(cat.minPiece, Math.round(it.L * 0.35 / 10) * 10 || cat.minPiece); P.minStag = Math.min(cat.minStag, Math.round(it.L * 0.3 / 10) * 10 || cat.minStag);
    if (it.angle) P.chevAngle = it.angle;
    if (UI.matTarget === 'main') for (const r of S.rooms) if (r.own && !r.mat) setPatternType(r.pat, pid);
    recomputeNow(); if (availTargets().includes(tk)) centerTarget(tk, true);
  }
  syncInputs(); renderSizes(); renderTones(); invalidate({ fast: true });
  say('Выбрано: ' + cat.name.toLowerCase() + ' ' + mm(it.L) + '×' + mm(it.W) + ' мм' + (targetKind(tk) !== 'border' ? ', рисунок «' + patDef(patOf(tk).type).name + '»' : '') + '.');
}
async function saveCustom() {
  const m = curMat(false), L = num(m.L), W = num(m.W); if (!(L >= 20 && W >= 20)) { say('Сначала впишите длину и ширину планки.', 'bad'); return; }
  const name = $('#customName').value.trim() || (catById(m.cat).name + ' ' + mm(L) + '×' + mm(W));
  const it = { id: Date.now().toString(36), name, L, W, T: num(m.T) || '', shape: m.shape, joint: num(m.joint), tone: m.tone };
  await Store.saveMats([...Store.mats, it]); $('#customName').value = ''; UI.catView = 'custom'; m.cat = 'custom'; m.item = 'c:' + it.id; renderCats(); renderSizes(); say('Размер «' + name + '» сохранён в «Свои размеры».', 'ok');
}

/* ================= 3. Рисунок ================= */
function setPatternType(P, id) {
  const old = patDef(P.type), nw = patDef(id); P.type = id;
  if (old.group !== nw.group || P.minEdge === undefined) { P.minEdge = nw.group === 'bond' ? 50 : 25; P.keepCenter = nw.group === 'herring' || nw.group === 'chevron'; }
}
function renderPatTab() {
  fixTargets();
  const keys = availTargets();
  $('#patTargets').innerHTML = keys.map(k => '<button class="chip" type="button" data-act="pat-target" data-key="' + k + '" aria-pressed="' + (k === UI.target) + '">' + esc(unitName(k)) + '</button>').join('');
  const kind = targetKind(UI.target), res = MODEL && MODEL.byKey[UI.target];
  $('#patTargetNote').textContent = kind === 'floor' ? (res && res.unit.roomIds.length > 1 ? 'Один рисунок на комнаты: ' + res.unit.roomIds.map(roomName).join(', ') + '. Он идёт через проёмы без сдвига.' : 'Рисунок комнаты.') : kind === 'border' ? 'Рамка вдоль стен: ряды идут параллельно каждой стене, в углах — рез на ус 45°.' : kind === 'ins' ? 'Вставка в центре комнаты со своим рисунком.' : 'Отдельный рисунок комнаты, не связан с соседними.';
  renderComposite(); renderPatList(); renderRefSelects(); syncPatternUI(); renderVariants(); syncPatInputs();
}
function renderComposite() {
  const r = curRoom(), box = $('#compBox'); if (!r) { box.innerHTML = ''; return; }
  $('#compRoom').textContent = r.name;
  const B = r.border, bm = B.mat || S.mat, G = MODEL && MODEL.geo[r.id];
  let h = '<div class="comp"><header><h4>Рамка вдоль стен</h4><button class="btn small' + (B.on ? ' primary' : '') + '" type="button" data-act="border-toggle" aria-pressed="' + B.on + '">' + (B.on ? 'Включена' : 'Включить') + '</button></header>';
  if (B.on) {
    h += '<div class="grid2"><label class="fld"><span>Рядов в рамке</span><span class="inp"><input id="bRows" data-bf="rows" data-num inputmode="numeric" value="' + (B.rows | 0) + '"><i>шт</i></span></label><div class="fld"><span>Ширина рамки</span><b style="font:600 15px var(--font-mono);padding:8px 0">' + (G && G.bw ? mm(G.bw) + ' мм' : '—') + '</b></div></div>' +
      '<div class="chips">' + BORDER_PATTERNS.map(id => '<button class="chip" type="button" data-act="border-type" data-v="' + id + '" aria-pressed="' + (B.pat.type === id) + '">' + esc(patDef(id).name) + '</button>').join('') + '</div>' +
      '<div class="tones" aria-label="Цвет рамки">' + Object.entries(TONES).map(([k, t]) => '<button class="tone" type="button" data-act="border-tone" data-tone="' + k + '" title="' + t.n + '" aria-label="Рамка: ' + t.n + '" aria-pressed="' + ((bm.tone || 'oak') === k) + '" style="background:' + rgb(t.c) + '"></button>').join('') + '</div>' +
      (G && G.borderErr ? '<p class="note bad">' + esc(G.borderErr) + '</p>' : '<p class="note">Планка рамки ' + mm(num(bm.L)) + '×' + mm(num(bm.W)) + ' мм. Другую планку для рамки выберите на шаге 2.</p>');
  } else h += '<p class="note">Например, центр квадратами, а по краям — палуба вразбежку. Рамка ложится вдоль всех стен комнаты.</p>';
  h += '</div><div class="comp"><header><h4>Вставки в центре</h4><button class="btn small" type="button" data-act="ins-add">' + ICON.plus + 'Добавить</button></header>';
  (r.inserts || []).forEach((ins, j) => {
    const key = 'ins:' + r.id + ':' + ins.id;
    h += '<div style="display:grid;gap:8px;padding-top:8px;border-top:1px dashed var(--line)"><div class="whead"><b>Вставка ' + (j + 1) + ' · ' + esc(patDef(ins.pat.type).name) + '</b><button class="btn small" type="button" data-act="ins-edit" data-key="' + key + '"' + (UI.target === key ? ' disabled' : '') + '>' + (UI.target === key ? 'Настраиваем' : 'Рисунок') + '</button><button class="icon" type="button" data-act="ins-del" data-ins="' + j + '" aria-label="Удалить вставку ' + (j + 1) + '">' + ICON.del + '</button></div>' +
      '<div class="grid2"><label class="fld"><span>Длина</span><span class="inp"><input id="i' + j + 'w" data-ins="' + j + '" data-f="w" data-num inputmode="decimal" value="' + mm(ins.w) + '"><i>мм</i></span></label><label class="fld"><span>Ширина</span><span class="inp"><input id="i' + j + 'h" data-ins="' + j + '" data-f="h" data-num inputmode="decimal" value="' + mm(ins.h) + '"><i>мм</i></span></label>' +
      '<label class="fld"><span>Сдвиг вдоль стены 1</span><span class="inp"><input id="i' + j + 'dx" data-ins="' + j + '" data-f="dx" data-num inputmode="decimal" value="' + mm(ins.dx) + '"><i>мм</i></span></label><label class="fld"><span>Сдвиг от стены 1</span><span class="inp"><input id="i' + j + 'dy" data-ins="' + j + '" data-f="dy" data-num inputmode="decimal" value="' + mm(ins.dy) + '"><i>мм</i></span></label></div>' +
      '<div class="seg mini" role="group" aria-label="Поворот вставки"><button type="button" data-act="ins-rot" data-ins="' + j + '" data-v="0" aria-pressed="' + (num(ins.rot) === 0) + '">Прямо</button><button type="button" data-act="ins-rot" data-ins="' + j + '" data-v="45" aria-pressed="' + (num(ins.rot) === 45) + '">Ромбом 45°</button></div></div>';
  });
  if (!(r.inserts || []).length) h += '<p class="note">Прямоугольник со своим рисунком: «ковёр» из квадратов или ёлочки посреди палубы.</p>';
  box.innerHTML = h + '</div>';
}
function renderPatList() {
  const el = $('#patList'), kind = targetKind(UI.target), list = kind === 'border' ? PATTERNS.filter(p => BORDER_PATTERNS.includes(p.id)) : PATTERNS, P = curP();
  el.innerHTML = list.map(p => '<button class="pat" type="button" data-act="pat" data-pat="' + p.id + '" aria-pressed="' + (p.id === P.type) + '"><canvas></canvas><b>' + esc(p.name) + '</b><span>' + esc(p.sub || '') + '</span></button>').join('');
  const M = E.unitMat(matForKey(UI.target), S);
  $$('.pat', el).forEach(b => drawPreview($('canvas', b), b.dataset.pat, M, P));
}
function drawPreview(c, pid, M, Pt) {
  const pd = patDef(pid), dpr = window.devicePixelRatio || 1, w = c.clientWidth || 100, h = c.clientHeight || 56;
  c.width = w * dpr; c.height = h * dpr; const ctx = c.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, w, h);
  let L = M.L, W = M.W, g = M.g; if (!(L >= 20 && W >= 20) || L < W) { L = 1200; W = 200; g = 0; }
  const span = pd.group === 'bond' ? 1.45 * L : pd.group === 'basket' ? 2.3 * L : 2.6 * L, s = Math.max(w / span, 4 / W), bw = w / s, bh = h / s;
  const box = [[0, 0], [bw, 0], [bw, bh], [0, bh]], bb = { u0: 0, v0: 0, u1: bw, v1: bh }, Mx = { L, W, g, kerf: 3 };
  let raw = [];
  try {
    if (pd.group === 'herring' && pd.n * (W + g) >= L + g) raw = [];
    else if (pd.id === 'remnant') raw = planRemnant([box], [], bb, Mx, { minPiece: Math.min(num(Pt.minPiece, 300), L * 0.3), minStag: Math.min(num(Pt.minStag, 300), L * 0.3) }).raw;
    else if (pd.id === 'random') raw = genBond(bb, L, W, g, randShifts(-2, Math.ceil(bh / W) + 2, L + g, L * 0.25, 3));
    else if (pd.group === 'bond') raw = genBond(bb, L, W, g, k => mod(k * pd.frac * (L + g), L + g));
    else if (pd.group === 'herring') raw = genHerring(bb, L, W, g, pd.n);
    else if (pd.group === 'chevron') raw = genChevron(bb, L, W, g, clamp(num(Pt.chevAngle, 45), 15, 75));
    else raw = genBasket(bb, L, W, g);
  } catch (e) { raw = []; }
  raw.forEach((p, i) => { const poly = clipBy(box, p.poly); if (poly.length < 3) return; ctx.beginPath(); poly.forEach((q, k) => k ? ctx.lineTo(q[0] * s, q[1] * s) : ctx.moveTo(q[0] * s, q[1] * s)); ctx.closePath(); ctx.fillStyle = rgb(woodRGB(M.tone, i, p.kind)); ctx.fill(); ctx.lineWidth = 0.7; ctx.strokeStyle = 'rgba(40,28,18,.55)'; ctx.stroke(); });
  if (!raw.length) { ctx.fillStyle = COL.muted; ctx.font = '500 11px ' + COL.body; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText('не подходит к размеру', w / 2, h / 2); }
}
function renderRefSelects() {
  const P = curP(), kind = targetKind(UI.target);
  const rr = kind === 'floor' ? S.rooms.filter(r => !r.own) : [room(UI.target.split(':')[1])].filter(Boolean);
  $('#refRoomFld').hidden = kind !== 'floor' || rr.length < 2;
  $('#refRoom').innerHTML = rr.map(r => '<option value="' + r.id + '"' + (r.id === P.refRoom ? ' selected' : '') + '>' + esc(r.name) + '</option>').join('');
  const refR = kind === 'floor' ? (rr.find(r => r.id === P.refRoom) || rr[0]) : rr[0];
  const g = refR ? roomGeom(refR) : null;
  $('#refWall').innerHTML = g ? g.corners.map((p, i) => '<option value="' + i + '"' + (i === (num(P.refWall) | 0) ? ' selected' : '') + '>Стена ' + (i + 1) + ' · ' + mm(dist(p, g.corners[(i + 1) % g.n])) + ' мм</option>').join('') : '';
}
function syncPatternUI() {
  const P = curP(), pd = patDef(P.type), grp = pd.group, kind = targetKind(UI.target);
  $$('#dirSeg button').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.v === P.dir)));
  $('#dirSec').hidden = kind === 'border';
  $('#refFlds').hidden = kind === 'ins';
  $('#customAngleFld').hidden = P.dir !== 'custom';
  $('#chevFld').hidden = grp !== 'chevron';
  $$('[data-show]').forEach(el => { const k = el.dataset.show; el.hidden = !(k === grp || k === pd.id); });
  $('#keepCenterFld').hidden = !(grp === 'herring' || grp === 'chevron') || kind === 'border';
  $('#offBFld').hidden = kind === 'border';
  $('#btnCenter').hidden = kind === 'border';
  $('#flipBtns').hidden = kind === 'border';
  const segTxt = grp === 'bond' || grp === 'basket' ? ['Вдоль', 'Поперёк', '45°', 'Свой угол'] : ['Ось вдоль', 'Ось поперёк', '45°', 'Свой угол'];
  $$('#dirSeg button').forEach((b, i) => { b.textContent = segTxt[i]; });
  $('#dirTitle').textContent = 'Направление · ' + (grp === 'herring' ? 'ось ёлочки' : grp === 'chevron' ? 'линия вершин' : grp === 'basket' ? 'квадраты' : 'доски');
  $('#dirNote').textContent = kind === 'ins' ? 'Направление считается от сторон вставки.' : grp === 'herring' ? 'Ось ёлочки параллельна опорной стене, планки идут к стенам под 45°. «45°» поворачивает ось — тогда планки параллельны стенам.' : grp === 'chevron' ? 'Вершины французской ёлочки идут по линии вдоль опорной стены. Обычно её ведут вдоль длинной стороны или по свету из окна.' : 'Доски кладут вдоль света из окна или вдоль длинной стены.';
  $('#btnFlipV').textContent = grp === 'bond' ? 'Первый ряд — у другой стены' : 'Отразить ⇅';
  $('#btnFlipU').textContent = grp === 'bond' ? 'Ряд начинать с другого конца' : 'Отразить ⇄';
  $('#offBLabel').textContent = kind === 'ins' ? 'Сдвиг поперёк' : grp === 'herring' ? 'Ось: сдвиг от стены' : grp === 'chevron' ? 'Вершины: сдвиг от стены' : 'Сдвиг от опорной стены';
  $('#offALabel').textContent = kind === 'border' ? 'Сдвиг стыков вдоль стен' : kind === 'ins' ? 'Сдвиг вдоль' : 'Сдвиг вдоль стены';
  const M = E.unitMat(matForKey(UI.target), S), pn = $('#patNote'); let note = '';
  if (grp === 'chevron' && M.shape !== 'chevron') note = 'Для французской ёлочки нужны планки со скошенными торцами (левые и правые). Прямоугольные придётся подрезать по торцам под ' + num(P.chevAngle, 45) + '°.';
  else if (grp !== 'chevron' && M.shape === 'chevron') note = 'Выбраны планки со скошенными торцами — они для французской ёлочки.';
  else if (grp === 'basket' && Math.abs(Math.round((M.L + M.g) / (M.W + M.g)) * (M.W + M.g) - (M.L + M.g)) > 1.5) note = 'Для квадратов длина должна делиться на ширину без остатка (280×70 = 4 планки). Сейчас ' + mm(M.L) + '/' + mm(M.W) + ' ≈ ' + f1(M.L / M.W) + ' — будут щели или нахлёст.';
  else if (grp === 'herring') note = 'Для ёлочки нужны левые (A) и правые (B) планки поровну.';
  pn.hidden = !note; pn.textContent = note; pn.className = 'note' + (note && !note.startsWith('Для ёлочки') ? ' warn' : '');
  $('#nudgeTarget').textContent = unitName(UI.target).toLowerCase();
  $$('.pad button').forEach(b => { const [, dy] = b.dataset.nudge.split(',').map(Number); b.disabled = kind === 'border' && dy !== 0; });
}
function clearVariants() { UI.variants = null; renderVariants(); }
function clearVariantMark() { if (UI.variants) { UI.variants.cur = -1; renderVariants(); } }
function renderVariants() {
  const el = $('#variants'); if (!el) return; const V = UI.variants;
  if (!V || V.key !== UI.target || !V.list.length) { el.innerHTML = ''; return; }
  el.innerHTML = '<p class="note">Лучшие положения. Нажмите, чтобы примерить на карте:</p>' + V.list.map((v, i) => '<button class="var" type="button" data-act="variant" data-i="' + i + '" aria-pressed="' + (V.cur === i) + '"><span class="vn">' + (i + 1) + '</span><span>' + (v.bad ? '<b style="color:var(--bad)">узких ' + v.bad + '</b>' : '<b>без узких</b>') + ' · мин. кусок ' + mm(v.minT) + ' мм · подрезок ' + v.cuts + '<br><small>сдвиг ' + (targetKind(V.key) === 'border' ? 'вдоль ' + mm(v.offA) : mm(v.offB) + ' / ' + mm(v.offA)) + ' мм</small></span></button>').join('');
}

/* сдвиг и центрирование */
function shiftP(F, P, du, dv) { const w = F.vecW([du, dv]); P.offA = Math.round(num(P.offA) + w[0] * F.e1[0] + w[1] * F.e1[1]); P.offB = Math.round(num(P.offB) + w[0] * F.e2[0] + w[1] * F.e2[1]); }
function balanceShift(a, b, P, sym) { const span = b - a, rem = mod(span, P); const w0 = rem < 1 || P - rem < 1 ? P : rem < P / 2 ? (rem + P) / 2 : sym ? rem / 2 : P; return mod(a + w0, P); }
function centerTarget(key, quiet) {
  const geo = MODEL ? MODEL.geo : computeGeo(S), u = buildUnit(key, S, geo); if (!u || u.kind === 'border') return;
  const P = u.P, M = u.mat, pd = patDef(P.type), F = u.parts[0].frame;
  const polys = (u.kind === 'ins' ? [u.ins.region] : [geo[u.refRoom].center]).map(p => p.map(F.toL)), b = bboxOf(polys.flat()), c = centroidMany(polys);
  let du = 0, dv = 0;
  if (pd.group === 'herring') { const per = Math.SQRT2 * (M.L + M.g), pu = Math.SQRT2 * pd.n * (M.W + M.g); dv = c[1] - Math.round(c[1] / per) * per; du = c[0] - Math.round(c[0] / pu) * pu; }
  else if (pd.group === 'chevron') { const Sv = (M.L + M.g) * Math.sin(clamp(num(P.chevAngle, 45), 15, 75) * DEG); dv = c[1] - Math.round(c[1] / Sv) * Sv; }
  else if (pd.group === 'basket') { const B = M.L + M.g; du = balanceShift(b.u0, b.u1, B, true); dv = balanceShift(b.v0, b.v1, B, true); }
  else { dv = balanceShift(b.v0, b.v1, M.W + M.g, pd.id === 'grid' || u.kind === 'ins'); if (pd.id === 'grid' || u.kind === 'ins') du = balanceShift(b.u0, b.u1, M.L + M.g, true); }
  shiftP(F, P, du, dv); syncPatInputs();
  if (!quiet) say(pd.group === 'herring' || pd.group === 'chevron' ? 'Ось поставлена по центру — подрезки у противоположных стен одинаковые.' : pd.group === 'bond' && pd.id !== 'grid' ? 'Первый ряд целый, если последний выходит не уже половины доски. Иначе крайние ряды поровну.' : 'Рисунок по центру: подрезки у противоположных стен одинаковые.', 'ok');
}
let optimizing = false;
async function optimize() {
  if (optimizing || !MODEL) return; const key = UI.target, geo = MODEL.geo;
  // кнопка «Подобрать» есть и в панели, и под картой
  const optBtns = (dis, txt) => $$('[data-act="optimize"]').forEach(b => { b.disabled = dis; if (txt) b.textContent = txt; });
  const u0 = buildUnit(key, S, geo); if (!u0) return;
  const base = computeUnit(u0, true); if (base.err) { say(base.err, 'bad'); return; }
  optimizing = true; optBtns(true);
  const P = u0.P, pd = patDef(P.type), M = u0.mat, F = u0.parts[0].frame, kind = u0.kind;
  const keep = !!P.keepCenter && (pd.group === 'herring' || pd.group === 'chevron') && kind !== 'border';
  let pu, pv;
  if (pd.group === 'bond') { pu = M.L + M.g; pv = M.W + M.g; }
  else if (pd.group === 'herring') { pu = Math.SQRT2 * pd.n * (M.W + M.g); pv = Math.SQRT2 * (M.L + M.g); }
  else if (pd.group === 'chevron') { const a = clamp(num(P.chevAngle, 45), 15, 75) * DEG; pu = (M.W + M.g) / Math.sin(a); pv = 2 * (M.L + M.g) * Math.sin(a); }
  else { pu = pv = 2 * (M.L + M.g); }
  const onlyV = pd.id === 'remnant' && kind !== 'border', onlyU = keep || kind === 'border';
  const N2 = clamp(Math.round(Math.sqrt(600000 / Math.max(50, base.pieces.length))), 12, 26);
  const Nu = onlyV ? 1 : onlyU ? 40 : N2, Nv = kind === 'border' ? 1 : onlyU ? 2 : onlyV ? 40 : N2;
  const A0 = num(P.offA), B0 = num(P.offB), seen = [];
  const at = (du, dv) => { if (kind === 'border') return [A0 + du, 0]; const w = F.vecW([du, dv]); return [A0 + w[0] * F.e1[0] + w[1] * F.e1[1], B0 + w[0] * F.e2[0] + w[1] * F.e2[1]]; };
  const evalAt = (du, dv) => { const o = at(du, dv); P.offA = o[0]; P.offB = o[1]; const r = computeUnit(buildUnit(key, S, geo), true); const v = { s: r.err ? Infinity : r.score, du, dv, bad: r.bad, minT: r.minT, cuts: r.cuts, offA: Math.round(o[0]), offB: Math.round(o[1]) }; seen.push(v); return v; };
  const starts = 6, levels = 3, total = Nu * Nv + starts * levels * 24; let cnt = 0;
  const tick = async () => { if (++cnt % 6 === 0) { optBtns(true, 'Подбираю… ' + Math.min(99, Math.round(cnt / total * 100)) + '%'); await new Promise(r => setTimeout(r, 0)); } };
  const coarse = [evalAt(0, 0)];
  for (let i = 0; i < Nu; i++) for (let j = 0; j < Nv; j++) { if (!i && !j) continue; coarse.push(evalAt(i / Nu * pu, j / Nv * pv)); await tick(); }
  coarse.sort((x, y) => x.s - y.s);
  for (const c0 of coarse.slice(0, starts)) {
    let cur = c0, hu = onlyV ? 0 : pu / Nu / 2, hv = onlyU ? 0 : pv / Nv / 2;
    for (let lv = 0; lv < levels; lv++) {
      let nb = cur;
      for (const i of hu ? [-2, -1, 0, 1, 2] : [0]) for (const j of hv ? [-2, -1, 0, 1, 2] : [0]) { if (!i && !j) continue; const v = evalAt(cur.du + i * hu / 2, cur.dv + j * hv / 2); if (v.s < nb.s - 1e-6) nb = v; await tick(); }
      cur = nb; hu /= 2; hv /= 2;
    }
  }
  // устойчивые варианты: проверяем после округления до миллиметра и берём разные по положению
  seen.sort((x, y) => x.s - y.s);
  const list = [], minSep = Math.min(pu, pv) * 0.12;
  for (const v of seen) {
    if (list.length >= 5) break;
    if (list.some(x => Math.hypot(x.offA - v.offA, x.offB - v.offB) < minSep)) continue;
    P.offA = v.offA; P.offB = v.offB; const r = computeUnit(buildUnit(key, S, geo), true); if (r.err) continue;
    list.push({ offA: v.offA, offB: v.offB, s: r.score, bad: r.bad, minT: r.minT, cuts: r.cuts });
  }
  list.sort((x, y) => x.s - y.s);
  const best = list[0] || { offA: A0, offB: B0 };
  P.offA = best.offA; P.offB = best.offB;
  UI.variants = { key, list, cur: 0 };
  optBtns(false); optimizing = false; $('#btnOptimize').textContent = 'Подобрать варианты'; renderCtxbar();
  syncPatInputs(); renderVariants(); recompute(); invalidate({ fast: true });
  const st = MODEL.byKey[key] && MODEL.byKey[key].stats;
  if (st && st.nBad) say('Вариант 1 применён: узких подрезок ' + st.nBad + '.' + (keep ? ' Снимите галочку «Только симметричные варианты» — без неё вариантов больше.' : ' Можно уменьшить порог в «Правилах» или сменить направление.'), 'bad');
  else say('Вариант 1 применён: узких подрезок нет, самый маленький кусок ' + (st ? mm(st.minT) : '—') + ' мм. Ниже — другие варианты.', 'ok');
}
/* стрелки под картой */
$('#nudge').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b || b.disabled) return;
  if ('stepCycle' in b.dataset) { UI.step = UI.step === 1 ? 10 : UI.step === 10 ? 50 : 1; syncStep(); saveUI(); return; }
  if (!b.dataset.nudge || !MODEL) return;
  const res = MODEL.byKey[UI.target]; if (!res || res.err) return;
  const [sx, sy] = b.dataset.nudge.split(',').map(Number), F = res.unit.parts[0].frame, P = curP(), d = UI.step;
  if (res.unit.kind === 'border') P.offA = Math.round(num(P.offA) + sx * d);
  else { const wx = sx * d, wy = sy * d; P.offA = Math.round(num(P.offA) + wx * F.e1[0] + wy * F.e1[1]); P.offB = Math.round(num(P.offB) + wx * F.e2[0] + wy * F.e2[1]); }
  syncPatInputs(); clearVariantMark(); invalidate();
});
function syncStep() { $('#stepBtn').textContent = 'шаг ' + UI.step + ' мм'; }

/* ================= 4. Расчёт ================= */
const wallRef = (rid, i, multi) => 'стены ' + (i + 1) + (multi ? ' (' + roomName(rid) + ')' : '');
function unitSteps(res) {
  const u = res.unit, st = res.stats, M = u.mat, pd = patDef(u.P.type), gap = num(S.set.gap), steps = [], multi = u.roomIds.length > 1 || S.rooms.length > 1;
  const gtxt = gl => { const p = []; if (gl.lo) p.push('<b>' + mm(gl.lo.dist) + ' мм</b> от ' + wallRef(gl.room, gl.lo.wall, multi)); if (gl.hi) p.push('<b>' + mm(gl.hi.dist) + ' мм</b> от ' + wallRef(gl.room, gl.hi.wall, multi)); return p.join(' и '); };
  if (u.kind === 'border') {
    const G = MODEL.geo[u.roomIds[0]];
    steps.push('Рамка: <b>' + (u.P && room(u.roomIds[0]).border.rows) + ' ' + plural(room(u.roomIds[0]).border.rows | 0, 'ряд', 'ряда', 'рядов') + '</b> по ' + mm(M.W) + ' мм вдоль всех стен, общая ширина <b>' + mm(G.bw) + ' мм</b>. В углах планки режутся на ус (45°).');
    steps.push('Отбейте линию рамки: <b>' + mm(G.bw + gap) + ' мм</b> от стен (' + mm(gap) + ' мм зазор + рамка). Обычно центр кладут с запасом, по этой линии подрезают его и затем кладут рамку.');
    steps.push('Рисунок рамки: «' + pd.name + '». Ряды идут от стены к центру.');
  } else if (u.kind === 'ins') {
    const ins = u.ins, g = MODEL.geo[u.refRoom].g, d1 = lineDist(ins.C, g, 0), d2w = perpWall(g, 0), d2 = d2w >= 0 ? lineDist(ins.C, g, d2w) : null;
    steps.push('Вставка ' + mm(num(ins.ins.w)) + '×' + mm(num(ins.ins.h)) + ' мм' + (num(ins.ins.rot) ? ', повёрнута на ' + num(ins.ins.rot) + '°' : '') + '. Центр — в <b>' + mm(d1) + ' мм</b> от стены 1' + (d2 !== null ? ' и <b>' + mm(d2) + ' мм</b> от стены ' + (d2w + 1) : '') + '.');
    steps.push('Отбейте контур вставки, уложите её первой, затем основной рисунок вокруг с подрезкой по контуру.');
  } else {
    if (gap > 0) steps.push('Поставьте клинья: зазор <b>' + mm(gap) + ' мм</b> от стен (его закроет плинтус).');
    if (u.kind === 'floor' && u.roomIds.length > 1) steps.push('Рисунок общий для комнат: ' + u.roomIds.map(roomName).join(', ') + '. Через проёмы ведите его без сдвига, порог не нужен.');
  }
  if (pd.group === 'bond' && res.rows && res.rows.length && u.kind !== 'border') {
    const rows = res.rows, first = rows[0], last = rows[rows.length - 1], thr = num(u.P.minEdge, 50);
    steps.push('Всего <b>' + rows.length + ' ' + plural(rows.length, 'ряд', 'ряда', 'рядов') + '</b>. Начало — угол с отметкой «СТАРТ» на плане.');
    steps.push('Первый ряд: ширина <b>' + mm(first.width) + ' мм</b>' + (first.width < M.W - 0.5 ? ' — распустите доски вдоль, отпилите ' + mm(M.W - first.width) + ' мм (со стороны стены обычно срезают гребень).' : ' — доски целые по ширине.'));
    if (rows.length > 1) steps.push('Последний ряд: ширина <b>' + mm(last.width) + ' мм</b>' + (last.width < thr ? '. <b style="color:var(--bad)">Это узко</b> — нажмите «По центру» или «Подобрать варианты» на шаге 3.' : '.'));
    if (pd.id === 'remnant') steps.push('Каждый следующий ряд начинайте обрезком от конца предыдущего — длины кусков по рядам ниже. Стыки соседних рядов не ближе <b>' + mm(num(u.P.minStag)) + ' мм</b>, куски не короче <b>' + mm(num(u.P.minPiece)) + ' мм</b>.');
    else if (pd.frac > 0) steps.push('Смещение стыков в соседних рядах: <b>' + mm(pd.frac * (M.L + M.g)) + ' мм</b>.');
    else if (pd.id === 'random') steps.push('Разбег стыков случайный, но не меньше <b>' + mm(num(u.P.minStag)) + ' мм</b>.');
    for (const gl of res.guides || []) if (gl.lo || gl.hi) steps.push((pd.id === 'grid' ? 'Разметочная линия по шву: ' : 'Для клеевой укладки отбейте линию по ' + gl.name + ': ') + gtxt(gl) + '.');
  } else if (pd.group === 'herring' && u.kind !== 'border') {
    const gl = res.guides[0], Wc = pd.n * (M.W + M.g), Lc = M.L + M.g;
    steps.push('Отбейте шнуром ось ёлочки (синий пунктир): ' + (gl && (gl.lo || gl.hi) ? gtxt(gl) : 'по центру') + '. Расстояния — до самой стены.');
    steps.push('Начинайте от оси: первая «ёлка» по линии, дальше в обе стороны. Шаг вдоль оси — <b>' + mm(Math.SQRT2 * Wc) + ' мм</b> на пару ' + (pd.n > 1 ? 'блоков' : 'планок') + ', соседние ёлки — через <b>' + mm(Math.SQRT2 * Lc) + ' мм</b>.');
    steps.push('Нужны левые и правые планки: A — <b>' + st.nA + '</b>, B — <b>' + st.nB + '</b> шт (с подрезками).');
  } else if (pd.group === 'chevron' && u.kind !== 'border') {
    const gl = res.guides[0], a = clamp(num(u.P.chevAngle, 45), 15, 75) * DEG;
    steps.push('Отбейте линию вершин (синий пунктир): ' + (gl && (gl.lo || gl.hi) ? gtxt(gl) : 'по центру') + '. По ней сходятся торцы планок.');
    steps.push('Вершины вдоль линии — через <b>' + mm((M.W + M.g) / Math.sin(a)) + ' мм</b>, следующие линии вершин — через <b>' + mm((M.L + M.g) * Math.sin(a)) + ' мм</b>.');
    steps.push('Планки A — <b>' + st.nA + '</b>, B — <b>' + st.nB + '</b> шт (с подрезками).');
  } else if (pd.group === 'basket') {
    for (const gl of res.guides || []) if (gl.lo || gl.hi) steps.push('Разметочная линия по краю квадратов: ' + gtxt(gl) + '.');
    const n = Math.max(1, Math.round((M.L + M.g) / (M.W + M.g)));
    steps.push('Квадрат — ' + n + ' ' + plural(n, 'планка', 'планки', 'планок') + ' по ' + mm(M.L) + ' мм, соседние квадраты повёрнуты на 90°.');
  }
  const worst = (res.walls || []).filter(w => w.count && w.minT < num(u.P.minEdge, 25));
  if (worst.length) steps.push('<b style="color:var(--bad)">Узкие подрезки</b> у ' + worst.map(w => (w.label === 'стена' ? 'стены ' : 'рамки у стены ') + (w.i + 1) + (multi ? ' (' + roomName(w.rid) + ')' : '')).join(', ') + '. Сдвиньте рисунок или нажмите «Подобрать варианты».');
  else if (st.nCut) steps.push('Узких подрезок нет: самый маленький кусок ' + mm(st.minT) + ' мм.');
  return steps;
}
function lineDist(p, g, i) { const a = g.corners[i], b = g.corners[(i + 1) % g.n], dx = b[0] - a[0], dy = b[1] - a[1], l = Math.hypot(dx, dy) || 1; return Math.abs((p[0] - a[0]) * dy - (p[1] - a[1]) * dx) / l; }
function perpWall(g, i) { const d0 = unitV(g.corners[i], g.corners[(i + 1) % g.n]); for (let k = 1; k < g.n; k++) { const j = (i + k) % g.n; if (Math.abs(g.arcs[j]) >= 0.5) continue; const d = unitV(g.corners[j], g.corners[(j + 1) % g.n]); if (Math.abs(d0[0] * d[0] + d0[1] * d[1]) < 0.02) return j; } return -1; }
function renderResults() {
  const el = $('#results'); if (!MODEL) return;
  const errs = S.rooms.filter(r => MODEL.geo[r.id].err), reserve = Math.max(0, num(S.set.reserve));
  let roomsA = 0, layA = 0; for (const r of S.rooms) { const G = MODEL.geo[r.id]; if (G.err) continue; roomsA += Math.abs(area(G.g.poly)); layA += Math.abs(area(G.lay)); }
  let h = '<div class="sec"><h3>Итог по этажу <small>' + S.rooms.length + ' ' + plural(S.rooms.length, 'комната', 'комнаты', 'комнат') + '</small></h3>' +
    (errs.length ? '<p class="note bad">Не построены: ' + errs.map(r => esc(r.name) + ' — ' + esc(MODEL.geo[r.id].err)).join('; ') + '</p>' : '') +
    '<div class="tiles"><div class="tile"><b>' + fm2(roomsA) + ' м²</b><span>площадь комнат</span></div><div class="tile"><b>' + fm2(layA) + ' м²</b><span>под укладку, без зазора</span></div></div></div>';
  h += '<div class="sec"><h3>Сколько покупать</h3><div class="tblwrap"><table class="tbl"><thead><tr><th>Покрытие</th><th>По плану</th><th>С запасом ' + f1(reserve) + '%</th></tr></thead><tbody>';
  for (const m of MODEL.mats) {
    const M = m.M, br = Math.ceil(m.boards * (1 + reserve / 100)), isMain = M.key === E.unitMat(S.mat, S).key;
    let packs = '';
    if (isMain && num(S.set.perPack) > 0) packs = ' · ' + Math.ceil(br / num(S.set.perPack)) + ' уп.';
    else if (isMain && num(S.set.packM2) > 0) packs = ' · ' + Math.ceil(br * M.L * M.W / 1e6 / num(S.set.packM2) - 1e-9) + ' уп.';
    h += '<tr><td>' + esc(catById(M.cat).name) + ' ' + mm(M.L) + '×' + mm(M.W) + '<br><small class="hint">' + esc(m.names.join(', ')) + '</small></td><td class="n">' + m.boards + ' шт<br><small class="hint">' + fm2(m.boards * M.L * M.W) + ' м²</small></td><td class="n"><b>' + br + ' шт</b>' + packs + '<br><small class="hint">' + fm2(br * M.L * M.W) + ' м²</small></td></tr>';
  }
  h += '</tbody></table></div><p class="note">Обрезки длиннее нужного куска засчитаны повторно, в «палубе по остаткам» — по рядам.' + (num(S.set.perPack) || num(S.set.packM2) ? '' : ' Впишите, сколько штук или м² в пачке (шаг 2), — посчитаем упаковки.') + '</p></div>';
  const keys = MODEL.units.map(r => r.unit.key);
  const res = MODEL.byKey[UI.target] || MODEL.units[0];
  h += '<div class="sec"><h3>Как укладывать</h3>' + (keys.length > 1 ? '<div class="chips">' + keys.map(k => '<button class="chip" type="button" data-act="res-target" data-key="' + k + '" aria-pressed="' + (res && k === res.unit.key) + '">' + esc(unitName(k)) + '</button>').join('') + '</div>' : '');
  if (!res) { el.innerHTML = h + '<p class="note">Нет участков для укладки.</p></div>'; return; }
  if (res.err) { el.innerHTML = h + '<p class="note bad">' + esc(res.err) + '</p></div>'; return; }
  const st = res.stats;
  h += '<div class="tiles"><div class="tile"><b>' + st.nFull + '</b><span>целых</span></div><div class="tile"><b>' + st.nCut + '</b><span>подрезок' + (st.nBad ? ', узких ' + st.nBad : '') + '</span></div></div>';
  h += '<ol class="steps">' + unitSteps(res).map(s => '<li><span>' + s + '</span></li>').join('') + '</ol></div>';
  if (res.walls && res.walls.length) {
    const thr = num(res.unit.P.minEdge, 25), multi = S.rooms.length > 1;
    h += '<div class="sec"><h3>Что приходит к стенам</h3><div class="tblwrap"><table class="tbl"><thead><tr><th>Стена</th><th>Подрезок</th><th>Глубина куска</th><th>Самый узкий</th></tr></thead><tbody>';
    for (const w of res.walls) {
      const name = (w.label === 'стена' ? '' : 'рамка ') + (w.i + 1) + (multi ? ' ' + roomName(w.rid) : '') + ' · ' + (w.arc ? '⌒' : '') + mm(w.len);
      const js = (MODEL.adj || []).filter(a => a.a === w.rid && a.i === w.i), jt = js.length ? '<br><small class="hint">' + esc(jointSegs(w.len, js).map(sg => mm(sg.len) + (sg.to ? ' общая с «' + roomName(sg.to) + '»' : '')).join(' + ')) + '</small>' : '';
      if (!w.count) { h += '<tr><td class="n">' + esc(name) + jt + '</td><td class="n">0</td><td colspan="2">целые планки</td></tr>'; continue; }
      const bad = w.minT < thr;
      h += '<tr class="' + (bad ? 'bad' : '') + '"><td class="n">' + esc(name) + jt + '</td><td class="n">' + w.count + '</td><td class="n">' + (Math.abs(w.maxD - w.minD) < 1 ? mm(w.minD) : mm(w.minD) + '–' + mm(w.maxD)) + ' мм</td><td class="n">' + mm(w.minT) + ' мм' + (bad ? ' ⚠' : '') + '</td></tr>';
    }
    h += '</tbody></table></div><p class="note">Глубина — насколько кусок заходит от края укладки. «Самый узкий» — ширина самого тонкого куска у этой стены.</p></div>';
  }
  if (res.rows && res.rows.length) {
    const M = res.unit.mat;
    h += '<div class="sec"><h3>Ряды <small>от старта, мм</small></h3><div class="rows">';
    res.rows.forEach((row, ri) => {
      const chips = []; let run = 0; const flush = () => { if (run) { chips.push('<span class="pc">' + mm(M.L) + (run > 1 ? ' × ' + run : '') + '</span>'); run = 0; } };
      row.items.forEach(it => { if (it.full) { run++; return; } flush(); chips.push('<span class="pc ' + (it.bad ? 'bad' : 'cut') + '">' + mm(it.len) + (it.src === 'pool' ? '<sup>обр.</sup>' : '') + '</span>'); });
      flush();
      const cutW = row.width < M.W - 0.5;
      h += '<div class="rowl"><div class="rh">Ряд ' + (ri + 1) + '<small class="' + (cutW ? 'cutw' : '') + '">' + (cutW ? 'шир. ' + mm(row.width) : 'целый') + '</small></div><div class="pcs">' + chips.join('') + '</div></div>';
    });
    h += '</div><p class="note"><span class="pc cut">742</span> — подрезанный кусок, <sup>обр.</sup> — из обрезка прошлых рядов.</p></div>';
  }
  if (res.groups.length && (!res.rows || patDef(res.unit.P.type).group !== 'bond')) {
    const list = res.groups.slice(0, 40), key = res.unit.key;
    h += '<div class="sec"><h3>Подрезки <small>одинаковые можно напилить пачкой</small></h3><div class="groups">' +
      list.map(g => '<button class="grp" type="button" data-act="grp" data-key="' + key + '" data-gk="' + esc(g.key) + '" aria-pressed="' + (!!UI.hl && UI.hl.key === key && UI.hl.gk === g.key) + '"><span class="cnt">×' + g.idx.length + '</span><span class="tx">' + (g.kind === 'A' || g.kind === 'B' ? '<small>планка ' + g.kind + '</small>' : '') + g.lines.map(esc).join('<br>') + '</span></button>').join('') + '</div>' +
      (res.groups.length > list.length ? '<p class="note">Ещё ' + (res.groups.length - list.length) + ' разных подрезок — смотрите на карте.</p>' : '') + '<p class="note">Нажмите на строку — такие куски подсветятся на плане.</p></div>';
  }
  h += '<div class="sec"><h3>Обозначения</h3><div class="legend"><span><i style="background:' + rgb((TONES[res.unit.mat.tone] || TONES.oak).c) + '"></i>целая</span><span><i style="background:' + COL.tape + '"></i>подрезка</span><span><i style="background:' + COL.badSoft + ';border-color:' + COL.bad + '"></i>узкая подрезка</span><span><i style="background:' + COL.chalk + ';height:3px"></i>линия разметки</span><span><i style="background:' + COL.gap + '"></i>зазор у стен</span></div></div>';
  h += '<div class="sec"><h3>Сохранить и отправить</h3><button class="btn primary next" type="button" data-act="export-img"><span>Фото проекта — план и расчёт</span>' + ICON.img + '</button><div class="row-btns"><button class="btn" type="button" data-act="export-share">' + ICON.share + (PF.inTG ? 'Отправить в чат' : 'Отправить текстом') + '</button><button class="btn" type="button" data-act="export-copy">Скопировать текст</button>' +
    (PF.inTG ? '' : '<a class="btn" id="tgShare" href="' + esc(tgShareLink()) + '" target="_blank" rel="noopener">В Telegram</a>') + '</div>' +
    '<p class="note">Фото — одна картинка: план с подрезками, сколько покупать, комнаты и как укладывать.' + (isPhone() ? ' Откроется в окне: нажмите «' + (PF.ios ? 'Сохранить в Фото' : 'Сохранить') + '» или удерживайте картинку пальцем.' : '') + ' Перенести сам проект на другой телефон — «Проекты» → «Копия для переноса».</p></div>';
  el.innerHTML = h;
}
/* расчёт по частям: тот же текст идёт и в сообщение, и на фото проекта */
function reportParts() {
  const strip = x => x.replace(/<[^>]+>/g, ''), reserve = Math.max(0, num(S.set.reserve)), rooms = [], buy = [], units = [];
  for (const r of S.rooms) {
    const G = MODEL.geo[r.id]; if (G.err) { rooms.push({ title: r.name, lines: [G.err] }); continue; }
    const wl = G.g.corners.map((p, i) => { const c = dist(p, G.g.corners[(i + 1) % G.g.n]), js = (MODEL.adj || []).filter(a => a.a === r.id && a.i === i); return (i + 1) + ') ' + (Math.abs(G.g.arcs[i]) >= 0.5 ? 'дуга ' : '') + mm(c) + (js.length ? ' (' + jointSegs(c, js).map(sg => mm(sg.len) + (sg.to ? ' общая с «' + roomName(sg.to) + '»' : '')).join(' + ') + ')' : ''); });
    const lines = ['стены ' + wl.join(', ') + ' мм'];
    if ((r.doors || []).length) lines.push('проёмы: ' + r.doors.map(d => 'ст. ' + ((d.wall | 0) + 1) + ' — ' + mm(d.width) + ' мм от угла ' + mm(d.pos) + (d.to && room(d.to) ? ' в «' + roomName(d.to) + '»' : '')).join('; '));
    if ((r.niches || []).length) lines.push('ниши и выступы: ' + r.niches.map(x => (x.kind === 'box' ? 'выступ ' : 'ниша ') + mm(x.width) + '×' + mm(x.depth) + ' на ст. ' + ((x.wall | 0) + 1) + ' от угла ' + mm(x.pos) + (x.kind !== 'box' && x.floor === false ? ', без пола' : '')).join('; '));
    rooms.push({ title: r.name + ': ' + fm2(Math.abs(area(G.g.poly))) + ' м²', lines });
  }
  for (const m of MODEL.mats) {
    const M = m.M, br = Math.ceil(m.boards * (1 + reserve / 100)), isMain = M.key === E.unitMat(S.mat, S).key;
    let packs = ''; if (isMain && num(S.set.perPack) > 0) packs = ', ' + Math.ceil(br / num(S.set.perPack)) + ' уп.'; else if (isMain && num(S.set.packM2) > 0) packs = ', ' + Math.ceil(br * M.L * M.W / 1e6 / num(S.set.packM2) - 1e-9) + ' уп.';
    buy.push(catById(M.cat).name + ' ' + mm(M.L) + '×' + mm(M.W) + ': ' + m.boards + ' шт, с запасом ' + f1(reserve) + '% — ' + br + ' шт (' + fm2(br * M.L * M.W) + ' м²)' + packs);
  }
  for (const res of MODEL.units) {
    const u = { title: res.unit.name + ' — ' + patDef(res.unit.P.type).name + ' ' + mm(res.unit.mat.L) + '×' + mm(res.unit.mat.W), steps: [], rows: [], groups: [], err: res.err || null };
    if (!res.err) {
      u.steps = unitSteps(res).map(strip);
      if (res.rows) u.rows = res.rows.map((row, i) => 'Ряд ' + (i + 1) + (row.width < res.unit.mat.W - 0.5 ? ' (шир. ' + mm(row.width) + ')' : '') + ': ' + row.items.map(it => (it.full ? '' : '✂') + mm(it.len)).join(' | '));
      else u.groups = res.groups.map(g => '×' + g.idx.length + (g.kind !== 'R' ? ' [' + g.kind + ']' : '') + ' ' + g.lines.join('; '));
    }
    units.push(u);
  }
  return { rooms, buy, units, reserve };
}
function reportText() {
  if (!MODEL) return '';
  const R = reportParts(), lines = [S.name || 'Раскладка'];
  for (const r of R.rooms) { lines.push(r.title + (r.lines.length ? ', ' + r.lines[0] : '')); for (const l of r.lines.slice(1)) lines.push('  ' + l); }
  lines.push('', 'Покупать:'); for (const b of R.buy) lines.push('— ' + b);
  for (const u of R.units) {
    lines.push('', '== ' + u.title + ' ==');
    if (u.err) { lines.push(u.err); continue; }
    u.steps.forEach((x, i) => lines.push((i + 1) + '. ' + x));
    lines.push(...(u.rows.length ? u.rows : u.groups));
  }
  return lines.join('\n');
}
async function copyReport() {
  const t = reportText();
  try { await navigator.clipboard.writeText(t); say('Расчёт скопирован — вставьте в мессенджер или заметки.', 'ok'); }
  catch (e) { openModal('<header><h2>Расчёт</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header><p class="note">Выделите текст и скопируйте.</p><textarea class="code" id="copyArea" readonly>' + esc(t) + '</textarea>'); const ta = $('#copyArea'); ta.focus(); ta.select(); }
}

/* ================= экспорт ================= */
const fileSafe = s => (String(s || 'raskladka').replace(/[\\/:*?"<>|]+/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 60) || 'raskladka');
/* телефон, ярлык на экране или Telegram: файл не «скачивается», а уходит в системное меню «Поделиться» */
function isPhone() { let coarse = false; try { coarse = window.matchMedia('(pointer:coarse)').matches && navigator.maxTouchPoints > 0; } catch (e) { coarse = false; } return PF.ios || PF.android || PF.inTG || PF.standalone || coarse; }
function canShareFiles(files) { try { return !!(navigator.share && navigator.canShare && navigator.canShare({ files })); } catch (e) { return false; } }
async function saveFile(name, data, mime) {
  const dl = await capUse('downloads');
  if (dl) { try { await dl.save({ filename: name, data }); return 'saved'; } catch (e) { if (e && e.code === 'declined') return 'declined'; } }
  if (isPhone()) return 'sheet';
  let top = false; try { top = window.top === window.self; } catch (e) { top = false; }
  if (top && !window.claude) {
    try { const blob = data instanceof Blob ? data : new Blob([data], { type: mime }); const url = URL.createObjectURL(blob); const a = document.createElement('a'); a.href = url; a.download = name; document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(url), 5000); return 'saved'; } catch (e) { /* ниже — окно */ }
  }
  return 'fallback';
}
/* окно с файлом: кнопка «Поделиться» вызывает меню системы прямо по нажатию — так iPhone разрешает сохранить в Фото и Файлы */
let SHARE = null, SHARE_URL = null;
function openShareSheet(title, files, bodyHtml, note) {
  SHARE = files && canShareFiles(files) ? files : null;
  const img = files && files[0] && /^image\//.test(files[0].type);
  openModal('<header><h2>' + esc(title) + '</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header>' +
    (SHARE ? '<button class="btn primary next" data-share-file type="button"><span>' + (img ? (PF.ios ? 'Сохранить в Фото или отправить' : 'Сохранить или отправить') : (PF.ios ? 'Сохранить в Файлы или отправить' : 'Сохранить или отправить')) + '</span>' + ICON.share + '</button>' : '') +
    '<p class="note">' + note + '</p>' + bodyHtml, 'share');
}
function shareNow() {
  if (!SHARE) return;
  // картинку отдаём без подписи: с текстом iPhone может спрятать «Сохранить изображение»
  const img = /^image\//.test(SHARE[0].type);
  navigator.share(img ? { files: SHARE } : { files: SHARE, title: S.name || 'Раскладка' }).then(() => { closeModal(); say('Готово.', 'ok'); PF.haptic('ok'); })
    .catch(err => { if (err && err.name === 'AbortError') return; say(PF.ios ? 'Меню «Поделиться» не открылось. Нажмите и удерживайте картинку → «Сохранить в Фото».' : 'Не получилось поделиться. Нажмите и удерживайте картинку, чтобы сохранить.', 'bad'); });
}
/* фото проекта: шапка, план с подрезками, под ним — сколько покупать, комнаты и как укладывать */
function wrapText(ctx, text, maxW) {
  const out = []; let cur = '';
  for (const w of String(text).split(' ')) { const t = cur ? cur + ' ' + w : w; if (cur && ctx.measureText(t).width > maxW) { out.push(cur); cur = w; } else cur = t; }
  if (cur) out.push(cur); return out;
}
function planCanvas() {
  const b = floorBBox(); if (!b) return null;
  const K = 2, W = 1000, head = 92, pad = 56, x0 = 28, tw = W - 2 * x0, s = (W - 2 * pad) / Math.max(1, b.u1 - b.u0), planH = Math.round(2 * pad + (b.v1 - b.v0) * s);
  // текст под планом: раскладываем по строкам заранее, чтобы знать высоту картинки
  const R = reportParts(), items = [], meas = document.createElement('canvas').getContext('2d');
  const F = { h: '700 17px ' + COL.body, b: '600 13.5px ' + COL.body, t: '400 13.5px ' + COL.body, s: '400 12px ' + COL.body };
  const add = (font, text, indent, color, gap) => { meas.font = F[font]; wrapText(meas, text, tw - (indent || 0)).forEach((l, i) => items.push({ font, text: l, x: x0 + (indent || 0), color: color || 'ink', gap: i === 0 ? (gap || 0) : 0 })); };
  add('h', 'Сколько покупать', 0, 'ink', 6); for (const l of R.buy) add('t', '— ' + l, 0);
  add('h', 'Комнаты', 0, 'ink', 14); for (const r of R.rooms) { add('b', r.title, 0, 'ink', 4); for (const l of r.lines) add('t', l, 14, 'muted'); }
  for (const u of R.units) {
    add('h', 'Как укладывать: ' + u.title, 0, 'ink', 14);
    if (u.err) { add('t', u.err, 0, 'bad'); continue; }
    u.steps.forEach((x, i) => add('t', (i + 1) + '. ' + x, 0, 'ink', 2));
  }
  add('s', 'Жёлтым — подрезки, красным — узкие куски, синим — линия разметки. Размеры в мм. Ряды и подрезки по стенам — в приложении «Раскладка».', 0, 'muted', 14);
  const LH = { h: 26, b: 21, t: 20, s: 18 }, textH = items.reduce((t, it) => t + LH[it.font] + it.gap, 0) + 34;
  const H = head + planH + textH;
  const c = document.createElement('canvas'); c.width = W * K; c.height = H * K; const ctx = c.getContext('2d');
  render(ctx, W, head + planH, { s, cx: (b.u0 + b.u1) / 2, cy: (b.v0 + b.v1) / 2 - head / 2 / s }, { k: K, style: UI.style, labels: true, live: false });
  ctx.setTransform(K, 0, 0, K, 0, 0); ctx.fillStyle = COL.panel; ctx.fillRect(0, 0, W, head - 16);
  ctx.fillStyle = COL.ink; ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic'; ctx.font = '700 20px ' + COL.body; ctx.fillText(S.name || 'Раскладка', 24, 32);
  ctx.font = '500 13px ' + COL.body; ctx.fillStyle = COL.muted;
  ctx.fillText(MODEL.units.filter(r => !r.err).map(r => r.unit.name + ' — ' + patDef(r.unit.P.type).name + ' ' + mm(r.unit.mat.L) + '×' + mm(r.unit.mat.W)).join(' · ').slice(0, 150), 24, 54);
  ctx.fillText(MODEL.mats.map(m => mm(m.M.L) + '×' + mm(m.M.W) + ': ' + m.boards + ' шт').join(' · ') + ' · зазор ' + mm(num(S.set.gap)) + ' мм · ' + new Date().toLocaleDateString('ru-RU'), 24, 72);
  ctx.fillStyle = COL.panel; ctx.fillRect(0, head + planH, W, textH);
  ctx.strokeStyle = COL.line || COL.grid; ctx.lineWidth = 1; ctx.beginPath(); ctx.moveTo(0, head + planH + 0.5); ctx.lineTo(W, head + planH + 0.5); ctx.stroke();
  let y = head + planH + 14;
  for (const it of items) { y += it.gap + LH[it.font]; ctx.font = F[it.font]; ctx.fillStyle = it.color === 'muted' ? COL.muted : it.color === 'bad' ? COL.bad : COL.ink; ctx.fillText(it.text, it.x, y - 6); }
  return c;
}
async function exportImage() {
  if (!MODEL) return; const c = planCanvas(); if (!c) return;
  const blob = await new Promise(res => c.toBlob(res, 'image/png')), name = fileSafe(S.name) + '.png';
  const r = blob ? await saveFile(name, blob, 'image/png') : 'fallback';
  if (r === 'saved') { say('Фото проекта сохранено.', 'ok'); return; } if (r === 'declined') return;
  if (SHARE_URL) { try { URL.revokeObjectURL(SHARE_URL); } catch (e) { /* уже нет */ } }
  SHARE_URL = blob ? URL.createObjectURL(blob) : c.toDataURL('image/png');
  const files = blob ? [new File([blob], name, { type: 'image/png' })] : null;
  openShareSheet('Фото проекта', files, '<img alt="Фото проекта: план и расчёт" src="' + SHARE_URL + '">',
    PF.ios ? 'Если кнопки нет или она не сработала: нажмите и удерживайте картинку → <b>«Сохранить в Фото»</b>.' : PF.android ? 'Или нажмите и удерживайте картинку → «Скачать изображение».' : 'Нажмите и удерживайте картинку (на компьютере — правая кнопка мыши), чтобы сохранить или отправить.');
}
function projData() { return { app: 'raskladka', v: 2, name: S.name, mat: S.mat, set: S.set, rooms: S.rooms, floorPat: S.floorPat, noDoor: S.noDoor || [] }; }
async function exportProject() {
  const json = JSON.stringify(projData(), null, 1), name = fileSafe(S.name) + '.json', r = await saveFile(name, json, 'application/json');
  if (r === 'saved') { say('Копия проекта (.json) сохранена. Открыть: «Проекты» → «Открыть копию».', 'ok'); return; } if (r === 'declined') return;
  let files = [new File([json], name, { type: 'application/json' })];
  if (!canShareFiles(files)) files = [new File([json], fileSafe(S.name) + '.txt', { type: 'text/plain' })];
  openShareSheet('Копия для переноса (.json)', files, '<textarea class="code" id="copyArea" readonly>' + esc(json) + '</textarea>', 'Это не картинка, а сам проект — чтобы открыть его на другом телефоне или компьютере: «Проекты» → «Открыть копию». Фото проекта — кнопка с камерой вверху. Можно и скопировать текст ниже, а потом «Вставить текст».');
}
/* текст расчёта: на телефоне — меню «Поделиться» (мессенджеры, заметки), в Telegram — выбор чата */
function shareReport() {
  const text = reportText();
  if (PF.inTG) { try { PF.tg.openTelegramLink(tgShareLink()); return; } catch (e) { /* ниже */ } }
  if (navigator.share && isPhone()) { navigator.share({ title: S.name || 'Раскладка', text }).catch(err => { if (!err || err.name !== 'AbortError') copyReport(); }); return; }
  copyReport();
}

/* ================= хранилище проектов ================= */
/* облако Telegram: значения до 4096 символов, поэтому проект режем на куски */
const TgStore = {
  cs: null, list: [], CH: 3800,
  call(fn, ...args) { return new Promise((res, rej) => { try { this.cs[fn](...args, (err, val) => err ? rej(err) : res(val)); } catch (e) { rej(e); } }); },
  keys(item, from, to) { const out = []; for (let i = from; i < to; i++) out.push(item.id + '_' + i); return out; },
  async init(tg) {
    if (!tg || !tg.CloudStorage || !PF.version('6.9')) return false; this.cs = tg.CloudStorage;
    try { const v = await this.call('getItem', 'idx'); this.list = v ? JSON.parse(v) : []; } catch (e) { this.list = []; }
    return true;
  },
  async saveIndex() {
    this.list.sort((a, b) => b.updated - a.updated);
    while (JSON.stringify(this.list).length > 4000 && this.list.length > 1) { const old = this.list.pop(); try { await this.call('removeItems', this.keys(old, 0, old.n)); } catch (e) { /* пропускаем */ } }
    await this.call('setItem', 'idx', JSON.stringify(this.list));
  },
  async save(p) {
    const data = JSON.stringify(p.data), n = Math.max(1, Math.ceil(data.length / this.CH)); if (n > 200) throw new Error('too big');
    const old = this.list.find(x => x.id === p.id);
    for (let i = 0; i < n; i++) await this.call('setItem', p.id + '_' + i, data.slice(i * this.CH, (i + 1) * this.CH));
    if (old && old.n > n) { try { await this.call('removeItems', this.keys(old, n, old.n)); } catch (e) { /* пропускаем */ } }
    this.list = this.list.filter(x => x.id !== p.id); this.list.push({ id: p.id, name: String(p.name).slice(0, 60), updated: p.updated, n });
    await this.saveIndex();
  },
  async load(item) { const ks = this.keys(item, 0, item.n), vals = await this.call('getItems', ks); return JSON.parse(ks.map(k => vals[k] || '').join('')); },
  async remove(item) { try { await this.call('removeItems', this.keys(item, 0, item.n)); } catch (e) { /* пропускаем */ } this.list = this.list.filter(x => x.id !== item.id); await this.saveIndex(); },
  async saveMats(list) { const v = JSON.stringify(list); if (v.length <= 4000) await this.call('setItem', 'mats', v); },
  async loadMats() { try { const v = await this.call('getItem', 'mats'); return v ? JSON.parse(v) : []; } catch (e) { return []; } },
};
const Store = {
  db: null, uid: null, cloud: [], mats: [], tg: false,
  localList() { try { return JSON.parse(lsGet(KEY_PROJ) || '[]') || []; } catch (e) { return []; } },
  setLocal(list) { return lsSet(KEY_PROJ, JSON.stringify(list)); },
  col() { return this.db.collection('data/users/' + this.uid); },
  list() { return [...this.cloud.map(p => Object.assign({ where: 'cloud' }, p)), ...(this.tg ? TgStore.list.map(p => Object.assign({ where: 'tg' }, p)) : []), ...this.localList().map(p => Object.assign({ where: 'local' }, p))].sort((a, b) => (b.updated || 0) - (a.updated || 0)); },
  async dataOf(p) { return p.where === 'tg' ? TgStore.load(p) : p.data; },
  async save(p) {
    if (this.db) { try { await this.col().doc(p.id).set({ name: p.name, updated: p.updated, data: JSON.stringify(p.data) }); this.setLocal(this.localList().filter(x => x.id !== p.id)); return 'cloud'; } catch (e) { this.db = null; } }
    if (this.tg) { try { await TgStore.save(p); this.setLocal(this.localList().filter(x => x.id !== p.id)); return 'tg'; } catch (e) { /* ниже — в браузер */ } }
    const l = this.localList().filter(x => x.id !== p.id); l.push(p); return this.setLocal(l) ? 'local' : 'fail';
  },
  async remove(p) { if (p.where === 'cloud' && this.db) { try { await this.col().doc(p.id).delete(); } catch (e) { say('Не удалось удалить: нет связи с аккаунтом.', 'bad'); } } else if (p.where === 'tg') { try { await TgStore.remove(p); } catch (e) { say('Не удалось удалить: нет связи с Telegram.', 'bad'); } } else this.setLocal(this.localList().filter(x => x.id !== p.id)); },
  loadMats() { try { this.mats = JSON.parse(lsGet(KEY_MATS) || '[]') || []; } catch (e) { this.mats = []; } },
  async saveMats(list) { this.mats = list; lsSet(KEY_MATS, JSON.stringify(list)); if (this.db) { try { await this.col().doc('mats').set({ items: JSON.stringify(list) }); } catch (e) { /* остаются в браузере */ } } if (this.tg) { try { await TgStore.saveMats(list); } catch (e) { /* остаются в браузере */ } } },
  async initTelegram(tg) { if (!(await TgStore.init(tg))) return; this.tg = true; const cm = await TgStore.loadMats(), ids = new Set(cm.map(m => m.id)); this.mats = cm.concat(this.mats.filter(m => !ids.has(m.id))); lsSet(KEY_MATS, JSON.stringify(this.mats)); },
  async init() {
    this.loadMats();
    const [db, user] = await Promise.all([capUse('db'), capUse('user')]); if (!db || !user) return;
    let id = null; try { id = await user.id(); } catch (e) { id = null; } if (!id) return;
    this.db = db; this.uid = id;
    try {
      this.col().onSnapshot(snap => {
        this.cloud = snap.docs.filter(d => d.id.startsWith('p_')).map(d => { const x = d.data() || {}; let data = null; try { data = JSON.parse(x.data || 'null'); } catch (e) { data = null; } return { id: d.id, name: x.name || 'Без названия', updated: x.updated || 0, data }; }).filter(p => p.data);
        const md = snap.docs.find(d => d.id === 'mats');
        if (md) { try { const cm = JSON.parse((md.data() || {}).items || '[]'), ids = new Set(cm.map(m => m.id)); this.mats = cm.concat(this.mats.filter(m => !ids.has(m.id))); lsSet(KEY_MATS, JSON.stringify(this.mats)); if (UI.catView === 'custom' && UI.tab === 'mat') renderSizes(); } catch (e) { /* пропускаем */ } }
        if (!$('#modal').hidden && $('#modal').dataset.kind === 'projects') openProjects();
      }, () => { this.db = null; });
    } catch (e) { this.db = null; }
  },
};
const pidNew = () => 'p_' + Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
async function saveProject(asNew) {
  if (asNew || !S.pid) S.pid = pidNew();
  const where = await Store.save({ id: S.pid, name: S.name || 'Без названия', updated: Date.now(), data: projData() });
  lsSet(KEY_DRAFT, JSON.stringify(S));
  say((where === 'cloud' ? 'Проект сохранён в вашем аккаунте — откроется и на другом устройстве.' : where === 'tg' ? 'Проект сохранён в Telegram — откроется в этом боте на любом вашем устройстве.' : where === 'local' ? 'Проект сохранён в приложении.' : 'Не удалось сохранить: память недоступна. Сделайте копию для переноса в «Проектах».') + (where === 'fail' ? '' : ' Фото проекта — кнопка с камерой вверху.'), where === 'fail' ? 'bad' : 'ok'); PF.haptic(where === 'fail' ? 'warn' : 'ok');
  if (!$('#modal').hidden && $('#modal').dataset.kind === 'projects') openProjects();
}
function loadProject(data, pid) {
  S = migrateState(data); S.pid = pid || null;
  UI.sel = null; UI.hl = null; UI.variants = null; UI.room = S.rooms[0].id; UI.target = 'floor'; UI.matTarget = 'main'; UI.catView = S.mat.cat || 'laminate';
  view.fitted = false; recomputeNow(); fitView(); syncAll(); invalidate({ fast: true });
}
function openProjects() {
  const list = Store.list();
  const rows = list.map(p => {
    let a = ''; if (p.data) try { const st = migrateState(p.data); let tot = 0; for (const r of st.rooms) { const g = roomGeom(r); if (g.poly.length >= 3) tot += Math.abs(area(g.poly)); } a = fm2(tot) + ' м²'; } catch (e) { a = ''; }
    const d = p.updated ? new Date(p.updated).toLocaleDateString('ru-RU', { day: 'numeric', month: 'short' }) : '';
    return '<div class="pitem"><div style="min-width:0"><b>' + esc(p.name) + '</b><small>' + [a, d, p.where === 'cloud' ? 'в аккаунте' : p.where === 'tg' ? 'в Telegram' : 'в этом браузере'].filter(Boolean).join(' · ') + '</small></div><div class="acts"><button class="btn small" data-open="' + p.id + '" type="button">Открыть</button><button class="btn small danger" data-del="' + p.id + '" type="button">' + (UI.delArm === p.id ? 'Точно?' : 'Удалить') + '</button></div></div>';
  }).join('');
  openModal('<header><h2>Проекты</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header>' +
    '<p class="note">' + (Store.db ? 'Проекты хранятся в вашем аккаунте и видны только вам.' : Store.tg ? 'Проекты хранятся в облаке Telegram и открываются в этом боте на телефоне и компьютере.' : 'Проекты хранятся в этом браузере. Чтобы перенести на другое устройство, сохраните файл проекта.') + '</p>' +
    '<div class="row-btns"><button class="btn primary" data-pact="save" type="button">Сохранить текущий</button><button class="btn" data-pact="saveas" type="button">Сохранить как новый</button><button class="btn" data-pact="new" type="button">Новый проект</button></div>' +
    '<div class="plist">' + (rows || '<p class="note">Сохранённых проектов пока нет.</p>') + '</div>' +
    '<h3 class="mh">Перенести на другое устройство</h3><p class="note">Копия (.json) — сам проект, чтобы открыть его на другом телефоне или компьютере. Это не картинка: фото проекта — кнопка с камерой вверху.</p>' +
    '<div class="row-btns"><button class="btn" data-pact="export" type="button">Копия для переноса (.json)</button><label class="btn" for="fileIn">Открыть копию</label><input type="file" id="fileIn" accept=".json,.txt,application/json,text/plain" hidden><button class="btn" data-pact="paste" type="button">Вставить текст</button></div>', 'projects');
  $('#fileIn').addEventListener('change', e => { const f = e.target.files && e.target.files[0]; if (!f) return; const rd = new FileReader(); rd.onload = () => importText(String(rd.result)); rd.readAsText(f); });
}
function importText(t) {
  try { const d = JSON.parse(t); if (!d || !(d.rooms || d.room)) throw new Error('bad'); loadProject(d, null); closeModal(); say('Проект «' + (d.name || 'без названия') + '» открыт.', 'ok'); }
  catch (e) { say('Это не файл проекта раскладки. Проверьте текст.', 'bad'); }
}
$('#modal').addEventListener('click', async e => {
  if (e.target.closest('[data-share-file]')) { shareNow(); return; }
  if (e.target === $('#modal') || e.target.closest('[data-close]')) { closeModal(); return; }
  const o = e.target.closest('[data-open]'); if (o) { const p = Store.list().find(x => x.id === o.dataset.open); if (p) { try { loadProject(await Store.dataOf(p), p.id); closeModal(); say('Открыт проект «' + p.name + '».', 'ok'); } catch (err) { say('Не удалось открыть проект: нет связи с Telegram.', 'bad'); } } return; }
  const d = e.target.closest('[data-del]');
  if (d) { if (UI.delArm === d.dataset.del) { const p = Store.list().find(x => x.id === d.dataset.del); UI.delArm = null; if (p) { await Store.remove(p); if (S.pid === p.id) S.pid = null; say('Проект удалён.'); } } else UI.delArm = d.dataset.del; openProjects(); return; }
  const a = e.target.closest('[data-pact]'); if (!a) return;
  const act = a.dataset.pact;
  if (act === 'save') saveProject(false); else if (act === 'saveas') saveProject(true);
  else if (act === 'new') { const st = defaultState(); st.name = 'Новый этаж'; st.rooms = [Object.assign(newRoom('Комната 1', rectWalls(4200, 3600)), { id: 'r1' })]; st.floorPat = Object.assign(defaultPat('remnant'), { refRoom: 'r1' }); st.mat = { cat: 'laminate', item: 'laminate:0', L: 1380, W: 193, T: 8, shape: 'plank', joint: 0, tone: 'oak' }; loadProject(st, null); closeModal(); setTab('plan'); say('Новый проект: впишите размеры комнаты.'); }
  else if (act === 'export') exportProject();
  else if (act === 'paste') openModal('<header><h2>Вставить проект</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header><textarea class="code" id="pasteArea" placeholder="Вставьте сюда текст файла проекта"></textarea><button class="btn primary" data-pact="doPaste" type="button">Открыть</button>');
  else if (act === 'doPaste') importText($('#pasteArea').value);
});
function openModal(html, kind) { const m = $('#modal'); $('#modalBox').innerHTML = html; m.dataset.kind = kind || ''; m.hidden = false; syncTgBack(); }
function closeModal() { $('#modal').hidden = true; $('#modal').dataset.kind = ''; UI.delArm = null; SHARE = null; syncTgBack(); }
document.addEventListener('keydown', e => {
  if (e.key !== 'Escape') return;
  if (!$('#modal').hidden) closeModal(); else if (UI.place) ACT['place-cancel'](); else if (UI.item) ACT['item-back'](); else if (UI.wall) ACT['wall-back']();
});

/* ================= верх, режимы, разделитель ================= */
$('#btnProjects').addEventListener('click', openProjects);
$('#btnPhoto').addEventListener('click', () => exportImage());
$('#btnSave').addEventListener('click', () => saveProject(false));
$('#btnHelp').addEventListener('click', openHelp);
document.addEventListener('click', e => {
  const b = e.target.closest && e.target.closest('[data-view]'); if (!b) return;
  const v = b.dataset.view;
  if (v === 'fit') { fitView(); draw(); }
  else if (v === 'labels') { UI.labels = !UI.labels; syncToolbar(); draw(); saveUI(); say(UI.labels ? 'Размеры на карте показаны.' : 'Размеры на карте скрыты.'); }
  else if (v === 'style') { UI.style = UI.style === 'scheme' ? 'wood' : 'scheme'; syncToolbar(); draw(); saveUI(); say(UI.style === 'scheme' ? 'Схема: жёлтые — подрезки, красные — узкие куски.' : 'Вид «дерево».'); }
});
function syncToolbar() {
  $$('[data-view="labels"]').forEach(b => b.setAttribute('aria-pressed', String(UI.labels)));
  $$('[data-view="style"]').forEach(b => b.setAttribute('aria-pressed', String(UI.style === 'scheme')));
  cv.className = 'm-' + UI.mode; $('#nudge').hidden = UI.mode !== 'pattern'; syncStep(); renderCtxbar();
  if (UI.mode === 'pattern') $('#nudgeTarget').textContent = unitName(UI.target).toLowerCase();
}
const work = $('#work'), mapcol = $('#mapcol'), splitter = $('#splitter');
const isNarrow = () => window.matchMedia('(max-width:900px)').matches;
function setMapH(h) { const total = work.clientHeight; if (!total) return; h = clamp(h, 170, Math.max(170, total - 170)); UI.mapH = h / total; work.style.setProperty('--mapH', Math.round(h) + 'px'); }
function applyMapH() { if (!isNarrow()) return; setMapH((UI.mapH || 0.5) * work.clientHeight); }
let spl = null;
splitter.addEventListener('pointerdown', e => { spl = { y: e.clientY, h: mapcol.getBoundingClientRect().height, moved: false }; splitter.setPointerCapture(e.pointerId); });
splitter.addEventListener('pointermove', e => { if (!spl) return; if (Math.abs(e.clientY - spl.y) > 4) spl.moved = true; if (spl.moved) setMapH(spl.h + (e.clientY - spl.y)); });
/* нажатие без протяжки: карта крупно ↔ поровну */
const splEnd = () => { if (!spl) return; if (!spl.moved) setMapH((UI.mapH || 0.5) > 0.6 ? 0.5 * work.clientHeight : 0.72 * work.clientHeight); spl = null; saveUI(); };
splitter.addEventListener('pointerup', splEnd); splitter.addEventListener('pointercancel', () => { spl = null; });
splitter.addEventListener('keydown', e => { if (e.key === 'ArrowUp' || e.key === 'ArrowDown') { e.preventDefault(); setMapH(mapcol.getBoundingClientRect().height + (e.key === 'ArrowDown' ? 30 : -30)); saveUI(); } else if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); setMapH((UI.mapH || 0.5) > 0.6 ? 0.5 * work.clientHeight : 0.72 * work.clientHeight); saveUI(); } });
function saveUI() { lsSet(KEY_UI, JSON.stringify({ tab: UI.tab, style: UI.style, labels: UI.labels, step: UI.step, helpSeen: !!UI.helpSeen, mapH: UI.mapH, room: UI.room, installOff: !!UI.installOff, open: UI.open })); }
function loadUI() { try { const u = JSON.parse(lsGet(KEY_UI) || 'null'); if (u) Object.assign(UI, { tab: MODE_OF[u.tab] ? u.tab : 'plan', style: u.style || 'wood', labels: u.labels !== false, step: u.step || 10, helpSeen: !!u.helpSeen || u.help === false, mapH: u.mapH || null, room: u.room || UI.room, installOff: !!u.installOff, open: u.open && typeof u.open === 'object' ? u.open : {} }); } catch (e) { /* по умолчанию */ } UI.mode = MODE_OF[UI.tab]; }
function openHelp() {
  openModal('<header><h2>Как пользоваться</h2><button class="icon" data-close type="button" aria-label="Закрыть">' + ICON.del + '</button></header>' +
    '<div class="help"><ol>' +
    '<li><b>Комнаты.</b> Впишите длину и ширину комнаты или нарисуйте её на карте: «+ Комната» под картой. Выбранную комнату тяните пальцем: у соседней стены она прилипнет, в общей стене сразу появится проём, а размер стены разделится по стыку.</li>' +
    '<li><b>Проёмы и ниши — куда сами решите.</b> «+ Проём» или «+ Ниша» под картой, потом ведите пальцем по стене: видно, сколько до каждого угла. Отпустите — встанет там. Готовый проём или нишу тяните по стене, кружки на краях — ширина, ромб — глубина ниши. Точные цифры — в полях под картой.</li>' +
    '<li><b>Покрытие.</b> Выберите вид и размер планки или впишите свой размер.</li>' +
    '<li><b>Рисунок.</b> Выберите рисунок. Тяните его пальцем по карте, стрелкой в центре меняйте направление. «Подобрать» найдёт положение без узких подрезок у стен.</li>' +
    '<li><b>Расчёт.</b> С чего начать, что приходит к каждой стене, ряды, подрезки и сколько покупать. Нажмите на доску на карте — покажу, как её пилить.</li>' +
    '<li><b>Фото проекта.</b> Кнопка с камерой вверху — план с подрезками, сколько покупать, комнаты и как укладывать одной картинкой. На iPhone — «Сохранить в Фото».</li>' +
    '</ol></div>' +
    '<p class="note"><b>Карта:</b> один палец — двигать (на шаге «Рисунок» — двигать рисунок), два пальца — масштаб и сдвиг карты. Кнопка с рамкой под картой — вписать план в экран. Полоску между картой и панелью можно тянуть или нажать — карта станет крупнее.</p>' +
    '<button class="btn primary" data-close type="button">Понятно</button>', 'help');
  UI.helpSeen = true; saveUI();
}
function syncAll() { syncInputs(); renderPlanTab(); syncToolbar(); renderTplChips(); if (UI.tab === 'mat') renderMatTab(); if (UI.tab === 'pat') renderPatTab(); if (UI.tab === 'res') renderResults(); renderStatus(); renderPieceInfo(); applyAcc(); renderSums(); }

/* ================= Telegram и ярлык на экране ================= */
const APP_URL = 'https://vidalost.github.io/Razmer/';
function appUrl() { try { if (location.protocol === 'https:' && !window.claude && !/claude\.ai|claudeusercontent/.test(location.host)) return location.origin + location.pathname; } catch (e) { /* ниже */ } return APP_URL; }
function tgShareLink() { const text = (S.name ? S.name + '\n' : '') + reportText().split('\n').slice(1).join('\n'); return 'https://t.me/share/url?url=' + encodeURIComponent(appUrl()) + '&text=' + encodeURIComponent(text.slice(0, 3000)); }
document.addEventListener('click', e => {
  const a = e.target.closest && e.target.closest('#tgShare'); if (!a) return;
  a.href = tgShareLink();
  if (PF.inTG) { e.preventDefault(); try { PF.tg.openTelegramLink(a.href); } catch (err) { say('Не удалось открыть выбор чата.', 'bad'); } }
});
let TG = null;
function syncTgBack() {
  if (!TG || !PF.version('6.1')) return;
  const need = !$('#modal').hidden || !$('#pieceInfo').hidden || !!UI.addTpl || !!UI.wall || !!UI.item || !!UI.place || UI.tab !== 'plan';
  try { if (need) TG.BackButton.show(); else TG.BackButton.hide(); } catch (e) { /* старый клиент */ }
}
function tgBack() {
  const tabs = ['plan', 'mat', 'pat', 'res'];
  if (!$('#modal').hidden) closeModal();
  else if (!$('#pieceInfo').hidden) ACT['piece-close']();
  else if (UI.addTpl) ACT['add-cancel']();
  else if (UI.place) ACT['place-cancel']();
  else if (UI.item) ACT['item-back']();
  else if (UI.wall) ACT['wall-back']();
  else if (UI.tab !== 'plan') setTab(tabs[Math.max(0, tabs.indexOf(UI.tab) - 1)]);
  syncTgBack();
}
function tgColors() {
  if (!TG || !PF.version('6.1')) return;
  const hex = v => /^#[0-9a-f]{6}$/i.test(v) ? v : null, cs = getComputedStyle(document.documentElement);
  try { const h = hex(cs.getPropertyValue('--panel').trim()); if (h) TG.setHeaderColor(h); } catch (e) { /* старый клиент */ }
  try { const b = hex(cs.getPropertyValue('--paper').trim()); if (b) TG.setBackgroundColor(b); } catch (e) { /* старый клиент */ }
  try { const b = hex(cs.getPropertyValue('--panel').trim()); if (b && PF.version('7.10')) TG.setBottomBarColor(b); } catch (e) { /* старый клиент */ }
}
function initTelegram(tg) {
  TG = tg;
  const theme = () => { document.documentElement.dataset.theme = tg.colorScheme === 'dark' ? 'dark' : 'light'; readColors(); draw(); tgColors(); };
  theme();
  try { tg.onEvent('themeChanged', theme); } catch (e) { /* старый клиент */ }
  try { if (PF.version('6.1')) tg.BackButton.onClick(tgBack); } catch (e) { /* старый клиент */ }
  syncTgBack(); renderInstall();
  Store.initTelegram(tg).then(() => { if (!$('#modal').hidden && $('#modal').dataset.kind === 'projects') openProjects(); });
}
let deferredPrompt = null;
window.addEventListener('beforeinstallprompt', e => { e.preventDefault(); deferredPrompt = e; renderInstall(); });
window.addEventListener('appinstalled', () => { deferredPrompt = null; UI.installOff = true; saveUI(); renderInstall(); say('Приложение установлено — ищите «Раскладку» на экране.', 'ok'); });
const SHARE_ICON = '<svg class="share" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true"><path d="M12 3v12M8 7l4-4 4 4"/><path d="M6 11H5v10h14V11h-1"/></svg>';
function renderInstall() {
  const el = $('#installBox'); if (!el) return;
  let standalone = PF.standalone; try { standalone = standalone || navigator.standalone === true || window.matchMedia('(display-mode: standalone)').matches; } catch (e) { /* как есть */ }
  let framed = false; try { framed = window.top !== window.self; } catch (e) { framed = true; }
  let h = '';
  if (!standalone && !PF.inTG && !window.claude && !framed && !UI.installOff) {
    if (deferredPrompt) h = '<h3>Значок на экране</h3><p>Установите «Раскладку» как приложение: значок на рабочем столе, открывается без адресной строки и работает без интернета.</p><div class="row-btns"><button class="btn primary" type="button" data-act="install">Установить</button><button class="btn" type="button" data-act="install-off">Не сейчас</button></div>';
    else if (PF.ios) h = '<h3>Ярлык на экран «Домой»</h3><p>В Safari нажмите ' + SHARE_ICON + ' <b>«Поделиться»</b>, затем <b>«На экран „Домой“»</b> и <b>«Добавить»</b>. «Раскладка» откроется без адресной строки, как приложение, и будет работать без интернета на объекте.</p><div class="row-btns"><button class="btn" type="button" data-act="install-off">Понятно</button></div>';
  }
  el.innerHTML = h; el.hidden = !h;
}

/* ================= старт ================= */
function start() {
  readColors(); loadUI();
  const draft = lsGet(KEY_DRAFT);
  if (draft) { try { S = migrateState(JSON.parse(draft)); } catch (e) { S = defaultState(); } }
  else { S = defaultState(); }
  UI.catView = S.mat.cat || 'eng';
  recomputeNow();
  setTab(UI.tab); syncAll(); modeHint();
  if (!UI.helpSeen && !draft) setTimeout(openHelp, 400);
  new ResizeObserver(() => { applyMapH(); resizeCanvas(); }).observe(work);
  new ResizeObserver(() => resizeCanvas()).observe(cv);
  applyMapH(); resizeCanvas();
  const mq = window.matchMedia('(prefers-color-scheme: dark)'), retheme = () => { readColors(); draw(); if (UI.tab === 'pat') renderPatList(); };
  if (mq.addEventListener) mq.addEventListener('change', retheme);
  new MutationObserver(retheme).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(() => { readColors(); draw(); });
  Store.init();
  renderInstall();
  PF.ready.then(p => { if (p && p.inTG) initTelegram(p.tg); });
  try { if ('serviceWorker' in navigator && location.protocol === 'https:' && window.top === window.self && !window.claude) navigator.serviceWorker.register('sw.js').catch(() => {}); } catch (e) { /* без офлайна */ }
}
start();
if (/[?&]debug=1/.test(location.search)) window.__rd = { gizmo: () => { const g = gizmo(); return g && { tx: g.tx, ty: g.ty, cx: g.cx, cy: g.cy }; }, rotHandle: () => rotHandle(UI.room), state: () => JSON.parse(JSON.stringify(S)), ui: () => ({ room: UI.room, target: UI.target, mode: UI.mode, tab: UI.tab, wall: UI.wall, item: UI.item, place: UI.place }), w2s: (x, y) => w2s(x, y), adj: () => MODEL.adj, geo: id => { const G = MODEL.geo[id]; return G && { poly: G.g.poly, corners: G.g.corners, doors: G.doors.map(d => [d.wall, d.t0, d.t1]), warn: G.warn || null, err: G.err || null }; } };
})();
