/* Раскладка пола — ядро расчёта.
   Чистая геометрия без DOM: комнаты (в том числе со стенами-дугами), проёмы, рамка вдоль стен,
   вставки, генераторы рисунков и подрезка планок по контуру. Подключается в браузере
   как обычный скрипт (глобальный RazmerEngine) и в Node для тестов (module.exports). */
(function (root) {
'use strict';

/* ================= helpers ================= */
const DEG = Math.PI / 180;
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const mod = (a, n) => ((a % n) + n) % n;
const num = (v, d = 0) => { const x = typeof v === 'number' ? v : parseFloat(String(v ?? '').replace(',', '.').replace(/\s/g, '')); return Number.isFinite(x) ? x : d; };
const mm = x => String(Math.round(x));
const f1 = x => (Math.round(x * 10) / 10).toString().replace('.', ',');
const fm2 = a => (a / 1e6).toFixed(2).replace('.', ',');
const dist = (a, b) => Math.hypot(b[0] - a[0], b[1] - a[1]);
const plural = (n, a, b, c) => { const n10 = n % 10, n100 = n % 100; if (n10 === 1 && n100 !== 11) return a; if (n10 >= 2 && n10 <= 4 && (n100 < 10 || n100 >= 20)) return b; return c; };
function hash01(n) { n = n | 0; n = (n ^ 61) ^ (n >>> 16); n = (n + (n << 3)) | 0; n = n ^ (n >>> 4); n = Math.imul(n, 0x27d4eb2d); n = n ^ (n >>> 15); return (n >>> 0) / 4294967296; }

/* ================= geometry ================= */
function area(p) { let a = 0; for (let i = 0, n = p.length; i < n; i++) { const q = p[i], r = p[(i + 1) % n]; a += q[0] * r[1] - r[0] * q[1]; } return a / 2; }
function perim(p) { let s = 0; for (let i = 0, n = p.length; i < n; i++) s += dist(p[i], p[(i + 1) % n]); return s; }
function inPoly(x, y, p) { let c = false; for (let i = 0, j = p.length - 1; i < p.length; j = i++) { const a = p[i], b = p[j]; if (((a[1] > y) !== (b[1] > y)) && (x < (b[0] - a[0]) * (y - a[1]) / (b[1] - a[1]) + a[0])) c = !c; } return c; }
function segDist(px, py, a, b) { const dx = b[0] - a[0], dy = b[1] - a[1], l2 = dx * dx + dy * dy; let t = l2 ? ((px - a[0]) * dx + (py - a[1]) * dy) / l2 : 0; t = clamp(t, 0, 1); return Math.hypot(px - a[0] - t * dx, py - a[1] - t * dy); }
function minEdgeDist(x, y, p) { let m = Infinity; for (let i = 0, n = p.length; i < n; i++) { const d = segDist(x, y, p[i], p[(i + 1) % n]); if (d < m) m = d; } return m; }
function bboxOf(p) { let u0 = Infinity, v0 = Infinity, u1 = -Infinity, v1 = -Infinity; for (const q of p) { if (q[0] < u0) u0 = q[0]; if (q[0] > u1) u1 = q[0]; if (q[1] < v0) v0 = q[1]; if (q[1] > v1) v1 = q[1]; } return { u0, v0, u1, v1 }; }
const bbHit = (a, b) => !(a.u1 <= b.u0 || a.u0 >= b.u1 || a.v1 <= b.v0 || a.v0 >= b.v1);
function bbUnion(list) { const b = { u0: Infinity, v0: Infinity, u1: -Infinity, v1: -Infinity }; for (const x of list) { b.u0 = Math.min(b.u0, x.u0); b.v0 = Math.min(b.v0, x.v0); b.u1 = Math.max(b.u1, x.u1); b.v1 = Math.max(b.v1, x.v1); } return b; }
function centroid(p) { let a = 0, cx = 0, cy = 0; const n = p.length; for (let i = 0; i < n; i++) { const q = p[i], r = p[(i + 1) % n]; const c = q[0] * r[1] - r[0] * q[1]; a += c; cx += (q[0] + r[0]) * c; cy += (q[1] + r[1]) * c; } if (Math.abs(a) < 1e-9) { let sx = 0, sy = 0; for (const q of p) { sx += q[0]; sy += q[1]; } return [sx / n, sy / n]; } return [cx / (3 * a), cy / (3 * a)]; }
function centroidMany(polys) { let A = 0, x = 0, y = 0; for (const p of polys) { const a = Math.abs(area(p)), c = centroid(p); A += a; x += c[0] * a; y += c[1] * a; } return A > 0 ? [x / A, y / A] : centroid(polys[0]); }
function dedupe(p) { const out = []; for (const q of p) { const l = out[out.length - 1]; if (!l || Math.abs(l[0] - q[0]) > 0.01 || Math.abs(l[1] - q[1]) > 0.01) out.push(q); } while (out.length > 1) { const a = out[0], b = out[out.length - 1]; if (Math.abs(a[0] - b[0]) <= 0.01 && Math.abs(a[1] - b[1]) <= 0.01) out.pop(); else break; } return out.length >= 3 ? out : []; }
/* оставить часть многоугольника по одну сторону прямой a→b (side = +1 / -1) */
function clipHalf(poly, a, b, side) {
  const n = poly.length; if (!n) return [];
  const ex = b[0] - a[0], ey = b[1] - a[1], out = [];
  let P = poly[n - 1], dP = side * (ex * (P[1] - a[1]) - ey * (P[0] - a[0]));
  for (let k = 0; k < n; k++) {
    const C = poly[k], dC = side * (ex * (C[1] - a[1]) - ey * (C[0] - a[0]));
    if (dC >= -1e-7) { if (dP < -1e-7) { const t = dP / (dP - dC); out.push([P[0] + (C[0] - P[0]) * t, P[1] + (C[1] - P[1]) * t]); } out.push(C); }
    else if (dP >= -1e-7) { const t = dP / (dP - dC); out.push([P[0] + (C[0] - P[0]) * t, P[1] + (C[1] - P[1]) * t]); }
    P = C; dP = dC;
  }
  return out;
}
/* Сазерленд–Ходжмен: subject — любой многоугольник (комната), clip — выпуклый (планка) */
function clipBy(subject, clip) {
  const s = area(clip) >= 0 ? 1 : -1; let out = subject;
  for (let i = 0, n = clip.length; i < n && out.length; i++) out = clipHalf(out, clip[i], clip[(i + 1) % n], s);
  return dedupe(out);
}
/* выпуклый s минус выпуклый r → список выпуклых кусков */
function convexMinus(s, r) {
  if (!bbHit(bboxOf(s), bboxOf(r))) return [s];
  const sg = area(r) >= 0 ? 1 : -1, out = []; let rest = s;
  for (let i = 0; i < r.length && rest.length; i++) {
    const a = r[i], b = r[(i + 1) % r.length];
    const o = dedupe(clipHalf(rest, a, b, -sg)); if (o.length >= 3 && Math.abs(area(o)) > 0.5) out.push(o);
    rest = dedupe(clipHalf(rest, a, b, sg));
  }
  return out;
}
function insetPoly(p, d) {
  const n = p.length, s = area(p) >= 0 ? 1 : -1, L = [];
  for (let i = 0; i < n; i++) { const a = p[i], b = p[(i + 1) % n]; let dx = b[0] - a[0], dy = b[1] - a[1]; const l = Math.hypot(dx, dy) || 1; dx /= l; dy /= l; const nx = s > 0 ? -dy : dy, ny = s > 0 ? dx : -dx; L.push({ px: a[0] + nx * d, py: a[1] + ny * d, dx, dy, nx, ny }); }
  const out = [];
  for (let i = 0; i < n; i++) {
    const A = L[(i - 1 + n) % n], B = L[i], den = A.dx * B.dy - A.dy * B.dx;
    if (Math.abs(den) < 1e-9) { out.push([p[i][0] + B.nx * d, p[i][1] + B.ny * d]); continue; }
    const t = ((B.px - A.px) * B.dy - (B.py - A.py) * B.dx) / den; out.push([A.px + A.dx * t, A.py + A.dy * t]);
  }
  return out;
}
const thickOf = poly => { const P = perim(poly); return P > 0 ? 2 * Math.abs(area(poly)) / P : 0; };
function onLine(p, q, a, b, tol) { const dx = b[0] - a[0], dy = b[1] - a[1], l = Math.hypot(dx, dy); if (l < 1e-6) return false; const nx = -dy / l, ny = dx / l; return Math.abs((p[0] - a[0]) * nx + (p[1] - a[1]) * ny) < tol && Math.abs((q[0] - a[0]) * nx + (q[1] - a[1]) * ny) < tol; }

/* ================= каталог ================= */
const I = (L, W, T, note, x) => Object.assign({ L, W, T, note: note || '' }, x || {});
const HB = { pat: 'herring1' }, CHV = a => ({ shape: 'chevron', angle: a, pat: 'chevron' }), TL = { shape: 'tile' }, TLg = p => ({ shape: 'tile', pat: p });
const CATS = [
  { id: 'laminate', name: 'Ламинат', gap: 10, kerf: 3, minPiece: 300, minStag: 300, tone: 'oak', pat: 'remnant', items: [
    I(1380, 193, 8, 'классика'), I(1380, 244, 8, 'широкий'), I(1380, 157, 8, 'узкий'), I(1285, 192, 8, 'классика'), I(1292, 193, 10, 'классика'),
    I(1292, 246, 8, 'широкий'), I(1292, 327, 8, 'XL'), I(1845, 244, 10, 'длинный'), I(1218, 198, 8, ''), I(1200, 190, 8, ''),
    I(600, 120, 8, 'ёлочка', HB), I(600, 100, 8, 'ёлочка', HB)] },
  { id: 'spc', name: 'Кварцвинил', gap: 5, kerf: 1, minPiece: 200, minStag: 200, tone: 'grey', pat: 'remnant', items: [
    I(1220, 180, 4, 'замковый'), I(1220, 183, 4, 'замковый'), I(1220, 228, 5, 'замковый, широкий'), I(1500, 228, 5, 'замковый'), I(1524, 228, 5, 'замковый'),
    I(610, 305, 4, 'плитка замковая', TLg('bond2')), I(600, 300, 4, 'плитка замковая', TLg('bond2')), I(914, 457, 5, 'под камень', TLg('bond2')), I(600, 600, 5, 'плитка', TLg('grid')),
    I(1219, 184, 2.5, 'клеевой'), I(914, 152, 2.5, 'клеевой'), I(1219, 228, 2.5, 'клеевой'), I(457, 457, 2.5, 'клеевая плитка', TLg('grid')),
    I(600, 125, 4, 'ёлочка', HB), I(615, 123, 4, 'ёлочка', HB), I(630, 126, 4, 'ёлочка', HB), I(720, 120, 4, 'ёлочка', HB),
    I(600, 125, 4, 'французская 45°', CHV(45)), I(720, 120, 4, 'французская 45°', CHV(45))] },
  { id: 'pboard', name: 'Паркетная доска', gap: 10, kerf: 3, minPiece: 500, minStag: 500, tone: 'natural', pat: 'remnant', items: [
    I(2200, 190, 14, 'трёхслойная'), I(2266, 188, 14, ''), I(2215, 194, 14, ''), I(2423, 187, 15, ''), I(2000, 190, 14, ''),
    I(1860, 190, 14, ''), I(1800, 140, 14, 'однополосная'), I(2200, 207, 14, '')] },
  { id: 'eng', name: 'Инженерная доска', gap: 10, kerf: 3, minPiece: 400, minStag: 400, tone: 'natural', pat: 'remnant', items: [
    I(1900, 190, 15, 'палуба'), I(2200, 220, 16, 'палуба'), I(1500, 150, 15, 'палуба'), I(1200, 120, 15, 'палуба'), I(1820, 180, 15, 'палуба'),
    I(2400, 240, 20, 'палуба'), I(1900, 240, 16, 'палуба'),
    I(500, 100, 14, 'ёлочка', HB), I(600, 100, 14, 'ёлочка', HB), I(600, 120, 15, 'ёлочка', HB), I(720, 120, 15, 'ёлочка', HB), I(700, 140, 16, 'ёлочка', HB), I(900, 150, 16, 'ёлочка', HB),
    I(600, 120, 15, 'французская 45°', CHV(45)), I(720, 120, 15, 'французская 45°', CHV(45)), I(900, 150, 16, 'французская 45°', CHV(45)), I(600, 100, 14, 'французская 60°', CHV(60))] },
  { id: 'solid', name: 'Массивная доска', gap: 10, kerf: 3, minPiece: 300, minStag: 300, tone: 'walnut', pat: 'remnant', items: [
    I(1800, 120, 20, ''), I(1500, 130, 20, ''), I(1200, 90, 18, ''), I(900, 90, 18, ''), I(2000, 140, 20, ''), I(1820, 150, 20, ''), I(600, 90, 18, 'короткая')] },
  { id: 'parquet', name: 'Штучный паркет', gap: 8, kerf: 2, minPiece: 150, minStag: 150, tone: 'oak', pat: 'herring1', items: [
    I(280, 70, 15, '4 в квадрат'), I(300, 75, 15, '4 в квадрат'), I(350, 70, 15, '5 в квадрат'), I(400, 80, 15, '5 в квадрат'), I(420, 70, 15, '6 в квадрат'),
    I(450, 75, 15, '6 в квадрат'), I(480, 80, 15, '6 в квадрат'), I(490, 70, 15, '7 в квадрат'), I(560, 70, 15, '8 в квадрат'), I(500, 70, 15, ''),
    I(600, 100, 15, ''), I(600, 120, 15, '')] },
  { id: 'module', name: 'Модульный паркет', gap: 8, kerf: 3, minPiece: 100, minStag: 100, tone: 'natural', pat: 'grid', items: [
    I(400, 400, 16, 'модуль', TL), I(450, 450, 16, 'модуль', TL), I(500, 500, 16, 'модуль', TL), I(600, 600, 18, 'шашка', TL), I(750, 750, 20, 'модуль', TL), I(1000, 1000, 20, 'Версаль', TL)] },
  { id: 'tile', name: 'Керамогранит', gap: 5, kerf: 2, minPiece: 100, minStag: 100, tone: 'stone', pat: 'grid', joint: 2, items: [
    I(600, 600, 9, '', TL), I(1200, 600, 9, '', TLg('bond2')), I(600, 300, 9, '', TLg('bond2')), I(1200, 200, 9, 'под дерево', TLg('bond3')), I(900, 150, 9, 'под дерево', TLg('bond3')),
    I(800, 800, 9, '', TL), I(1200, 1200, 9, '', TL), I(300, 300, 8, '', TL), I(450, 450, 8, '', TL)] },
  { id: 'cork', name: 'Пробка', gap: 8, kerf: 2, minPiece: 200, minStag: 200, tone: 'cork', pat: 'remnant', items: [
    I(905, 295, 10, 'замковая'), I(600, 300, 4, 'клеевая', TLg('bond2')), I(1220, 185, 10, 'замковая')] },
  { id: 'custom', name: 'Свои размеры', gap: 10, kerf: 3, minPiece: 300, minStag: 300, tone: 'oak', pat: 'remnant', items: [] },
];
const catById = id => CATS.find(c => c.id === id) || CATS[0];
const TONES = {
  oak: { n: 'Дуб светлый', c: [212, 177, 128] }, natural: { n: 'Дуб натуральный', c: [189, 142, 92] }, walnut: { n: 'Орех', c: [120, 84, 60] },
  grey: { n: 'Серый дуб', c: [168, 162, 152] }, white: { n: 'Белёный', c: [229, 221, 206] }, smoke: { n: 'Копчёный', c: [98, 79, 64] },
  stone: { n: 'Камень', c: [188, 187, 181] }, cork: { n: 'Пробка', c: [186, 142, 98] },
};
const PATTERNS = [
  { id: 'remnant', name: 'Палуба по остаткам', sub: 'обрезок начинает ряд', group: 'bond' },
  { id: 'bond2', name: 'Смещение 1/2', sub: 'кирпич', group: 'bond', frac: 1 / 2 },
  { id: 'bond3', name: 'Смещение 1/3', sub: 'лесенка', group: 'bond', frac: 1 / 3 },
  { id: 'bond4', name: 'Смещение 1/4', sub: 'мелкая лесенка', group: 'bond', frac: 1 / 4 },
  { id: 'random', name: 'Вразбежку', sub: 'случайный разбег', group: 'bond' },
  { id: 'grid', name: 'Шов в шов', sub: 'прямая сетка', group: 'bond', frac: 0 },
  { id: 'herring1', name: 'Ёлочка', sub: 'классическая', group: 'herring', n: 1 },
  { id: 'herring2', name: 'Двойная ёлочка', sub: 'по 2 планки', group: 'herring', n: 2 },
  { id: 'herring3', name: 'Тройная ёлочка', sub: 'по 3 планки', group: 'herring', n: 3 },
  { id: 'chevron', name: 'Французская ёлочка', sub: 'шеврон, венгерская', group: 'chevron' },
  { id: 'basket', name: 'Квадраты', sub: 'плетёнка, шашка', group: 'basket' },
];
const patDef = id => PATTERNS.find(p => p.id === id) || PATTERNS[0];
const BORDER_PATTERNS = ['remnant', 'bond2', 'bond3', 'bond4', 'grid'];

const rectWalls = (L, W) => [{ len: L, turn: 0, arc: 0 }, { len: W, turn: 90, arc: 0 }, { len: L, turn: 90, arc: 0 }, { len: W, turn: 90, arc: 0 }];
const w_ = (len, turn, arc) => ({ len, turn: turn || 0, arc: arc || 0 });
const TEMPLATES = [
  { id: 'rect', name: 'Прямоугольник', make: () => rectWalls(4200, 3600) },
  { id: 'L', name: 'Г-образная', make: () => [w_(5000), w_(2000, 90), w_(2400, 90), w_(2000, -90), w_(2600, 90), w_(4000, 90)] },
  { id: 'U', name: 'П-образная', make: () => [w_(6000), w_(4000, 90), w_(2000, 90), w_(2000, 90), w_(2000, -90), w_(2000, -90), w_(2000, 90), w_(4000, 90)] },
  { id: 'bevel', name: 'Скошенный угол', make: () => [w_(4000), w_(1414, 45), w_(2500, 45), w_(5000, 90), w_(3500, 90)] },
  { id: 'bay', name: 'Эркер', make: () => [w_(1500), w_(849, -45), w_(1800, 45), w_(849, 45), w_(1500, -45), w_(4000, 90), w_(6000, 90), w_(4000, 90)] },
  { id: 'arcwall', name: 'Стена-дуга', make: () => [w_(5000), w_(3600, 90), w_(5000, 90, 700), w_(3600, 90)] },
  { id: 'semi', name: 'Полукруг', make: () => [w_(5000), w_(5000, 180, 2500)] },
  { id: 'round', name: 'Круг', make: () => [w_(4000, 0, 2000), w_(4000, 180, 2000)] },
  { id: 'corridor', name: 'Коридор', make: () => rectWalls(7200, 1400) },
];

/* ================= состояние по умолчанию ================= */
function defaultPat(type) {
  type = type || 'remnant'; const g = patDef(type).group;
  return { type, refRoom: null, refWall: 0, dir: 'along', angle: 30, chevAngle: 45, offA: 0, offB: 0, flipU: false, flipV: false, minPiece: 300, minStag: 300, minEdge: g === 'bond' ? 50 : 25, seed: 1, keepCenter: g === 'herring' || g === 'chevron' };
}
const defBorder = () => ({ on: false, rows: 2, mat: null, pat: Object.assign(defaultPat('bond2'), { minPiece: 200, minStag: 200 }) });
let ridSeq = 0;
const newId = p => p + Date.now().toString(36).slice(-4) + (ridSeq++).toString(36) + Math.random().toString(36).slice(2, 5);
function newRoom(name, walls, x0, y0) { return { id: newId('r'), name: name || 'Комната', x0: x0 || 0, y0: y0 || 0, a0: 0, walls: walls || rectWalls(4200, 3600), doors: [], own: false, pat: defaultPat('remnant'), mat: null, border: defBorder(), inserts: [] }; }
function defaultState() {
  const r1 = { id: 'r1', name: 'Гостиная', x0: 0, y0: 0, a0: 0, walls: rectWalls(5200, 3850), doors: [{ id: 'd1', wall: 1, pos: 1450, width: 900 }], own: false, pat: defaultPat('remnant'), mat: null, border: defBorder(), inserts: [] };
  const r2 = { id: 'r2', name: 'Спальня', x0: 5320, y0: 0, a0: 0, walls: rectWalls(3600, 3850), doors: [], own: false, pat: defaultPat('remnant'), mat: null, border: defBorder(), inserts: [] };
  return {
    v: 2, pid: null, name: 'Пример: гостиная и спальня',
    mat: { cat: 'eng', item: 'eng:9', L: 600, W: 120, T: 15, shape: 'plank', joint: 0, tone: 'natural' },
    set: { gap: 10, kerf: 3, perPack: 0, packM2: 0, reserve: 5, wallT: 120 },
    rooms: [r1, r2],
    floorPat: Object.assign(defaultPat('herring1'), { refRoom: 'r1', minPiece: 150, minStag: 150, offA: 78, offB: 218 }),
  };
}
/* приводим старые сохранения (одна комната) и битые данные к текущему виду */
function migrateState(st) {
  const d = defaultState();
  if (!st || typeof st !== 'object') return d;
  if (st.v !== 2 && st.room) {
    const room = { id: 'r1', name: 'Комната 1', x0: num(st.room.x0), y0: num(st.room.y0), a0: num(st.room.a0), walls: (st.room.walls || []).map(w => w_(num(w.len, 1000), num(w.turn), 0)), doors: [], own: false, pat: defaultPat('remnant'), mat: null, border: defBorder(), inserts: [] };
    const tone = (st.set && st.set.tone) || 'oak';
    st = { v: 2, pid: st.pid || null, name: st.name, mat: Object.assign({}, st.mat, { tone }), set: Object.assign({}, st.set), rooms: [room], floorPat: Object.assign(defaultPat((st.pat && st.pat.type) || 'remnant'), st.pat || {}, { refRoom: 'r1' }) };
  }
  const out = { v: 2, pid: st.pid || null, name: typeof st.name === 'string' ? st.name : d.name };
  out.mat = Object.assign({}, d.mat, st.mat || {});
  out.set = Object.assign({}, d.set, st.set || {});
  delete out.set.tone;
  out.floorPat = Object.assign(defaultPat(), st.floorPat || {});
  if (!PATTERNS.some(p => p.id === out.floorPat.type)) out.floorPat.type = 'remnant';
  const rooms = Array.isArray(st.rooms) && st.rooms.length ? st.rooms : d.rooms;
  out.rooms = rooms.map((r, i) => {
    const walls = Array.isArray(r.walls) && r.walls.length >= 2 ? r.walls.map(w => w_(Math.max(0, num(w.len, 1000)), num(w.turn), num(w.arc))) : rectWalls(4200, 3600);
    const pat = Object.assign(defaultPat(), r.pat || {}); if (!PATTERNS.some(p => p.id === pat.type)) pat.type = 'remnant';
    const border = Object.assign(defBorder(), r.border || {}); border.pat = Object.assign(defaultPat('bond2'), (r.border && r.border.pat) || {});
    if (!BORDER_PATTERNS.includes(border.pat.type)) border.pat.type = 'bond2';
    return {
      id: String(r.id || 'r' + (i + 1)), name: String(r.name || 'Комната ' + (i + 1)), x0: num(r.x0), y0: num(r.y0), a0: num(r.a0), walls,
      doors: (Array.isArray(r.doors) ? r.doors : []).map((x, j) => ({ id: String(x.id || 'd' + j), wall: num(x.wall) | 0, pos: num(x.pos), width: Math.max(100, num(x.width, 800)) })),
      own: !!r.own, pat, mat: r.mat && typeof r.mat === 'object' ? Object.assign({}, d.mat, r.mat) : null, border,
      inserts: (Array.isArray(r.inserts) ? r.inserts : []).map((x, j) => ({ id: String(x.id || 'i' + j), w: Math.max(100, num(x.w, 2000)), h: Math.max(100, num(x.h, 2000)), dx: num(x.dx), dy: num(x.dy), rot: num(x.rot), pat: Object.assign(defaultPat('basket'), x.pat || {}), mat: x.mat && typeof x.mat === 'object' ? Object.assign({}, d.mat, x.mat) : null })),
    };
  });
  if (!out.rooms.some(r => r.id === out.floorPat.refRoom)) out.floorPat.refRoom = out.rooms[0].id;
  return out;
}

/* ================= комната: стены, дуги, контур ================= */
/* точки дуги между углами P и Q; h — прогиб (+ наружу), sgn — ориентация обхода */
function arcPts(P, Q, h, sgn) {
  const c = dist(P, Q); if (c < 1 || Math.abs(h) < 0.5) return [];
  const d = [(Q[0] - P[0]) / c, (Q[1] - P[1]) / c], n = sgn > 0 ? [d[1], -d[0]] : [-d[1], d[0]];
  const M = [(P[0] + Q[0]) / 2, (P[1] + Q[1]) / 2], A = [M[0] + n[0] * h, M[1] + n[1] * h];
  const R = (c * c / 4 + h * h) / (2 * Math.abs(h)), sh = Math.sign(h), C = [A[0] - n[0] * sh * R, A[1] - n[1] * sh * R];
  const ang = p => Math.atan2(p[1] - C[1], p[0] - C[0]);
  const nrm = x => { while (x <= -Math.PI) x += 2 * Math.PI; while (x > Math.PI) x -= 2 * Math.PI; return x; };
  const t0 = ang(P), tot = nrm(ang(A) - t0) + nrm(ang(Q) - ang(A));
  const k = clamp(Math.ceil(Math.abs(tot) / (4 * DEG)), 2, 90), out = [];
  for (let i = 1; i < k; i++) { const t = t0 + tot * i / k; out.push([C[0] + R * Math.cos(t), C[1] + R * Math.sin(t)]); }
  return out;
}
const arcRadius = (c, h) => Math.abs(h) < 0.5 ? Infinity : (c * c / 4 + h * h) / (2 * Math.abs(h));
function arcLength(c, h) { if (Math.abs(h) < 0.5) return c; const R = arcRadius(c, h), half = Math.asin(clamp(c / 2 / R, -1, 1)); const th = Math.abs(h) > c / 2 ? 2 * (Math.PI - half) : 2 * half; return R * th; }
const sagittaFromRadius = (c, R) => (R < c / 2 ? NaN : R - Math.sqrt(R * R - c * c / 4));

function roomGeom(room) {
  let x = num(room.x0), y = num(room.y0), h = num(room.a0) * DEG;
  const W = room.walls || [], corners = [[x, y]];
  W.forEach((w, i) => { if (i > 0) h += num(w.turn) * DEG; x += num(w.len) * Math.cos(h); y += num(w.len) * Math.sin(h); corners.push([x, y]); });
  const closure = dist(corners[corners.length - 1], corners[0]), closed = closure < 1;
  if (closed) corners.pop();
  const n = corners.length, arcs = W.map(w => num(w.arc)).slice(0, n);
  while (arcs.length < n) arcs.push(0);
  const build = sg => { const poly = [], wIdx = []; for (let i = 0; i < n; i++) { const P = corners[i], Q = corners[(i + 1) % n]; wIdx.push(poly.length); poly.push(P); for (const q of arcPts(P, Q, arcs[i], sg)) poly.push(q); } return { poly, wIdx }; };
  let sgn = Math.sign(area(corners)) || 1, b = build(sgn);
  const s2 = Math.sign(area(b.poly)) || 1; if (s2 !== sgn) { sgn = s2; b = build(sgn); }
  return { corners, poly: b.poly, wIdx: b.wIdx, n, closure, autoClosed: !closed, sgn, arcs };
}
function wallsFromCorners(corners, arcs) {
  const n = corners.length, walls = []; let prev = 0, a0 = 0;
  for (let i = 0; i < n; i++) {
    const P = corners[i], Q = corners[(i + 1) % n], len = dist(P, Q), hd = Math.atan2(Q[1] - P[1], Q[0] - P[0]) / DEG;
    if (i === 0) { a0 = hd; walls.push(w_(len, 0, arcs[i])); } else { const t = mod(hd - prev + 180, 360) - 180; walls.push(w_(len, t, arcs[i])); }
    prev = hd;
  }
  return { x0: corners[0][0], y0: corners[0][1], a0, walls };
}
/* внутренний угол между хордами стен (90 — обычный, 270 — выступ) */
function innerAngles(g) {
  const { corners: c, n, sgn } = g, out = [];
  for (let i = 0; i < n; i++) {
    const a = c[(i - 1 + n) % n], b = c[i], d = c[(i + 1) % n];
    const h1 = Math.atan2(b[1] - a[1], b[0] - a[0]), h2 = Math.atan2(d[1] - b[1], d[0] - b[0]);
    let t = (h2 - h1) / DEG; t = mod(t + 180, 360) - 180; out.push(180 - sgn * t);
  }
  return out;
}
const unitV = (a, b) => { const l = dist(a, b) || 1; return [(b[0] - a[0]) / l, (b[1] - a[1]) / l]; };
const inwardOf = (e1, sgn) => sgn > 0 ? [-e1[1], e1[0]] : [e1[1], -e1[0]];

function unitMat(m, S) {
  const x = m || S.mat;
  return { L: num(x.L), W: num(x.W), g: Math.max(0, num(x.joint)), shape: x.shape || 'plank', kerf: Math.max(0, num(S.set.kerf, 3)), tone: x.tone || 'oak', cat: x.cat || 'custom', T: x.T, key: [num(x.L), num(x.W), x.shape || 'plank', num(x.joint)].join('|') };
}
function tolFor(S) { const gap = Math.max(0, num(S.set.gap)); return gap > 0 ? clamp(gap * 0.3, 1, 4) : 0.5; }

/* контур укладки комнаты: зазор, рамка, проёмы, вставки */
function roomLay(room, S) {
  const out = { room, err: null, doors: [], inserts: [], sides: null };
  const W = room.walls || [];
  if (W.length < 2) { out.err = 'Нужно хотя бы 2 стены.'; return out; }
  const bad = W.findIndex(w => num(w.len) < 5); if (bad >= 0) { out.err = 'Стена ' + (bad + 1) + ' нулевой длины — впишите размер.'; return out; }
  const g = roomGeom(room); out.g = g;
  if (g.poly.length < 3 || Math.abs(area(g.poly)) < 2e5) { out.err = 'Комната не построена: проверьте длины и углы.'; return out; }
  const gap = Math.max(0, num(S.set.gap)), tol = tolFor(S);
  const lay = gap > 0 ? insetPoly(g.poly, gap) : g.poly.map(p => p.slice());
  if (Math.abs(area(lay)) < 1e5 || Math.sign(area(lay)) !== g.sgn) { out.err = 'Зазор слишком большой для этой комнаты.'; return out; }
  out.lay = lay; out.outer = gap - tol > 0 ? insetPoly(g.poly, gap - tol) : g.poly;
  let center = lay;
  const B = room.border;
  if (B && B.on) {
    const bm = unitMat(B.mat, S), bw = Math.max(1, num(B.rows, 1) | 0) * (bm.W + bm.g);
    const inner = insetPoly(lay, bw);
    if (bm.W >= 20 && Math.abs(area(inner)) > 1e5 && Math.sign(area(inner)) === g.sgn) {
      center = inner; out.inner = inner; out.bw = bw; out.sides = [];
      const n = g.n, Lp = lay.length;
      for (let i = 0; i < n; i++) {
        const s = g.wIdx[i], e = i + 1 < n ? g.wIdx[i + 1] : Lp, pts = [];
        for (let k = s; k <= e; k++) pts.push(lay[k % Lp]);
        for (let k = e; k >= s; k--) pts.push(inner[k % Lp]);
        const poly = dedupe(pts), A = lay[s], Bp = lay[e % Lp];
        if (poly.length < 3 || dist(A, Bp) < 1) { out.sides.push(null); continue; }
        const e1 = unitV(A, Bp); out.sides.push({ poly, A, e1, e2: inwardOf(e1, g.sgn), wall: i });
      }
    } else out.borderErr = 'Рамка не помещается: уменьшите число рядов.';
  }
  out.center = center;
  for (const d of room.doors || []) { const r = doorRect(g, d, S); if (r) out.doors.push(r); }
  for (const ins of room.inserts || []) out.inserts.push(insertGeom(out, ins));
  return out;
}
function doorRect(g, d, S) {
  const i = num(d.wall) | 0; if (i < 0 || i >= g.n || Math.abs(g.arcs[i]) >= 0.5) return null;
  const P = g.corners[i], Q = g.corners[(i + 1) % g.n], c = dist(P, Q); if (c < 50) return null;
  const t0 = clamp(num(d.pos), 0, c - 20), t1 = clamp(num(d.pos) + num(d.width, 800), t0 + 20, c);
  const u = unitV(P, Q), n = g.sgn > 0 ? [u[1], -u[0]] : [-u[1], u[0]];
  const gap = Math.max(0, num(S.set.gap)), T = Math.max(0, num(S.set.wallT, 120));
  const B1 = [P[0] + u[0] * t0, P[1] + u[1] * t0], B2 = [P[0] + u[0] * t1, P[1] + u[1] * t1];
  const poly = [[B1[0] - n[0] * gap, B1[1] - n[1] * gap], [B2[0] - n[0] * gap, B2[1] - n[1] * gap], [B2[0] + n[0] * (T + gap), B2[1] + n[1] * (T + gap)], [B1[0] + n[0] * (T + gap), B1[1] + n[1] * (T + gap)]];
  return { poly, door: d, wall: i, t0, t1, u, n, P };
}
function insertGeom(G, ins) {
  const g = G.g, e1 = unitV(g.corners[0], g.corners[1 % g.n]), e2 = inwardOf(e1, g.sgn), c = centroid(G.center);
  const C = [c[0] + e1[0] * num(ins.dx) + e2[0] * num(ins.dy), c[1] + e1[1] * num(ins.dx) + e2[1] * num(ins.dy)];
  const t = num(ins.rot) * DEG, a = [Math.cos(t) * e1[0] + Math.sin(t) * e2[0], Math.cos(t) * e1[1] + Math.sin(t) * e2[1]], b = [-Math.sin(t) * e1[0] + Math.cos(t) * e2[0], -Math.sin(t) * e1[1] + Math.cos(t) * e2[1]];
  const hw = Math.max(50, num(ins.w)) / 2, hh = Math.max(50, num(ins.h)) / 2;
  const P = (sx, sy) => [C[0] + a[0] * sx * hw + b[0] * sy * hh, C[1] + a[1] * sx * hw + b[1] * sy * hh];
  const rect = [P(-1, -1), P(1, -1), P(1, 1), P(-1, 1)];
  return { ins, C, a, b, rect, region: clipBy(G.center, rect) };
}
function computeGeo(S) { const geo = {}; for (const r of S.rooms) geo[r.id] = roomLay(r, S); return geo; }

/* ================= система координат рисунка ================= */
const dirDeg = p => p.dir === 'across' ? 90 : p.dir === 'diag' ? 45 : p.dir === 'custom' ? num(p.angle, 0) : 0;
function makeFrame(A, e1, e2, pat) {
  const rho = dirDeg(pat) * DEG, c = Math.cos(rho), sn = Math.sin(rho);
  let eu = [c * e1[0] + sn * e2[0], c * e1[1] + sn * e2[1]];
  let ev = [-sn * e1[0] + c * e2[0], -sn * e1[1] + c * e2[1]];
  if (ev[0] * e1[0] + ev[1] * e1[1] < -1e-9 && ev[0] * e2[0] + ev[1] * e2[1] < 1e-9) ev = [-ev[0], -ev[1]];
  if (pat.flipU) eu = [-eu[0], -eu[1]];
  if (pat.flipV) ev = [-ev[0], -ev[1]];
  const oa = num(pat.offA), ob = num(pat.offB);
  const O = [A[0] + oa * e1[0] + ob * e2[0], A[1] + oa * e1[1] + ob * e2[1]];
  return {
    O, eu, ev, e1, e2, A,
    toL: p => { const dx = p[0] - O[0], dy = p[1] - O[1]; return [dx * eu[0] + dy * eu[1], dx * ev[0] + dy * ev[1]]; },
    toW: q => [O[0] + q[0] * eu[0] + q[1] * ev[0], O[1] + q[0] * eu[1] + q[1] * ev[1]],
    vecW: q => [q[0] * eu[0] + q[1] * ev[0], q[0] * eu[1] + q[1] * ev[1]],
  };
}
function frameFor(G, P) {
  const g = G.g, n = g.n, r = clamp(num(P.refWall) | 0, 0, n - 1), L = G.lay;
  const A = L[g.wIdx[r]], B = L[g.wIdx[(r + 1) % n]];
  const e1 = dist(A, B) > 1 ? unitV(A, B) : [1, 0];
  return makeFrame(A, e1, inwardOf(e1, g.sgn), P);
}

/* ================= генераторы (u — вдоль, v — поперёк) ================= */
const mkRect = (u0, v0, L, W, kind, row, id) => ({ id, poly: [[u0, v0], [u0 + L, v0], [u0 + L, v0 + W], [u0, v0 + W]], kind, row, fr: { o: [u0, v0], x: [1, 0], y: [0, 1], L, W }, fa: L * W });
function genBond(bb, L, W, g, shiftOf) {
  const Lp = L + g, Wp = W + g, out = [];
  const k0 = Math.floor(bb.v0 / Wp) - 1, k1 = Math.ceil(bb.v1 / Wp) + 1;
  for (let k = k0; k <= k1; k++) {
    const s = shiftOf(k), v0 = k * Wp + g / 2;
    const j0 = Math.floor((bb.u0 - s) / Lp) - 1, j1 = Math.ceil((bb.u1 - s) / Lp) + 1;
    for (let j = j0; j <= j1; j++) out.push(mkRect(s + j * Lp + g / 2, v0, L, W, 'R', k, 'b' + k + '_' + j));
  }
  return out;
}
const circDist = (a, b, P) => Math.min(mod(a - b, P), mod(b - a, P));
function randShifts(k0, k1, Lp, minS, seed) {
  const m = new Map(), h = (k, t) => hash01(k * 7919 + t * 104729 + seed * 15485863);
  const pick = (k, prev) => { for (let t = 0; t < 32; t++) { const c = h(k, t) * Lp; if (circDist(c, prev, Lp) >= minS) return c; } return mod(prev + Lp / 2, Lp); };
  m.set(0, h(0, 0) * Lp);
  for (let k = 1; k <= Math.max(k1, 0); k++) m.set(k, pick(k, m.get(k - 1)));
  for (let k = -1; k >= Math.min(k0, 0); k--) m.set(k, pick(k, m.get(k + 1)));
  return k => m.has(k) ? m.get(k) : 0;
}
function genHerring(bb, L, W, g, n) {
  const Lc = L + g, Wc = n * (W + g), r = Math.SQRT1_2, vs = (Lc - Wc / 2) * r;
  const toUV = (x, y) => [(x + y) * r, (y - x) * r + vs], X = [r, -r], Y = [r, r];
  let i0 = Infinity, i1 = -Infinity, j0 = Infinity, j1 = -Infinity;
  for (const [u, v] of [[bb.u0, bb.v0], [bb.u1, bb.v0], [bb.u1, bb.v1], [bb.u0, bb.v1]]) {
    const s = u / r, t = (v - vs) / r, x = (s - t) / 2, y = (s + t) / 2, i = (x + y) / (2 * Wc), j = (x - y) / (2 * Lc);
    i0 = Math.min(i0, i); i1 = Math.max(i1, i); j0 = Math.min(j0, j); j1 = Math.max(j1, j);
  }
  const mi = Math.ceil((Lc + Wc) / (2 * Wc)) + 1;
  i0 = Math.floor(i0) - mi; i1 = Math.ceil(i1) + mi; j0 = Math.floor(j0) - 2; j1 = Math.ceil(j1) + 2;
  const out = [];
  const mk = (x, y, vert, kind, id) => {
    const pts = vert ? [[x, y], [x + W, y], [x + W, y + L], [x, y + L]] : [[x, y], [x + L, y], [x + L, y + W], [x, y + W]];
    return { id, poly: pts.map(p => toUV(p[0], p[1])), kind, fr: { o: toUV(x, y), x: vert ? Y : X, y: vert ? X : Y, L, W }, fa: L * W };
  };
  for (let i = i0; i <= i1; i++) for (let j = j0; j <= j1; j++) {
    const px = i * Wc + j * Lc, py = i * Wc - j * Lc;
    for (let q = 0; q < n; q++) {
      out.push(mk(px + g / 2, py + g / 2 + q * (W + g), false, 'A', 'h' + i + '_' + j + '_' + q + 'A'));
      out.push(mk(px + Lc + g / 2 + q * (W + g), py + Wc - Lc + g / 2, true, 'B', 'h' + i + '_' + j + '_' + q + 'B'));
    }
  }
  return out;
}
function genChevron(bb, L, W, g, alphaDeg) {
  const a = alphaDeg * DEG, sa = Math.sin(a), ca = Math.cos(a);
  const Lc = L + g, e = (W + g) / sa, Sv = Lc * sa, dx = Lc * ca, out = [];
  const k0 = Math.floor(bb.v0 / Sv) - 1, k1 = Math.ceil(bb.v1 / Sv) + 1;
  for (let k = k0; k <= k1; k++) {
    const even = mod(k, 2) === 0, d = even ? [ca, sa] : [-ca, sa], base = even ? 0 : dx, fy = even ? [sa, -ca] : [sa, ca];
    const m0 = Math.floor((bb.u0 - base - Math.abs(dx) - e) / e) - 1, m1 = Math.ceil((bb.u1 - base + Math.abs(dx)) / e) + 1;
    for (let m = m0; m <= m1; m++) {
      const A = [m * e + base, k * Sv], B = [A[0] + e, A[1]], C = [B[0] + Lc * d[0], B[1] + Lc * d[1]], D = [A[0] + Lc * d[0], A[1] + Lc * d[1]];
      let poly = [A, B, C, D]; if (g > 0) poly = insetPoly(poly, g / 2);
      out.push({ id: 'c' + k + '_' + m, poly, kind: even ? 'A' : 'B', fr: { o: A, x: d, y: fy, L, W, shift: (even ? 1 : -1) * W * ca / sa }, fa: Math.abs(area(poly)) });
    }
  }
  return out;
}
function genBasket(bb, L, W, g) {
  const n = Math.max(1, Math.round((L + g) / (W + g))), B = L + g, pitch = B / n, w = pitch - g, out = [];
  const i0 = Math.floor(bb.u0 / B) - 1, i1 = Math.ceil(bb.u1 / B) + 1, j0 = Math.floor(bb.v0 / B) - 1, j1 = Math.ceil(bb.v1 / B) + 1;
  for (let i = i0; i <= i1; i++) for (let j = j0; j <= j1; j++) {
    const x0 = i * B, y0 = j * B, hor = mod(i + j, 2) === 0;
    for (let q = 0; q < n; q++) {
      const id = 'k' + i + '_' + j + '_' + q;
      if (hor) out.push(mkRect(x0 + g / 2, y0 + q * pitch + g / 2, L, w, 'A', undefined, id));
      else { const u = x0 + q * pitch + g / 2, v = y0 + g / 2; out.push({ id, poly: [[u, v], [u + w, v], [u + w, v + L], [u, v + L]], kind: 'B', fr: { o: [u, v], x: [0, 1], y: [1, 0], L, W: w }, fa: L * w }); }
    }
  }
  return out;
}
function scanPoly(poly, y) {
  const xs = [];
  for (let i = 0, n = poly.length; i < n; i++) { const a = poly[i], b = poly[(i + 1) % n]; if ((a[1] > y) !== (b[1] > y)) xs.push(a[0] + (y - a[1]) * (b[0] - a[0]) / (b[1] - a[1])); }
  xs.sort((p, q) => p - q); const out = [];
  for (let i = 0; i + 1 < xs.length; i += 2) out.push([xs[i], xs[i + 1]]);
  return out;
}
function mergeIv(ivs, tol) { ivs.sort((p, q) => p[0] - q[0]); const out = []; for (const iv of ivs) { const l = out[out.length - 1]; if (l && iv[0] <= l[1] + tol) l[1] = Math.max(l[1], iv[1]); else out.push(iv.slice()); } return out; }
function intersectIv(A, B) { const out = []; for (const a of A) for (const b of B) { const lo = Math.max(a[0], b[0]), hi = Math.min(a[1], b[1]); if (hi > lo) out.push([lo, hi]); } return out; }
function subtractIv(A, B) { let cur = A.map(x => x.slice()); for (const b of B) { const next = []; for (const a of cur) { if (b[1] <= a[0] || b[0] >= a[1]) { next.push(a); continue; } if (b[0] > a[0]) next.push([a[0], b[0]]); if (b[1] < a[1]) next.push([b[1], a[1]]); } cur = next; } return cur; }
/* занятые отрезки ряда v ∈ [va, vb] по всем областям, без дыр-вставок */
function rowIntervals(polys, va, vb, holes) {
  const ys = vb - va < 0.1 ? [(va + vb) / 2] : [va + 0.01, (va + vb) / 2, vb - 0.01];
  for (const p of polys) for (const q of p) if (q[1] > va + 0.02 && q[1] < vb - 0.02) ys.push(q[1] - 0.01, q[1] + 0.01);
  let ivs = [];
  for (const p of polys) for (const y of ys) ivs = ivs.concat(scanPoly(p, y));
  ivs = mergeIv(ivs, 1);
  if (holes && holes.length) {
    for (const h of holes) {
      let cov = null;
      for (const y of [va + 0.01, (va + vb) / 2, vb - 0.01]) { const iv = scanPoly(h, y); cov = cov === null ? iv : intersectIv(cov, iv); }
      if (cov && cov.length) ivs = subtractIv(ivs, cov);
    }
  }
  return ivs.filter(iv => iv[1] - iv[0] > 2);
}
/* «Палуба по остаткам»: ряд за рядом, обрезок с конца ряда начинает следующий */
function planRemnant(polys, holes, bb, M, P) {
  const L = M.L, W = M.W, g = M.g, kerf = M.kerf, Lp = L + g, Wp = W + g;
  const minP = clamp(num(P.minPiece, 300), 20, L), minS = clamp(num(P.minStag, 300), 0, L / 2);
  const pool = [], rows = [], raw = []; let boards = 0, prevJ = null;
  const take = len => {
    if (len >= L - 0.5) { boards++; return 'full'; }
    let bi = -1; for (let i = 0; i < pool.length; i++) if (pool[i] >= len - 0.01 && (bi < 0 || pool[i] < pool[bi])) bi = i;
    if (bi >= 0) { const c = pool.splice(bi, 1)[0], rest = c - len - kerf; if (rest >= minP) pool.push(rest); return 'pool'; }
    boards++; const rest = L - len - kerf; if (rest >= minP) pool.push(rest); return 'new';
  };
  const k0 = Math.floor(bb.v0 / Wp) - 1, k1 = Math.ceil(bb.v1 / Wp);
  for (let k = k0; k <= k1; k++) {
    const v0 = k * Wp + g / 2, v1 = v0 + W;
    if (v1 <= bb.v0 + 0.3 || v0 >= bb.v1 - 0.3) continue;
    const ivs = rowIntervals(polys, Math.max(v0, bb.v0), Math.min(v1, bb.v1), holes);
    if (!ivs.length) continue;
    const row = { k, v0, v1, segs: [] }, joints = [];
    ivs.forEach(([a, b], si) => {
      const span = b - a, seg = { a, b, items: [] };
      if (span <= L + 0.5) { const len = Math.min(span, L); seg.items.push({ u0: a, len, src: take(len), cut: len < L - 0.5 }); }
      else {
        const ev = p => {
          const rest = span - p - g; if (rest <= 0.5) return null;
          let n = Math.floor(rest / Lp + 1e-9), last = rest - n * Lp;
          if (last > L - 0.5) { n += 1; last = 0; } if (last < 0.5) last = 0;
          const js = []; for (let j = 0; j < n; j++) js.push(a + p + g / 2 + j * Lp); if (last > 0) js.push(a + p + g / 2 + n * Lp);
          let worst = Infinity; if (prevJ) for (const j1 of js) for (const j2 of prevJ) { const d = Math.abs(j1 - j2); if (d < worst) worst = d; }
          return { p, n, last, js, worst, okP: p >= minP - 0.01, okL: last === 0 || last >= minP - 0.01, okS: worst >= minS - 0.01 };
        };
        const cands = [];
        for (let i = pool.length - 1; i >= 0; i--) cands.push(Math.min(pool[i], L));
        cands.push(L);
        for (let p = Math.floor((L - 10) / 10) * 10; p >= minP; p -= 10) cands.push(p);
        let best = null, fallback = null;
        for (const p of cands) {
          const r = ev(p); if (!r) continue;
          if (r.okP && r.okL && r.okS) { best = r; break; }
          if (r.okP && r.okL && (!fallback || r.worst > fallback.worst)) fallback = r;
        }
        best = best || fallback || ev(L) || { p: L, n: 0, last: span - L - g > 0.5 ? span - L - g : 0, js: [] };
        seg.items.push({ u0: a, len: best.p, src: take(best.p), cut: best.p < L - 0.5 });
        let x = a + best.p + g;
        for (let j = 0; j < best.n; j++) { take(L); seg.items.push({ u0: x, len: L, src: 'full', cut: false }); x += Lp; }
        if (best.last > 0) seg.items.push({ u0: x, len: best.last, src: take(best.last), cut: true });
        joints.push(...best.js);
      }
      seg.items.forEach((it, ii) => {
        const pc = mkRect(it.u0, v0, it.len, W, 'R', k, 'r' + k + '_' + si + '_' + ii); pc.fa = L * W; pc.fr.L = L; pc.src = it.src;
        if (ii === 0 && it.cut && seg.items.length > 1) pc.fr.o = [it.u0 + it.len - L, v0]; // обрезок: пиленый торец к стене
        raw.push(pc);
      });
      row.segs.push(seg);
    });
    prevJ = joints; rows.push(row);
  }
  return { raw, rows, boards };
}

/* ================= участки укладки (units) ================= */
function unitKeys(S, geo) {
  const keys = [];
  if (S.rooms.some(r => !r.own && geo[r.id] && !geo[r.id].err)) keys.push('floor');
  for (const r of S.rooms) if (r.own && geo[r.id] && !geo[r.id].err) keys.push('room:' + r.id);
  for (const r of S.rooms) if (r.border && r.border.on && geo[r.id] && geo[r.id].sides) keys.push('border:' + r.id);
  for (const r of S.rooms) for (const ins of r.inserts || []) if (geo[r.id] && !geo[r.id].err) keys.push('ins:' + r.id + ':' + ins.id);
  return keys;
}
function regionsOf(G, rid) {
  const out = [{ poly: G.center, meta: { room: rid, type: 'center', outer: G.inner ? null : G.outer } }];
  for (const d of G.doors) out.push({ poly: d.poly, meta: { room: rid, type: 'door' } });
  return out;
}
function buildUnit(key, S, geo) {
  const tol = tolFor(S);
  if (key === 'floor') {
    const rooms = S.rooms.filter(r => !r.own && geo[r.id] && !geo[r.id].err); if (!rooms.length) return null;
    const P = S.floorPat, ref = rooms.find(r => r.id === P.refRoom) || rooms[0];
    const regions = [], subtract = [];
    for (const r of rooms) { regions.push(...regionsOf(geo[r.id], r.id)); for (const x of geo[r.id].inserts) subtract.push(x.rect); }
    return { key, kind: 'floor', name: rooms.length > 1 ? 'Общий рисунок (' + rooms.length + ' ' + plural(rooms.length, 'комната', 'комнаты', 'комнат') + ')' : 'Рисунок: ' + rooms[0].name, roomIds: rooms.map(r => r.id), refRoom: ref.id, P, mat: unitMat(S.mat, S), tol, parts: [{ frame: frameFor(geo[ref.id], P), regions, subtract }] };
  }
  const [k, rid, iid] = key.split(':'); const r = S.rooms.find(x => x.id === rid), G = geo[rid];
  if (!r || !G || G.err) return null;
  if (k === 'room') {
    if (!r.own) return null;
    return { key, kind: 'room', name: r.name + ': свой рисунок', roomIds: [rid], refRoom: rid, P: r.pat, mat: unitMat(r.mat, S), tol, parts: [{ frame: frameFor(G, r.pat), regions: regionsOf(G, rid), subtract: G.inserts.map(x => x.rect) }] };
  }
  if (k === 'border') {
    if (!r.border || !r.border.on || !G.sides) return null;
    const P = r.border.pat, parts = [];
    G.sides.forEach(sd => { if (sd) parts.push({ frame: makeFrame(sd.A, sd.e1, sd.e2, Object.assign({}, P, { dir: 'along', offB: 0, flipU: false, flipV: false })), regions: [{ poly: sd.poly, meta: { room: rid, type: 'side', wall: sd.wall } }], subtract: [] }); });
    return { key, kind: 'border', name: r.name + ': рамка', roomIds: [rid], refRoom: rid, P, mat: unitMat(r.border.mat, S), tol: 0.5, parts };
  }
  if (k === 'ins') {
    const ins = (r.inserts || []).find(x => x.id === iid), IG = G.inserts.find(x => x.ins.id === iid);
    if (!ins || !IG || IG.region.length < 3) return null;
    const idx = r.inserts.indexOf(ins) + 1;
    return { key, kind: 'ins', name: r.name + ': вставка ' + idx, roomIds: [rid], refRoom: rid, P: ins.pat, mat: unitMat(ins.mat, S), tol: 0.5, ins: IG, parts: [{ frame: makeFrame(IG.C, IG.a, IG.b, ins.pat), regions: [{ poly: IG.region, meta: { room: rid, type: 'ins' } }], subtract: [] }] };
  }
  return null;
}
function unitError(u) {
  const M = u.mat, pd = patDef(u.P.type);
  if (!(M.L >= 20 && M.W >= 20)) return 'Укажите размеры планки в миллиметрах (не меньше 20 мм).';
  if (M.L < M.W) return 'Длина планки меньше ширины — поменяйте их местами.';
  if (pd.group === 'herring' && pd.n * (M.W + M.g) >= M.L + M.g) return 'Для рисунка «' + pd.name + '» длина планки должна быть больше ' + pd.n + ' × ширина.';
  let A = 0; for (const part of u.parts) for (const r of part.regions) A += Math.abs(area(r.poly));
  const est = A / (M.L * M.W); if (est > 30000) return 'Слишком много элементов (' + Math.round(est) + '). Проверьте, что размеры планки в миллиметрах.';
  return null;
}
function genRaw(pd, bb, M, P, polysL, holesL) {
  const alpha = clamp(num(P.chevAngle, 45), 15, 75);
  if (pd.group === 'bond') {
    if (pd.id === 'remnant') return planRemnant(polysL, holesL, bb, M, P);
    if (pd.id === 'random') { const Wp = M.W + M.g; return { raw: genBond(bb, M.L, M.W, M.g, randShifts(Math.floor(bb.v0 / Wp) - 1, Math.ceil(bb.v1 / Wp) + 1, M.L + M.g, clamp(num(P.minStag, 300), 0, M.L / 2), num(P.seed, 1) | 0)) }; }
    return { raw: genBond(bb, M.L, M.W, M.g, k => mod(k * pd.frac * (M.L + M.g), M.L + M.g)) };
  }
  if (pd.group === 'herring') return { raw: genHerring(bb, M.L, M.W, M.g, pd.n) };
  if (pd.group === 'chevron') return { raw: genChevron(bb, M.L, M.W, M.g, alpha) };
  return { raw: genBasket(bb, M.L, M.W, M.g) };
}
/* раскладка одного участка: генерация, вычитание вставок, обрезка по контуру */
function computeUnit(u, light, analyze) {
  const res = { unit: u, err: unitError(u), pieces: [], plans: [] };
  if (res.err) return res;
  const M = u.mat, P = u.P, pd = patDef(P.type), tol = u.tol;
  u.parts.forEach((part, pi) => {
    const F = part.frame;
    const regs = part.regions.map(r => { const L = r.poly.map(F.toL); return { L, bb: bboxOf(L), outerL: r.meta.outer ? r.meta.outer.map(F.toL) : null, meta: r.meta }; });
    const subL = part.subtract.map(p => p.map(F.toL));
    const bb = bbUnion(regs.map(r => r.bb));
    const g = genRaw(pd, bb, M, P, regs.map(r => r.L), subL);
    if (g.rows) res.plans.push({ part: pi, rows: g.rows, boards: g.boards });
    for (const pc of g.raw) {
      const pb = bboxOf(pc.poly); if (!bbHit(pb, bb)) continue;
      let shapes = [pc.poly];
      for (const s of subL) { shapes = shapes.flatMap(x => convexMinus(x, s)); if (!shapes.length) break; }
      if (!shapes.length) continue;
      const parts = []; let a = 0;
      for (const r of regs) {
        if (!bbHit(pb, r.bb)) continue;
        for (const sh of shapes) {
          const sb = shapes.length === 1 ? pb : bboxOf(sh); if (!bbHit(sb, r.bb)) continue;
          const c = [(sb.u0 + sb.u1) / 2, (sb.v0 + sb.v1) / 2]; let rad = 0; for (const q of sh) rad = Math.max(rad, dist(q, c));
          let poly;
          if (minEdgeDist(c[0], c[1], r.L) > rad + 0.01) { if (!inPoly(c[0], c[1], r.L)) continue; poly = sh; }
          else { poly = clipBy(r.L, sh); if (poly.length < 3) continue; }
          const pa = Math.abs(area(poly)); if (pa < 1) continue;
          parts.push({ poly, reg: r }); a += pa;
        }
      }
      if (!parts.length || a < 4) continue;
      let full = a >= pc.fa * 0.9995;
      if (!full && shapes.length === 1 && shapes[0] === pc.poly) {
        for (const p of parts) { const o = p.reg.outerL; if (!o) continue; const po = clipBy(o, pc.poly); if (po.length >= 3 && Math.abs(area(po)) >= pc.fa * 0.9995) { full = true; break; } }
      }
      let thick = 0;
      if (!full) { for (const p of parts) thick = Math.max(thick, thickOf(p.poly)); if (thick < tol) continue; }
      res.pieces.push({ id: pi + ':' + pc.id, part: pi, kind: pc.kind, row: pc.row, src: pc.src, fr: pc.fr, raw: pc.poly, parts: parts.map(p => p.poly), full, area: a, fa: pc.fa, thick, F });
    }
  });
  const thr = num(P.minEdge, 25); let bad = 0, pen = 0, cuts = 0, minT = Infinity;
  for (const p of res.pieces) if (!p.full) { cuts++; if (p.thick < minT) minT = p.thick; if (p.thick < thr) { bad++; pen += (thr - p.thick) / thr; } }
  res.score = bad * 100 + pen * 10 + cuts * 0.3 - Math.min(cuts ? minT : 0, thr * 3) * 0.1; res.bad = bad; res.minT = minT; res.cuts = cuts;
  if (!light && analyze) analyze(res);
  return res;
}

/* ================= подрезка планки ================= */
function plankPts(p, poly) { const o = p.fr.o, fx = p.fr.x, fy = p.fr.y; return (poly || p.parts[0]).map(q => { const dx = q[0] - o[0], dy = q[1] - o[1]; return [dx * fx[0] + dy * fx[1], dx * fy[0] + dy * fy[1]]; }); }
function plankOutline(fr) { const L = fr.L, W = fr.W, s = fr.shift || 0; return [[0, 0], [L, 0], [L + s, W], [s, W]]; }
function mainPart(p) { let best = p.parts[0], ba = -1; for (const q of p.parts) { const a = Math.abs(area(q)); if (a > ba) { ba = a; best = q; } } return best; }
function cutSpec(p) {
  const fr = p.fr, L = fr.L, W = fr.W;
  if (p.full) return { lines: ['Целая планка ' + mm(L) + ' × ' + mm(W) + ' мм'], key: 'full', ext: L };
  const pts = plankPts(p, mainPart(p)), out = plankOutline(fr), n = pts.length;
  let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
  for (const q of pts) { minX = Math.min(minX, q[0]); maxX = Math.max(maxX, q[0]); minY = Math.min(minY, q[1]); maxY = Math.max(maxY, q[1]); }
  const width = maxY - minY;
  const ext = y0 => { let lo = Infinity, hi = -Infinity; for (let i = 0; i < n; i++) { const a = pts[i], b = pts[(i + 1) % n]; if (Math.abs(a[1] - y0) < 0.6 && Math.abs(b[1] - y0) < 0.6) { lo = Math.min(lo, a[0], b[0]); hi = Math.max(hi, a[0], b[0]); } } return hi > lo + 0.5 ? hi - lo : 0; };
  const e0 = ext(0), eW = ext(W), lines = [], cutAng = [];
  for (let i = 0; i < n; i++) {
    const a = pts[i], b = pts[(i + 1) % n]; if (dist(a, b) < 1) continue;
    let fac = false; for (let k = 0; k < 4; k++) if (onLine(a, b, out[k], out[(k + 1) % 4], 0.6)) { fac = true; break; }
    if (fac) continue;
    let ang = Math.abs(Math.atan2(b[1] - a[1], b[0] - a[0]) / DEG); if (ang > 90) ang = 180 - ang; cutAng.push(Math.round(ang));
  }
  const rip = cutAng.some(a => a <= 1), cross = cutAng.some(a => a >= 89), obl = [...new Set(cutAng.filter(a => a > 1 && a < 89))].sort((x, y) => x - y);
  if (e0 && eW) {
    if (Math.abs(e0 - eW) < 1) lines.push('Длина ' + mm(e0) + ' мм' + (fr.shift && !obl.length ? ' (торец как заводской)' : cross && !obl.length ? ', рез 90°' : ''));
    else lines.push('По кромкам ' + mm(Math.max(e0, eW)) + ' и ' + mm(Math.min(e0, eW)) + ' мм');
  } else if (e0 || eW) {
    const e = e0 || eW;
    if (rip && !obl.length) lines.push('Распил вдоль: ширина ' + mm(width) + ' мм, длина ' + mm(e) + ' мм');
    else if (n === 3) lines.push('Треугольник: по кромке ' + mm(e) + ' мм, высота ' + mm(width) + ' мм');
    else lines.push('По кромке ' + mm(e) + ' мм, ширина ' + mm(width) + ' мм');
  } else lines.push('Кусок ' + mm(maxX - minX) + ' × ' + mm(width) + ' мм');
  if (obl.length) lines.push('Косой рез ' + obl.map(a => a + '°').join(', '));
  if (n > 5 || p.parts.length > 1) lines.push('Сложная форма — режьте по чертежу');
  return { lines, key: p.kind + '|' + lines.join('|'), ext: maxX - minX };
}

const E = {
  DEG, clamp, mod, num, mm, f1, fm2, dist, plural, hash01,
  area, perim, inPoly, segDist, minEdgeDist, bboxOf, bbHit, bbUnion, centroid, centroidMany, dedupe, clipHalf, clipBy, convexMinus, insetPoly, thickOf, onLine,
  CATS, catById, TONES, PATTERNS, patDef, BORDER_PATTERNS, TEMPLATES, rectWalls,
  defaultPat, defBorder, newRoom, newId, defaultState, migrateState,
  arcPts, arcRadius, arcLength, sagittaFromRadius, roomGeom, wallsFromCorners, innerAngles, unitV, inwardOf, unitMat, tolFor, roomLay, doorRect, insertGeom, computeGeo,
  dirDeg, makeFrame, frameFor,
  mkRect, genBond, randShifts, genHerring, genChevron, genBasket, scanPoly, rowIntervals, planRemnant,
  unitKeys, buildUnit, unitError, genRaw, computeUnit,
  plankPts, plankOutline, mainPart, cutSpec,
};
root.RazmerEngine = E;
if (typeof module !== 'undefined' && module.exports) module.exports = E;
})(typeof self !== 'undefined' ? self : globalThis);
