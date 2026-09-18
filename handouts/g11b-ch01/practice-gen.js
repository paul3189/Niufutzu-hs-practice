/* ══════════════════════════════════════════════════════════════
   g11b-ch01 空間概念與空間向量・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示                         p：參數與結構化答案（給 verify_gen11b1.py 獨立重算）
   同時可在瀏覽器（window.PGEN）與 Node（module.exports）使用。
   ══════════════════════════════════════════════════════════════ */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.PGEN = factory();
}(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  function makeRng(seed) {
    var s = (seed === undefined) ? (Date.now() % 2147483647) : (seed % 2147483647);
    if (s <= 0) s += 2147483646;
    var r = function () { s = (s * 16807) % 2147483647; return (s - 1) / 2147483646; };
    r.int = function (lo, hi) { return lo + Math.floor(r() * (hi - lo + 1)); };
    r.nz = function (lo, hi) { var v; do { v = r.int(lo, hi); } while (v === 0); return v; };
    r.pick = function (arr) { return arr[Math.floor(r() * arr.length)]; };
    r.sign = function () { return r() < 0.5 ? -1 : 1; };
    r.shuffle = function (arr) { var a = arr.slice(); for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(r() * (i + 1)), t = a[i]; a[i] = a[j]; a[j] = t; } return a; };
    return r;
  }
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function F(n, d) { if (d === undefined) d = 1; if (d < 0) { n = -n; d = -d; } var g = gcd(n, d) || 1; return { n: n / g, d: d / g }; }
  var Fr = {
    add: function (x, y) { return F(x.n * y.d + y.n * x.d, x.d * y.d); },
    sub: function (x, y) { return F(x.n * y.d - y.n * x.d, x.d * y.d); },
    mul: function (x, y) { return F(x.n * y.n, x.d * y.d); },
    div: function (x, y) { return F(x.n * y.d, x.d * y.n); },
    eq: function (x, y) { return x.n * y.d === y.n * x.d; },
    tex: function (x, small) {
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function fr2(f) { return [f.n, f.d]; }
  function simpSqrt(n) { var c = 1, r = n; for (var k = 2; k * k <= r; k++) { while (r % (k * k) === 0) { r /= k * k; c *= k; } } return { c: c, r: r }; }
  function sqrtTex(n) { if (n === 0) return '0'; var s = simpSqrt(n); if (s.r === 1) return String(s.c); return (s.c === 1 ? '' : s.c) + '\\sqrt{' + s.r + '}'; }
  /* √(n/d)（n,d 正整數）化簡成 (c√r)/d' */
  function sqrtFracTex(n, d, neg) {
    if (n === 0) return '0';
    var g = gcd(n, d); n /= g; d /= g;
    var s = simpSqrt(n * d), c = s.c, r = s.r;              /* √(n/d) = √(nd)/d */
    var g2 = gcd(c, d); c /= g2; var dd = d / g2;
    var body = (c === 1 ? (r === 1 ? '1' : '') : c) + (r === 1 ? '' : '\\sqrt{' + r + '}');
    if (r === 1) body = String(c);
    var t = dd === 1 ? body : '\\dfrac{' + body + '}{' + dd + '}';
    return (neg ? '-' : '') + t;
  }
  /* num·√rad / den */
  function radTex(num, rad, den) {
    if (num === 0) return '0';
    var s = simpSqrt(rad); num *= s.c; rad = s.r;
    var g = gcd(Math.abs(num), den); num /= g; den /= g;
    var body = (Math.abs(num) === 1 ? '' : Math.abs(num)) + (rad === 1 ? (Math.abs(num) === 1 ? '1' : '') : '\\sqrt{' + rad + '}');
    if (rad === 1) body = String(Math.abs(num));
    return (num < 0 ? '-' : '') + (den === 1 ? body : '\\dfrac{' + body + '}{' + den + '}');
  }
  function T(s) { return '$' + s + '$'; }
  function term(coef, v, first) {
    if (coef === 0) return '';
    var sgn = coef < 0 ? '-' : (first ? '' : '+');
    var ab = Math.abs(coef);
    return sgn + (ab === 1 && v ? '' : ab) + v;
  }
  /* ── 三維向量工具 ── */
  function vt(v) { return '(' + v[0] + ',' + v[1] + ',' + v[2] + ')'; }
  function vtF(v) { return '\\left(' + Fr.tex(v[0]) + ',\\ ' + Fr.tex(v[1]) + ',\\ ' + Fr.tex(v[2]) + '\\right)'; }
  function add(u, v) { return [u[0] + v[0], u[1] + v[1], u[2] + v[2]]; }
  function sub(u, v) { return [u[0] - v[0], u[1] - v[1], u[2] - v[2]]; }
  function sc(k, v) { return [k * v[0], k * v[1], k * v[2]]; }
  function dot(u, v) { return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]; }
  function cross(u, v) { return [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]]; }
  function n2(v) { return dot(v, v); }
  function det3(a, b, c) { return dot(a, cross(b, c)); }
  function ov(s) { return '\\overrightarrow{' + s + '}'; }
  function vec(s) { return '\\vec ' + s; }
  function comb(k, s, first) { if (k === 0) return ''; var sgn = k < 0 ? '-' : (first ? '' : '+'), ab = Math.abs(k); return sgn + (ab === 1 ? '' : ab) + s; }
  function rv(r, lo, hi) { return [r.nz(lo, hi), r.nz(lo, hi), r.nz(lo, hi)]; }
  function rp(r, lo, hi) { return [r.int(lo, hi), r.int(lo, hi), r.int(lo, hi)]; }
  function isZero(v) { return v[0] === 0 && v[1] === 0 && v[2] === 0; }
  function parallel(u, v) { return isZero(cross(u, v)); }
  var AXES = ['x', 'y', 'z'], PLANES = ['xy', 'yz', 'zx'];
  var QUAD = [[1, 2, 2], [2, 3, 6], [1, 4, 8], [4, 4, 7], [2, 6, 9], [3, 4, 12], [2, 10, 11], [6, 6, 7], [3, 6, 6], [2, 2, 1], [4, 8, 1], [6, 2, 3]];   /* 整數長度的向量 */
  function quad(r) { var q = r.pick(QUAD); q = r.shuffle(q); return [q[0] * r.sign(), q[1] * r.sign(), q[2] * r.sign()]; }
  function octant(P) {
    var x = P[0] > 0, y = P[1] > 0, z = P[2] > 0;
    var up = [[true, true], [false, true], [false, false], [true, false]];        /* I..IV: (x>0,y>0),(x<0,y>0),(x<0,y<0),(x>0,y<0) */
    for (var i = 0; i < 4; i++) if (up[i][0] === x && up[i][1] === y) return z ? i + 1 : i + 5;
    return 0;
  }
  var CN = ['', '一', '二', '三', '四', '五', '六', '七', '八'];

  /* ── patch_gen_11b1 新增工具（優化 #7 提示、#6 題幹、#3 排版） ── */
  /* 乘積一律寫成「括號並列」：(3)(-2)、\left(\dfrac12\right)(4)。
     好處是因數剛好等於 1 時也不會印出 1\cdot（排版掃描會當成「係數 1 沒省略」）。 */
  function hxPar(s) { s = String(s); return s.indexOf('\\') >= 0 ? '\\left(' + s + '\\right)' : '(' + s + ')'; }
  function hxPr(list) { return list.map(hxPar).join(''); }
  /* 平方：負數自動補括號；平方和 */
  function hxSq(v) { return (Number(v) < 0 ? '(' + v + ')' : String(v)) + '^2'; }
  function hxN2(u) { return u.map(function (v) { return hxSq(v); }).join('+'); }
  /* 內積展開成三項乘積 */
  function hxDot(u, v) { return [0, 1, 2].map(function (i) { return hxPr([u[i], v[i]]); }).join('+'); }
  /* 二階行列式 */
  function hxD2(a, b, c, d) { return '\\begin{vmatrix}' + a + '&' + b + '\\\\' + c + '&' + d + '\\end{vmatrix}'; }
  /* 外積三個分量對應的二階行列式（中間那個還要再加負號） */
  function hxCr(u, v) { return [hxD2(u[1], u[2], v[1], v[2]), hxD2(u[0], u[2], v[0], v[2]), hxD2(u[0], u[1], v[0], v[1])]; }
  /* 3x3 數字行列式 */
  function hxM3(M) { return '\\begin{vmatrix}' + M.map(function (row) { return row.join('&'); }).join('\\\\') + '\\end{vmatrix}'; }
  /* 一次組合：[[2,'s'],[-1,'t']] → 2s-t（係數全為 0 就寫 0） */
  function hxLin(pairs) { var s = ''; pairs.forEach(function (pr) { s += term(pr[0], pr[1], s === ''); }); return s === '' ? '0' : s; }
  /* 平行六面體：頂點相對 A 的三稜組合（(1,1,0) → AB+AD） */
  function hxVC(c) { var s = ''; [ov('AB'), ov('AD'), ov('AE')].forEach(function (nm, i) { s += comb(c[i], nm, s === ''); }); return s === '' ? '\\vec 0' : s; }
  /* ── patch_gen_11b1 新增工具結束 ── */
  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* 2-1 卦限與各種距離 */
  L1.octantDist = function (r) {
    var P = rv(r, -9, 9), ax = r.int(0, 2), pl = r.int(0, 2);
    var toAx = n2(P) - P[ax] * P[ax], toPl = Math.abs(P[[2, 0, 1][pl]]);
    var rest = [0, 1, 2].filter(function (i) { return i !== ax; }), miss = AXES[[2, 0, 1][pl]];
    return { q: '設 ' + T('P' + vt(P)) + '。(1) ' + T('P') + ' 在第幾卦限？(2) 求 ' + T('\\overline{OP}') + '。(3) 求 ' + T('P') + ' 到 ' + T(AXES[ax]) + ' 軸的距離。(4) 求 ' + T('P') + ' 到 ' + T(PLANES[pl]) + ' 平面的距離。',
             a: '(1) 第' + CN[octant(P)] + '卦限　(2) ' + T(sqrtTex(n2(P))) + '　(3) ' + T(sqrtTex(toAx)) + '　(4) ' + T(String(toPl)),
             h: '(1) 先看 ' + T('z=' + P[2]) + '：' + (P[2] > 0 ? '為正 ⟹ 落在上半（第一～四卦限）' : '為負 ⟹ 落在下半（第五～八卦限）') + '，再由 ' + T('(x,y)=(' + P[0] + ',' + P[1] + ')') + ' 的象限決定編號。(2) ' + T('\\overline{OP}^2=' + hxN2(P)) + '，加完再開根號。(3) 到 ' + T(AXES[ax]) + ' 軸的距離「把 ' + T(AXES[ax]) + ' 丟掉」：平方等於 ' + T(hxSq(P[rest[0]]) + '+' + hxSq(P[rest[1]])) + '。(4) 到 ' + T(PLANES[pl]) + ' 平面的距離只看缺席的那個坐標 ' + T(miss) + ' 的絕對值。',
             p: { P: P, ax: ax, pl: pl, ans: { oct: octant(P), r2: n2(P), ax2: toAx, pl: toPl } } };
  };

  /* 2-2 對稱點與投影點 */
  L1.symProj = function (r) {
    var P = rv(r, -9, 9), tgts = ['$xy$ 平面', '$yz$ 平面', '$zx$ 平面', '$x$ 軸', '$y$ 軸', '$z$ 軸', '原點'];
    var i = r.int(0, 6), j = r.int(0, 5);
    function sym(P, k) { var Q = P.slice(); if (k === 0) Q[2] = -Q[2]; else if (k === 1) Q[0] = -Q[0]; else if (k === 2) Q[1] = -Q[1]; else if (k === 3) { Q[1] = -Q[1]; Q[2] = -Q[2]; } else if (k === 4) { Q[0] = -Q[0]; Q[2] = -Q[2]; } else if (k === 5) { Q[0] = -Q[0]; Q[1] = -Q[1]; } else Q = sc(-1, Q); return Q; }
    function proj(P, k) { var Q = P.slice(); if (k === 0) Q[2] = 0; else if (k === 1) Q[0] = 0; else if (k === 2) Q[1] = 0; else if (k === 3) { Q[1] = 0; Q[2] = 0; } else if (k === 4) { Q[0] = 0; Q[2] = 0; } else { Q[0] = 0; Q[1] = 0; } return Q; }
    var S = sym(P, i), Q = proj(P, j);
    var FLIP = [[2], [0], [1], [1, 2], [0, 2], [0, 1], [0, 1, 2]], ZERO = [[2], [0], [1], [1, 2], [0, 2], [0, 1]];
    var nm = function (k) { return T(AXES[k] + '=' + P[k]); };
    return { q: '設 ' + T('P' + vt(P)) + '。(1) 求 ' + T('P') + ' 對' + (i === 6 ? '' : ' ') + tgts[i] + '的對稱點。(2) 求 ' + T('P') + ' 在 ' + tgts[j] + '上的投影點。(3) 求 (1) 的對稱點與 ' + T('P') + ' 的距離。',
             a: '(1) ' + T(vt(S)) + '　(2) ' + T(vt(Q)) + '　(3) ' + T(sqrtTex(n2(sub(S, P)))),
             h: '(1) 對' + (i === 6 ? '' : ' ') + tgts[i] + '對稱，要變號的坐標是 ' + FLIP[i].map(nm).join('、') + '，其餘不動。(2) 投影到 ' + tgts[j] + '，要歸零的坐標是 ' + ZERO[j].map(nm).join('、') + '。(3) 對稱點與 ' + T('P') + ' 只在剛才變號的那幾個坐標上不同，每一個的差都是該坐標的兩倍；把這些差的平方加起來再開根號。',
             p: { P: P, i: i, j: j, ans: { S: S, Q: Q, d2: n2(sub(S, P)) } } };
  };

  /* 2-3 分點與中點 */
  L1.midDiv = function (r) {
    var A = rv(r, -8, 8), B; do { B = rv(r, -8, 8); } while (isZero(sub(A, B)));
    var m = r.int(1, 4), n = r.int(1, 4); if (m === n) n += 1;
    var g0 = gcd(m, n); m /= g0; n /= g0;                          /* 2:4 → 1:2 */
    var AB = sub(B, A);
    var P = [F(n * A[0] + m * B[0], m + n), F(n * A[1] + m * B[1], m + n), F(n * A[2] + m * B[2], m + n)];
    var M = [F(A[0] + B[0], 2), F(A[1] + B[1], 2), F(A[2] + B[2], 2)];
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '。(1) 求 ' + T('\\overline{AB}') + ' 與中點 ' + T('M') + '。(2) 求 ' + T('\\overline{AB}') + ' 上滿足 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + ' 的點 ' + T('P') + '。',
             a: '(1) ' + T('\\overline{AB}=' + sqrtTex(n2(sub(B, A)))) + '，' + T('M' + vtF(M)) + '　(2) ' + T('P' + vtF(P)),
             h: '(1) ' + T(ov('AB') + '=' + vt(AB)) + '，' + T('\\overline{AB}^2=' + hxN2(AB)) + '；中點取兩點坐標的平均。(2) 內分 ' + T(m + ':' + n) + ' 要「交叉配」：' + T('P=\\dfrac{' + term(n, 'A', true) + term(m, 'B', false) + '}{' + (m + n) + '}') + '——離 ' + T('A') + ' 近的權重給 ' + T('A') + '；例如 ' + T('x') + ' 坐標 ' + T('=\\dfrac{' + hxPr([n, A[0]]) + '+' + hxPr([m, B[0]]) + '}{' + (m + n) + '}') + '。',
             p: { A: A, B: B, m: m, n: n, ans: { d2: n2(sub(B, A)), M: M.map(fr2), P: P.map(fr2) } } };
  };

  /* 2-4 重心反求頂點 */
  L1.centroidC = function (r) {
    var A = rv(r, -7, 7), B = rv(r, -7, 7), C = rv(r, -7, 7), G = [F(A[0] + B[0] + C[0], 3), F(A[1] + B[1] + C[1], 3), F(A[2] + B[2] + C[2], 3)];
    var D = rv(r, -7, 7), G4 = [F(A[0] + B[0] + C[0] + D[0], 4), F(A[1] + B[1] + C[1] + D[1], 4), F(A[2] + B[2] + C[2] + D[2], 4)];
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，' + T('\\triangle ABC') + ' 的重心為 ' + T('G' + vtF(G)) + '。(1) 求 ' + T('C') + '。(2) 若 ' + T('D' + vt(D)) + '，求四面體 ' + T('ABCD') + ' 的重心（四頂點坐標的平均）。',
             a: '(1) ' + T('C' + vt(C)) + '　(2) ' + T(vtF(G4)),
             h: '(1) 由 ' + T('G=\\dfrac{A+B+C}{3}') + ' 反解 ' + T('C=3G-A-B') + '，三個坐標各算一次：' + T('x') + ' 坐標 ' + T('=3\\cdot\\left(' + Fr.tex(G[0], true) + '\\right)' + term(-A[0], '', false) + term(-B[0], '', false)) + '。(2) 四面體重心 ' + T('=\\dfrac{A+B+C+D}{4}') + '，' + T('D' + vt(D)) + ' 已知，' + T('C') + ' 用 (1) 的結果代進去。',
             p: { A: A, B: B, G: G.map(fr2), D: D, ans: { C: C, G4: G4.map(fr2) } } };
  };

  /* 2-5 坐標軸上與兩點等距的點 */
  L1.equidistAxis = function (r) {
    var A = rv(r, -6, 6), B, ax = r.int(0, 2);
    do { B = rv(r, -6, 6); } while (B[ax] === A[ax] || isZero(sub(A, B)));
    /* P 在軸上：t 為軸坐標。|PA|²=|PB|² ⟹ (t-A_ax)² + rest_A = (t-B_ax)² + rest_B */
    var restA = n2(A) - A[ax] * A[ax], restB = n2(B) - B[ax] * B[ax];
    var t = F(n2(B) - n2(A), 2 * (B[ax] - A[ax]));
    var PA2 = Fr.add(Fr.mul(Fr.sub(t, F(A[ax])), Fr.sub(t, F(A[ax]))), F(restA));
    var Pt = [F(0), F(0), F(0)]; Pt[ax] = t;
    var expand = function (X) { return [0, 1, 2].map(function (k) { return k === ax ? (X[k] === 0 ? 't^2' : '(t' + term(-X[k], '', false) + ')^2') : hxSq(X[k]); }).join('+'); };
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '。求 ' + T(AXES[ax]) + ' 軸上與 ' + T('A') + '、' + T('B') + ' 等距離的點 ' + T('P') + '，並求 ' + T('\\overline{PA}^2') + '。',
             a: T('P' + vtF(Pt)) + '，' + T('\\overline{PA}^2=' + Fr.tex(PA2)),
             h: '設 ' + T('P') + ' 的 ' + T(AXES[ax]) + ' 坐標為 ' + T('t') + '、其餘為 ' + T('0') + '，則 ' + T('\\overline{PA}^2=' + expand(A)) + '、' + T('\\overline{PB}^2=' + expand(B)) + '；令兩者相等，' + T('t^2') + ' 相消後只剩 ' + T('t') + ' 的一次方程式。',
             p: { A: A, B: B, ax: ax, ans: { t: fr2(t), PA2: fr2(PA2) } } };
  };

  /* 2-6 長方體：體對角線、與底面夾角、與稜夾角 */
  L1.boxGeom = function (r) {
    var a = r.int(2, 9), b = r.int(2, 9), c = r.int(2, 9), s = a * a + b * b + c * c;
    var cosBase = sqrtFracTex(a * a + b * b, s), cosAB = sqrtFracTex(a * a, s);
    return { q: '長方體 ' + T('ABCD') + '-' + T('EFGH') + ' 中 ' + T('\\overline{AB}=' + a) + '、' + T('\\overline{AD}=' + b) + '、' + T('\\overline{AE}=' + c) + '。(1) 求體對角線 ' + T('\\overline{AG}') + '。(2) 求 ' + T('\\overline{AG}') + ' 與底面 ' + T('ABCD') + ' 所夾角的餘弦值。(3) 求 ' + T('\\overline{AG}') + ' 與稜 ' + T('\\overline{AB}') + ' 所夾角的餘弦值。',
             a: '(1) ' + T(sqrtTex(s)) + '　(2) ' + T(cosBase) + '　(3) ' + T(cosAB),
             h: '取 $A$ 為原點，$\\overrightarrow{AG}=(' + a + ',' + b + ',' + c + ')$；它在底面的投影是 $\\overrightarrow{AC}=(' + a + ',' + b + ',0)$，$\\cos=\\dfrac{|\\overrightarrow{AC}|}{|\\overrightarrow{AG}|}$；與 $\\overrightarrow{AB}$ 的夾角用內積。',
             p: { a: a, b: b, c: c, ans: { s: s, cos2base: [a * a + b * b, s], cos2AB: [a * a, s] } } };
  };

  /* 2-7 坐標化解最小值（將軍飲馬：異側） */
  L1.minSum = function (r) {
    var a = r.int(-7, 7), b = r.int(-7, 7), c = r.int(-7, 7), d = r.int(-7, 7), p = r.int(1, 8), q = r.int(1, 8);
    var A = [a, b, p], B = [c, d, -q], D2 = n2(sub(A, B));
    function sq(v, k) { return k === 0 ? v + '^2' : '(' + v + term(-k, '', false) + ')^2'; }   /* k=0 時寫 x^2，不寫 (x)^2 */
    return { q: '設 ' + T('x,y') + ' 為實數，求 ' + T('\\sqrt{' + sq('x', a) + '+' + sq('y', b) + '+' + (p * p) + '}+\\sqrt{' + sq('x', c) + '+' + sq('y', d) + '+' + (q * q) + '}') + ' 的最小值。',
             a: T(sqrtTex(D2)),
             h: '把 $' + (p * p) + '$ 看成 $' + p + '^2$、$' + (q * q) + '$ 看成 $(-' + q + ')^2$：式子是 $xy$ 平面上的動點到 $A' + vt(A) + '$ 與 $B' + vt(B) + '$ 的距離和；兩點在平面異側，最小值就是 $\\overline{AB}$。',
             p: { A: A, B: B, ans: D2 } };
  };

  /* 3-1 向量基本運算 */
  L1.vecOps3 = function (r) {
    var a = rv(r, -6, 6), b = rv(r, -6, 6), k1 = r.pick([2, 3, -2]), k2 = r.pick([1, -1, 2, -3]);
    var c = add(sc(k1, a), sc(k2, b)), na = n2(a);
    var s = simpSqrt(na), gu = gcd(gcd(gcd(a[0], a[1]), a[2]), s.c);   /* (1/(2√14))(-2,-6,4) → (1/√14)(-1,-3,2) */
    var unit = s.r === 1 ? vtF([F(a[0], s.c), F(a[1], s.c), F(a[2], s.c)]) : '\\dfrac{1}{' + (s.c / gu === 1 ? '' : s.c / gu) + '\\sqrt{' + s.r + '}}' + vt(a.map(function (v) { return v / gu; }));
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '。(1) 求 ' + T(comb(k1, vec('a'), true) + comb(k2, vec('b'), false)) + '。(2) 求 ' + T('|' + vec('a') + '|') + ' 與 ' + T('|' + vec('a') + '+' + vec('b') + '|') + '。(3) 求與 ' + T(vec('a')) + ' 同向的單位向量。',
             a: '(1) ' + T(vt(c)) + '　(2) ' + T(sqrtTex(na)) + '、' + T(sqrtTex(n2(add(a, b)))) + '　(3) ' + T(unit),
             h: '(1) 分量各自算，例如 ' + T('x') + ' 分量 ' + T('=' + hxPr([k1, a[0]]) + '+' + hxPr([k2, b[0]])) + '。(2) ' + T('|\\vec a|^2=' + hxN2(a)) + '；先把 ' + T('\\vec a+\\vec b=' + vt(add(a, b))) + ' 加出來再算平方和。(3) 單位向量 ' + T('=\\dfrac{\\vec a}{|\\vec a|}') + '，分子的公因數與根號外的係數要一起約掉。',
             p: { a: a, b: b, k1: k1, k2: k2, ans: { c: c, na: na, nab: n2(add(a, b)) } } };
  };

  /* 3-2 平行：待定分量 */
  L1.parallel3 = function (r) {
    var b = rv(r, -5, 5), k = r.pick([2, 3, -2, -3, -1]), a = sc(k, b), i = r.int(0, 2), j = (i + 1) % 3;
    var kf = F(k), kk = 3 - i - j;
    return { q: '若 ' + T('(' + [0, 1, 2].map(function (t) { return t === i ? 'm' : t === j ? 'n' : String(a[t]); }).join(',') + ')\\parallel' + vt(b)) + '，求 ' + T('m') + '、' + T('n') + ' 與 ' + T('m+n') + '。',
             a: T('m=' + a[i]) + '、' + T('n=' + a[j]) + '，' + T('m+n=' + (a[i] + a[j])),
             h: '平行 ⟹ 分量成比例。兩邊都是數字的是第 ' + (kk + 1) + ' 個分量：' + T(String(a[kk])) + ' 與 ' + T(String(b[kk])) + '，由它們的比先定出倍數 ' + T('k') + '；再把 ' + T('k') + ' 乘上 ' + T(vt(b)) + ' 剩下的兩個分量 ' + T(String(b[i])) + '、' + T(String(b[j])) + '，就是 ' + T('m') + '、' + T('n') + '。',
             p: { b: b, k: k, i: i, j: j, known: a[3 - i - j], ans: { m: a[i], n: a[j] } } };
  };

  /* 3-3 三點共線：反求坐標 */
  L1.collinear3 = function (r) {
    var A = rv(r, -5, 5), d = rv(r, -4, 4), k = r.pick([2, 3, -1, -2, F(1, 2)]);
    var B = add(A, d), kf = typeof k === 'number' ? F(k) : k;
    var C = [Fr.add(F(A[0]), Fr.mul(kf, F(d[0]))), Fr.add(F(A[1]), Fr.mul(kf, F(d[1]))), Fr.add(F(A[2]), Fr.mul(kf, F(d[2])))];
    if (C.some(function (x) { return x.d !== 1; })) { kf = F(2); C = [F(A[0] + 2 * d[0]), F(A[1] + 2 * d[1]), F(A[2] + 2 * d[2])]; }
    var Cn = C.map(function (x) { return x.n; }), hide = r.int(0, 2);
    var AB = sub(B, A), kn = [0, 1, 2].filter(function (t) { return t !== hide; });
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C(' + [0, 1, 2].map(function (t) { return t === hide ? 'c' : String(Cn[t]); }).join(',') + ')') + ' 三點共線，求 ' + T('c') + '，並求 ' + T('\\overrightarrow{AC}=k\\,\\overrightarrow{AB}') + ' 中的 ' + T('k') + '。',
             a: T('c=' + Cn[hide]) + '，' + T('k=' + Fr.tex(kf)),
             h: '共線 ⟺ ' + T(ov('AC') + '\\parallel' + ov('AB')) + '。先算 ' + T(ov('AB') + '=' + vt(AB)) + '；' + T(ov('AC')) + ' 已知的兩個分量是 ' + kn.map(function (u) { return T(String(Cn[u] - A[u])); }).join(' 與 ') + '，拿其中一個與 ' + T(ov('AB')) + ' 的同一個分量相比就得到 ' + T('k') + '；最後由第 ' + (hide + 1) + ' 個分量 ' + T('c' + term(-A[hide], '', false) + '=k\\cdot' + hxPar(AB[hide])) + ' 解出 ' + T('c') + '。',
             p: { A: A, B: B, C: Cn, hide: hide, ans: { c: Cn[hide], k: fr2(kf) } } };
  };

  /* 3-4 係數和判別法：分點 */
  L1.divCoef = function (r) {
    var A = rv(r, -6, 6), B; do { B = rv(r, -6, 6); } while (isZero(sub(A, B)));
    var m = r.int(1, 4), n = r.int(1, 4); if (m === n) n += 1;
    var g0 = gcd(m, n); m /= g0; n /= g0;                          /* 答案的比要最簡 */
    function cf(v, first) { var one = v.d === 1 && Math.abs(v.n) === 1; return (v.n < 0 ? (one ? '-' : '') : (first ? '' : '+')) + (one ? '' : Fr.tex(v) + '\\,'); }   /* 係數 ±1 不印 1 */
    var ext = r() < 0.4;                                          /* 外分：AP:PB = m:n，P 在直線上但不在線段上 */
    var x = ext ? F(-n, m - n) : F(n, m + n), y = ext ? F(m, m - n) : F(m, m + n);   /* OP = x OA + y OB */
    var P = [Fr.add(Fr.mul(x, F(A[0])), Fr.mul(y, F(B[0]))), Fr.add(Fr.mul(x, F(A[1])), Fr.mul(y, F(B[1]))), Fr.add(Fr.mul(x, F(A[2])), Fr.mul(y, F(B[2])))];
    return { q: '設 ' + T('O') + ' 為原點，' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，且 ' + T(ov('OP') + '=' + cf(x, true) + ov('OA') + cf(y, false) + ov('OB')) + '。(1) 說明 ' + T('P') + ' 在直線 ' + T('AB') + ' 上，並求 ' + T('P') + ' 的坐標。(2) ' + T('P') + ' 在線段 ' + T('\\overline{AB}') + ' 上嗎？求 ' + T('\\overline{AP}:\\overline{PB}') + '。',
             a: '(1) 係數和 ' + T(Fr.tex(x, true) + (y.n < 0 ? '' : '+') + Fr.tex(y, true) + '=1') + '，' + T('P' + vtF(P)) + '　(2) ' + (ext ? '不在線段上（外分）' : '在線段上（內分）') + '，' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n),
             h: '係數和 ' + T(Fr.tex(x, true) + (y.n < 0 ? '' : '+') + Fr.tex(y, true) + '=1') + ' ⟹ ' + T('P') + ' 在直線 ' + T('AB') + ' 上；把係數乘進坐標即可，例如 ' + T('x') + ' 坐標 ' + T('=' + hxPr([Fr.tex(x, true), A[0]]) + '+' + hxPr([Fr.tex(y, true), B[0]])) + '。兩個係數的正負決定 ' + T('P') + ' 在不在線段內部（兩個都是正的才在內部）；' + T('\\overline{AP}:\\overline{PB}=|y|:|x|') + '（' + T('B') + ' 的係數對應 ' + T('\\overline{AP}') + '），最後要約成最簡整數比。',
             p: { A: A, B: B, x: fr2(x), y: fr2(y), ans: { P: P.map(fr2), m: m, n: n, ext: ext } } };
  };

  /* 3-5 共平面：線性組合的係數 */
  L1.coplanarComb = function (r) {
    var u, v; do { u = rv(r, -4, 4); v = rv(r, -4, 4); } while (parallel(u, v));
    var p = r.nz(-3, 3), q = r.nz(-3, 3), w = add(sc(p, u), sc(q, v));
    return { q: '設 ' + T(vec('u') + '=' + vt(u)) + '、' + T(vec('v') + '=' + vt(v)) + '、' + T(vec('w') + '=' + vt(w)) + '。(1) 判斷三者是否共平面。(2) 若共平面，把 ' + T(vec('w')) + ' 寫成 ' + T('p\\,' + vec('u') + '+q\\,' + vec('v')) + '。',
             a: '(1) 共平面（' + T('\\det(\\vec u,\\vec v,\\vec w)=0') + '）　(2) ' + T('(p,q)=(' + p + ',' + q + ')'),
             h: '三個分量各給一條方程式：' + [0, 1, 2].map(function (i) { return T(hxLin([[u[i], 'p'], [v[i], 'q']]) + '=' + w[i]); }).join('、') + '；兩個未知數用前兩條解出來，第三條拿來驗算（驗得過就共平面，也就是 ' + T('\\det(\\vec u,\\vec v,\\vec w)=0') + '）。',
             p: { u: u, v: v, w: w, ans: { p: p, q: q } } };
  };

  /* 3-6 四點共平面反求坐標 */
  L1.fourCoplanar = function (r) {
    var A = rv(r, -4, 4), B = rv(r, -4, 4), C = rv(r, -4, 4), s = r.nz(-2, 2), t = r.nz(-2, 2);
    if (isZero(sub(B, A))) B = add(B, [1, 1, 1]);
    var AB = sub(B, A), AC = sub(C, A);
    if (parallel(AB, AC)) { C = add(C, [1, 2, 0]); AC = sub(C, A); if (parallel(AB, AC)) C = add(C, [0, 0, 3]); AC = sub(C, A); }
    var D = add(A, add(sc(s, AB), sc(t, AC))), hide = r.int(0, 2);
    var nABC = cross(AB, AC); while (nABC[hide] === 0) hide = (hide + 1) % 3;   /* 法向量在被藏的方向分量為 0 ⟹ 平面平行該軸、k 任意；換一個坐標藏 */
    var kn = [0, 1, 2].filter(function (i) { return i !== hide; });
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '、' + T('D(' + [0, 1, 2].map(function (i) { return i === hide ? 'k' : String(D[i]); }).join(',') + ')') + ' 四點共平面，求 ' + T('k') + '，並把 ' + T(ov('AD')) + ' 寫成 ' + T('s\\,' + ov('AB') + '+t\\,' + ov('AC')) + '。',
             a: T('k=' + D[hide]) + '，' + T('(s,t)=(' + s + ',' + t + ')'),
             h: '先算 ' + T(ov('AB') + '=' + vt(AB)) + '、' + T(ov('AC') + '=' + vt(AC)) + '。四點共平面 ⟺ ' + T(ov('AD') + '=s\\,' + ov('AB') + '+t\\,' + ov('AC')) + '：用不含 ' + T('k') + ' 的兩個分量列式 ' + kn.map(function (i) { return T(hxLin([[AB[i], 's'], [AC[i], 't']]) + '=' + (D[i] - A[i])); }).join('、') + '，解出 ' + T('s') + '、' + T('t') + ' 之後再代回含 ' + T('k') + ' 的那一條。',
             p: { A: A, B: B, C: C, D: D, hide: hide, ans: { k: D[hide], s: s, t: t } } };
  };

  /* 3-7 三角不等式 */
  L1.triIneq3 = function (r) {
    var la = r.int(2, 9), lb = r.int(2, 9), lo = Math.abs(la - lb), hi = la + lb, m = r.int(lo, hi);
    var dotv = F(m * m - la * la - lb * lb, 2);
    return { q: '設 ' + T('|\\vec a|=' + la) + '、' + T('|\\vec b|=' + lb) + '。(1) 求 ' + T('|\\vec a+\\vec b|') + ' 的範圍。(2) 若又知 ' + T('|\\vec a+\\vec b|=' + m) + '，求 ' + T('\\vec a\\cdot\\vec b') + '。',
             a: '(1) ' + T(lo + '\\le|\\vec a+\\vec b|\\le' + hi) + '　(2) ' + T('\\vec a\\cdot\\vec b=' + Fr.tex(dotv)),
             h: '(1) 三角不等式 ' + T('\\big||\\vec a|-|\\vec b|\\big|\\le|\\vec a+\\vec b|\\le|\\vec a|+|\\vec b|') + '：本題兩個長度是 ' + T(String(la)) + ' 與 ' + T(String(lb)) + '，下界取兩者之差的絕對值、上界取兩者之和。(2) 求長度先平方：' + T('|\\vec a+\\vec b|^2=|\\vec a|^2+2\\vec a\\cdot\\vec b+|\\vec b|^2') + '，代進去就是 ' + T(hxSq(m) + '=' + hxSq(la) + '+2\\vec a\\cdot\\vec b+' + hxSq(lb)) + '，移項就解得出內積。',
             p: { la: la, lb: lb, m: m, ans: { lo: lo, hi: hi, dot: fr2(dotv) } } };
  };

  /* 3-8 三向量和的長度（夾角 60/90/120） */
  L1.sumLen = function (r) {
    var l = [r.int(1, 5), r.int(1, 5), r.int(1, 5)], degs = [r.pick([60, 90, 120]), r.pick([60, 90, 120]), r.pick([60, 90, 120])];
    var cs = { 60: F(1, 2), 90: F(0), 120: F(-1, 2) };
    var CT = { 60: '\\dfrac{1}{2}', 90: '0', 120: '-\\dfrac{1}{2}' };
    var s2 = F(l[0] * l[0] + l[1] * l[1] + l[2] * l[2]);
    s2 = Fr.add(s2, Fr.mul(F(2 * l[0] * l[1]), cs[degs[0]])); s2 = Fr.add(s2, Fr.mul(F(2 * l[1] * l[2]), cs[degs[1]])); s2 = Fr.add(s2, Fr.mul(F(2 * l[2] * l[0]), cs[degs[2]]));
    var seen = {}, used = [];
    degs.forEach(function (d) { if (!seen[d]) { seen[d] = 1; used.push(T('\\cos' + d + '^\\circ=' + CT[d])); } });
    return { q: '設 ' + T('|\\vec a|=' + l[0]) + '、' + T('|\\vec b|=' + l[1]) + '、' + T('|\\vec c|=' + l[2]) + '，且 ' + T('\\vec a,\\vec b') + ' 夾 ' + T(degs[0] + '^\\circ') + '、' + T('\\vec b,\\vec c') + ' 夾 ' + T(degs[1] + '^\\circ') + '、' + T('\\vec c,\\vec a') + ' 夾 ' + T(degs[2] + '^\\circ') + '。求 ' + T('|\\vec a+\\vec b+\\vec c|') + '。',
             a: T(sqrtTex(s2.n) + (s2.d === 1 ? '' : '\\ \\text{（即 }\\sqrt{' + Fr.tex(s2, true) + '}\\text{）}')),
             h: '求長度先平方：' + T('|\\vec a+\\vec b+\\vec c|^2=' + hxN2(l) + '+2(\\vec a\\cdot\\vec b+\\vec b\\cdot\\vec c+\\vec c\\cdot\\vec a)') + '；三個內積分別是 ' + T(hxPr([l[0], l[1]]) + '\\cos' + degs[0] + '^\\circ') + '、' + T(hxPr([l[1], l[2]]) + '\\cos' + degs[1] + '^\\circ') + '、' + T(hxPr([l[2], l[0]]) + '\\cos' + degs[2] + '^\\circ') + '，而 ' + used.join('、') + '。加完再開根號。',
             p: { l: l, degs: degs, ans: fr2(s2) } };
  };

  /* 4-1 內積與夾角 */
  L1.dotAngle3 = function (r) {
    var a = rv(r, -5, 5), b = rv(r, -5, 5), d = dot(a, b), na = n2(a), nb = n2(b);
    var cosT = d === 0 ? '0' : sqrtFracTex(d * d, na * nb, d < 0);
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '。(1) 求 ' + T('\\vec a\\cdot\\vec b') + '。(2) 求夾角的餘弦值，並判斷夾角是銳角、直角或鈍角。(3) 求 ' + T('|' + vec('a') + '+' + vec('b') + '|^2') + '。',
             a: '(1) ' + T(String(d)) + '　(2) ' + T('\\cos\\theta=' + cosT) + '，' + (d > 0 ? '銳角' : d < 0 ? '鈍角' : '直角') + '　(3) ' + T(String(na + nb + 2 * d)),
             h: '(1) 內積是三組分量相乘再相加：' + T('\\vec a\\cdot\\vec b=' + hxDot(a, b)) + '。(2) ' + T('|\\vec a|^2=' + hxN2(a)) + '、' + T('|\\vec b|^2=' + hxN2(b)) + '，再套 ' + T('\\cos\\theta=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec a||\\vec b|}') + '；正負號完全由內積決定（正是銳角、負是鈍角、零是直角）。(3) ' + T('|\\vec a+\\vec b|^2=|\\vec a|^2+|\\vec b|^2+2\\vec a\\cdot\\vec b') + '。',
             p: { a: a, b: b, ans: { dot: d, cos2: [d * d, na * nb], nab: na + nb + 2 * d } } };
  };

  /* 4-2 垂直：待定係數 */
  L1.perpT = function (r) {
    var b = rv(r, -5, 5), a = [r.nz(-5, 5), r.nz(-5, 5), 0], i = r.int(0, 2); if (b[i] === 0) b[i] = 1;
    /* a[i] 未知 t：Σ a_j b_j + t b_i = 0 */
    var known = [0, 1, 2].filter(function (j) { return j !== i; }), s = 0;
    var av = rv(r, -5, 5); known.forEach(function (j) { s += av[j] * b[j]; });
    var t = F(-s, b[i]);
    var ss = '';
    for (var k = 0; k < 3; k++) {
      if (k === i) ss += term(b[k], 't', ss === '');
      else ss += (ss === '' ? '' : '+') + hxPr([av[k], b[k]]);
    }
    return { q: '若 ' + T('(' + [0, 1, 2].map(function (j) { return j === i ? 't' : String(av[j]); }).join(',') + ')\\perp' + vt(b)) + '，求 ' + T('t') + '。',
             a: T('t=' + Fr.tex(t)),
             h: '垂直 ⟺ 內積為 ' + T('0') + '。把兩個向量的三組分量乘開相加：' + T(ss + '=0') + '，整理之後就是 ' + T('t') + ' 的一次方程式，移項再除就得到 ' + T('t') + '。',
             p: { b: b, av: av, i: i, ans: fr2(t) } };
  };

  /* 4-3 同時垂直於兩向量的單位向量（外積） */
  L1.unitPerp = function (r) {
    var a, b, c; do { a = rv(r, -3, 3); b = rv(r, -3, 3); c = cross(a, b); } while (isZero(c));
    var g = gcd(gcd(Math.abs(c[0]), Math.abs(c[1])), Math.abs(c[2])) || 1, cr = sc(1 / g, c), nc = n2(cr);
    return { q: '求同時垂直於 ' + T(vec('a') + '=' + vt(a)) + ' 與 ' + T(vec('b') + '=' + vt(b)) + ' 的單位向量。',
             a: T('\\pm\\dfrac{1}{' + sqrtTex(nc) + '}' + vt(cr)),
             h: '先算 $\\vec a\\times\\vec b=' + vt(c) + '$（可約掉公因數），再除以長度；「同時垂直」永遠有正反兩個方向。',
             p: { a: a, b: b, ans: { dir: cr, nc: nc } } };
  };

  /* 4-4 正射影 */
  L1.proj3 = function (r) {
    var a = rv(r, -5, 5), b = rv(r, -4, 4), d = dot(a, b), nb = n2(b);
    var k = F(d, nb), pv = [Fr.mul(k, F(b[0])), Fr.mul(k, F(b[1])), Fr.mul(k, F(b[2]))];
    var lenT = d === 0 ? '0' : sqrtFracTex(d * d, nb, d < 0);
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '。求 ' + T(vec('a')) + ' 在 ' + T(vec('b')) + ' 上的正射影向量與正射影長。',
             a: '正射影向量 ' + T(vtF(pv)) + '，正射影長 ' + T(lenT),
             h: '先把兩個數字算出來：' + T('\\vec a\\cdot\\vec b=' + hxDot(a, b)) + '、' + T('|\\vec b|^2=' + hxN2(b)) + '。正射影向量 ' + T('=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|^2}\\vec b') + '（分母是平方，答案是向量）；正射影長 ' + T('=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|}') + '（只除一次，可以是負的）。',
             p: { a: a, b: b, ans: { k: fr2(k), len2: [d * d, nb], neg: d < 0 } } };
  };

  /* 4-5 柯西不等式 */
  L1.cauchy3 = function (r) {
    var a = r.nz(-6, 6), b = r.nz(-6, 6), c = r.nz(-6, 6), d = r.nz(-12, 12), s = a * a + b * b + c * c;
    var mn = F(d * d, s), k = F(d, s), P = [Fr.mul(k, F(a)), Fr.mul(k, F(b)), Fr.mul(k, F(c))];
    return { q: '設 ' + T('x,y,z') + ' 為實數且 ' + T(term(a, 'x', true) + term(b, 'y', false) + term(c, 'z', false) + '=' + d) + '，求 ' + T('x^2+y^2+z^2') + ' 的最小值，並求此時的 ' + T('(x,y,z)') + '。',
             a: '最小值 ' + T(Fr.tex(mn)) + '，此時 ' + T(vtF(P)),
             h: '柯西：$(x^2+y^2+z^2)(' + [a, b, c].map(function (v) { return v < 0 ? '(' + v + ')^2' : v + '^2'; }).join('+') + ')\\ge(' + term(a, 'x', true) + term(b, 'y', false) + term(c, 'z', false) + ')^2$，等號在 $(x,y,z)\\parallel' + vt([a, b, c]) + '$。',
             p: { a: a, b: b, c: c, d: d, ans: { mn: fr2(mn), P: P.map(fr2) } } };
  };

  /* 4-6 外積計算 */
  L1.cross3 = function (r) {
    var a, b, c; do { a = rv(r, -4, 4); b = rv(r, -4, 4); c = cross(a, b); } while (isZero(c));
    var dt = hxCr(a, b);
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '。(1) 求 ' + T('\\vec a\\times\\vec b') + '。(2) 求 ' + T('|\\vec a\\times\\vec b|') + '。(3) 驗證 ' + T('|\\vec a\\times\\vec b|^2+(\\vec a\\cdot\\vec b)^2=|\\vec a|^2|\\vec b|^2') + '。',
             a: '(1) ' + T(vt(c)) + '　(2) ' + T(sqrtTex(n2(c))) + '　(3) ' + T(n2(c) + '+' + (dot(a, b) * dot(a, b)) + '=' + (n2(a) * n2(b))) + ' ✓',
             h: '外積的三個分量各是一個二階行列式（把那一列遮住剩下的四個數字）：' + T('x') + ' 分量 ' + T('=' + dt[0]) + '、' + T('y') + ' 分量要「反過來減」' + T('=-' + dt[1]) + '、' + T('z') + ' 分量 ' + T('=' + dt[2]) + '。算完拿「與 ' + T('\\vec a') + '、' + T('\\vec b') + ' 的內積都是 ' + T('0') + '」檢查；(3) 用到 ' + T('\\vec a\\cdot\\vec b=' + hxDot(a, b)) + '、' + T('|\\vec a|^2=' + hxN2(a)) + '、' + T('|\\vec b|^2=' + hxN2(b)) + '。',
             p: { a: a, b: b, ans: { c: c, nc: n2(c) } } };
  };

  /* 4-7 三點決定的三角形面積 */
  L1.area3 = function (r) {
    var A, B, C, cr; do { A = rv(r, -4, 4); B = rv(r, -4, 4); C = rv(r, -4, 4); cr = cross(sub(B, A), sub(C, A)); } while (isZero(cr));
    var n = n2(cr), s = simpSqrt(n), areaT = s.c % 2 === 0 ? sqrtTex(n / 4) : '\\dfrac{' + sqrtTex(n) + '}{2}';
    var AB = sub(B, A), AC = sub(C, A), dt = hxCr(AB, AC);
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。(1) 求 ' + T(ov('AB') + '\\times' + ov('AC')) + '。(2) 求 ' + T('\\triangle ABC') + ' 的面積。',
             a: '(1) ' + T(vt(cr)) + '　(2) ' + T(areaT),
             h: '先把兩個邊向量算出來：' + T(ov('AB') + '=' + vt(AB)) + '、' + T(ov('AC') + '=' + vt(AC)) + '。外積的三個分量各是一個二階行列式：' + T('=' + dt[0]) + '、' + T('=-' + dt[1]) + '、' + T('=' + dt[2]) + '（中間那項反過來減）。面積 ' + T('=\\dfrac12|' + ov('AB') + '\\times' + ov('AC') + '|') + '；平行四邊形就不除 ' + T('2') + '。',
             p: { A: A, B: B, C: C, ans: { cr: cr, n: n } } };
  };

  /* 4-8 長方體的兩面角 */
  L1.dihedralBox = function (r) {
    var a = r.int(2, 8), b = r.int(2, 8), c = r.int(2, 8), which = r.int(0, 1);
    /* which=0：底面 ABCD 與平面 ABGH（含稜 AB）：cos = b/√(b²+c²)；which=1：底面與平面 ADGF（含稜 AD）：cos = a/√(a²+c²) */
    var cos2 = which === 0 ? [b * b, b * b + c * c] : [a * a, a * a + c * c];
    var plane = which === 0 ? 'ABGH' : 'ADGF';
    var edge = which === 0 ? 'AB' : 'AD', other = which === 0 ? 'AD' : 'AB', slant = which === 0 ? 'AH' : 'AF', up = which === 0 ? 'DH' : 'BF';
    var el = which === 0 ? b : a;
    return { q: '長方體 ' + T('ABCD') + '-' + T('EFGH') + ' 中 ' + T('\\overline{AB}=' + a) + '、' + T('\\overline{AD}=' + b) + '、' + T('\\overline{AE}=' + c) + '（' + T('ABCD') + ' 為底面、' + T('\\overline{AE}') + ' 鉛直）。求底面 ' + T('ABCD') + ' 與平面 ' + T(plane) + ' 所夾兩面角的餘弦值。',
             a: T(sqrtFracTex(cos2[0], cos2[1])),
             h: '以 ' + T('A') + ' 為原點，' + T(ov('AB') + '=' + vt([a, 0, 0])) + '、' + T(ov('AD') + '=' + vt([0, b, 0])) + '、' + T(ov('AE') + '=' + vt([0, 0, c])) + '。兩面角的稜是 ' + T('\\overline{' + edge + '}') + '，平面角就落在 ' + T('\\overline{' + other + '}') + ' 與 ' + T('\\overline{' + slant + '}') + ' 之間——它在直角三角形「' + T('\\overline{' + other + '}=' + el) + '、' + T('\\overline{' + up + '}=' + c) + '、斜邊 ' + T('\\overline{' + slant + '}') + '」裡，餘弦 ' + T('=\\dfrac{\\text{鄰邊}}{\\text{斜邊}}') + '。也可以用法向量：底面取 ' + T('(0,0,1)') + '，平面 ' + T(plane) + ' 的法向量用外積求。',
             p: { a: a, b: b, c: c, which: which, ans: cos2 } };
  };

  /* 5-1 三階行列式 */
  L1.det3calc = function (r) {
    var M = [rv(r, -5, 5), rv(r, -5, 5), rv(r, -5, 5)], d = det3(M[0], M[1], M[2]);
    var tex = '\\begin{vmatrix}' + M.map(function (row) { return row.join('&'); }).join('\\\\') + '\\end{vmatrix}';
    var g = function (i, j) { return M[i][j]; };
    return { q: '計算 ' + T(tex) + '。',
             a: T(String(d)),
             h: '沿第一列展開，或用「對角線法」：往右下的三項 ' + T(hxPr([g(0, 0), g(1, 1), g(2, 2)])) + '、' + T(hxPr([g(0, 1), g(1, 2), g(2, 0)])) + '、' + T(hxPr([g(0, 2), g(1, 0), g(2, 1)])) + ' 相加，往左下的三項 ' + T(hxPr([g(0, 2), g(1, 1), g(2, 0)])) + '、' + T(hxPr([g(0, 1), g(1, 0), g(2, 2)])) + '、' + T(hxPr([g(0, 0), g(1, 2), g(2, 1)])) + ' 相加，前者減後者。',
             p: { M: M, ans: d } };
  };

  /* 5-2 行列式性質：列的線性組合 */
  L1.detProps = function (r) {
    var p = r.nz(-3, 3), q = r.nz(-3, 3), s = r.nz(-3, 3), t = r.nz(-3, 3), k = p * t - q * s;
    if (k === 0) { t += 1; k = p * t - q * s; }
    var D = r.pick([2, 3, 5, -4, 6]), sw = r.int(0, 1);
    var row1 = comb(p, '\\vec a', true) + comb(q, '\\vec b', false), row2 = comb(s, '\\vec a', true) + comb(t, '\\vec b', false);
    return { q: '設 ' + T('\\det(\\vec a,\\vec b,\\vec c)=' + D) + '。(1) 求 ' + T('\\det(' + row1 + ',\\ ' + row2 + ',\\ \\vec c)') + '。(2) 求 ' + T(sw ? '\\det(\\vec c,\\vec b,\\vec a)' : '\\det(\\vec b,\\vec c,\\vec a)') + '。(3) 以 ' + T(row1) + '、' + T(row2) + '、' + T('\\vec c') + ' 為三邊的平行六面體體積是多少？',
             a: '(1) ' + T(String(k * D)) + '　(2) ' + T(String(sw ? -D : D)) + '　(3) ' + T(String(Math.abs(k * D))),
             h: '(1) 每一列都是線性的，而且有兩列相同就是 ' + T('0') + '，展開後只剩 ' + T('\\det(' + row1 + ',\\ ' + row2 + ',\\ \\vec c)=\\left(' + hxPr([p, t]) + '-' + hxPr([q, s]) + '\\right)\\det(\\vec a,\\vec b,\\vec c)') + '，而題目給了 ' + T('\\det(\\vec a,\\vec b,\\vec c)=' + D) + '。(2) 對調兩列變號、輪換三列不變：' + T(sw ? '\\det(\\vec c,\\vec b,\\vec a)' : '\\det(\\vec b,\\vec c,\\vec a)') + ' 是' + (sw ? '對調第一、三列' : '把三列輪換一次') + '。(3) 平行六面體體積就是 (1) 的絕對值。',
             p: { p: p, q: q, s: s, t: t, D: D, sw: sw, ans: { v1: k * D, v2: sw ? -D : D, v3: Math.abs(k * D) } } };
  };

  /* 5-3 平行六面體與四面體體積 */
  L1.volume3 = function (r) {
    var u, v, w, d; do { u = rv(r, -4, 4); v = rv(r, -4, 4); w = rv(r, -4, 4); d = det3(u, v, w); } while (d === 0);
    var dt = hxCr(v, w);
    return { q: '設 ' + T(vec('u') + '=' + vt(u)) + '、' + T(vec('v') + '=' + vt(v)) + '、' + T(vec('w') + '=' + vt(w)) + '。(1) 求三重積 ' + T('\\vec u\\cdot(\\vec v\\times\\vec w)') + '。(2) 求以三者為邊的平行六面體體積。(3) 求以三者為邊的四面體體積。',
             a: '(1) ' + T(String(d)) + '　(2) ' + T(String(Math.abs(d))) + '　(3) ' + T(Fr.tex(F(Math.abs(d), 6))),
             h: '三重積就是把 ' + T('\\vec u,\\vec v,\\vec w') + ' 依序排成三列的三階行列式。先算 ' + T('\\vec v\\times\\vec w') + ' 的三個分量 ' + T('=' + dt[0]) + '、' + T('=-' + dt[1]) + '、' + T('=' + dt[2]) + '，再與 ' + T('\\vec u=' + vt(u)) + ' 內積。平行六面體體積取絕對值，四面體再除以 ' + T('6') + '。',
             p: { u: u, v: v, w: w, ans: { d: d } } };
  };

  /* 5-4 牆角型：原點到平面的距離（體積法） */
  L1.ptPlaneAxes = function (r) {
    var a = r.int(1, 6), b = r.int(1, 6), c = r.int(1, 6), N = a * a * b * b + b * b * c * c + c * c * a * a;
    /* d = abc/√N */
    return { q: '設 ' + T('O') + ' 為原點、' + T('A(' + a + ',0,0)') + '、' + T('B(0,' + b + ',0)') + '、' + T('C(0,0,' + c + ')') + '。(1) 求四面體 ' + T('OABC') + ' 的體積。(2) 求 ' + T('\\triangle ABC') + ' 的面積。(3) 求 ' + T('O') + ' 到平面 ' + T('ABC') + ' 的距離。',
             a: '(1) ' + T(Fr.tex(F(a * b * c, 6))) + '　(2) ' + T(radTex(1, N, 2)) + '　(3) ' + T(sqrtFracTex(a * a * b * b * c * c, N)),
             h: '牆角型（三條稜互相垂直）：(1) ' + T('V=\\dfrac{1}{6}' + hxPr([a, b, c])) + '。(2) ' + T(ov('AB') + '\\times' + ov('AC') + '=(bc,\\ ca,\\ ab)=' + vt([b * c, c * a, a * b])) + '，' + T('\\triangle ABC') + ' 的面積是這個向量長度的一半。(3) 用體積法 ' + T('d=\\dfrac{3V}{S}') + '——本章不需要平面方程式。',
             p: { a: a, b: b, c: c, ans: { V: [a * b * c, 6], N: N, d2: [a * a * b * b * c * c, N] } } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 2-1 長方體兩條體對角線的夾角 */
  L2.lineFaceAngle = function (r) {
    var a = r.int(2, 8), b = r.int(2, 8), c = r.int(2, 8), which = r.int(0, 1);
    if ((which === 0 ? b * b - a * a : a * a - b * b) + c * c === 0) c += 1;   /* 兩條體對角線恰好垂直 ⟹「取銳角」不成立 */
    var AG = [a, b, c], BH = [-a, b, c], DF = [a, -b, c];
    var other = which === 0 ? BH : DF, name = which === 0 ? 'BH' : 'DF';
    var cosv = F(dot(AG, other), n2(AG));
    return { q: '長方體 ' + T('ABCD') + '-' + T('EFGH') + ' 中 ' + T('\\overline{AB}=' + a) + '、' + T('\\overline{AD}=' + b) + '、' + T('\\overline{AE}=' + c) + '。求兩條體對角線 ' + T('\\overline{AG}') + ' 與 ' + T('\\overline{' + name + '}') + ' 所夾角的餘弦值（取銳角）。',
             a: T(Fr.tex(F(Math.abs(cosv.n), cosv.d))),
             h: '取 $A$ 為原點：$\\overrightarrow{AG}=' + vt(AG) + '$、$\\overrightarrow{' + name + '}=' + vt(other) + '$，兩者長度相同，$\\cos=\\dfrac{\\text{內積}}{' + n2(AG) + '}$。',
             p: { a: a, b: b, c: c, which: which, ans: fr2(F(Math.abs(cosv.n), cosv.d)) } };
  };

  /* 2-2 係數就是坐標：到稜的距離 */
  L2.cubeCoefDist = function (r) {
    function inner() { var nn = r.int(1, 5), dd = r.int(2, 6); if (nn >= dd) dd = nn + 1; return F(nn, dd); }   /* 「P 在內部」⟹ 三個係數都要在 0 與 1 之間 */
    var x = inner(), y = inner(), z = inner();
    var which = r.int(0, 2), names = ['AB', 'AD', 'AE'], coords = [x, y, z];
    var rest = [0, 1, 2].filter(function (i) { return i !== which; });
    var d2 = Fr.add(Fr.mul(coords[rest[0]], coords[rest[0]]), Fr.mul(coords[rest[1]], coords[rest[1]]));
    var toPlane = coords[[2, 0, 1][which]];   /* 到平面 ABCD 的距離 = z；到平面 ABFE = y；到平面 ADHE = x */
    var pl = ['ABCD', 'ADHE', 'ABFE'][which];   /* 與 toPlane 同一個索引：z↔ABCD、x↔ADHE、y↔ABFE */
    return { q: '正立方體 ' + T('ABCD') + '-' + T('EFGH') + ' 的邊長為 ' + T('1') + '（' + T('ABCD') + ' 為底面、' + T('\\overline{AE}') + ' 鉛直），' + T('P') + ' 在其內部且 ' + T(ov('AP') + '=' + Fr.tex(x) + ov('AB') + '+' + Fr.tex(y) + ov('AD') + '+' + Fr.tex(z) + ov('AE')) + '。(1) 求 ' + T('P') + ' 到直線 ' + T(names[which]) + ' 的距離。(2) 求 ' + T('P') + ' 到平面 ' + T(pl) + ' 的距離。',
             a: '(1) ' + T(sqrtFracTex(d2.n, d2.d)) + '　(2) ' + T(Fr.tex(toPlane)),
             h: '以 $A$ 為原點、三稜為三軸，三個係數就是 $P$ 的坐標 $\\left(' + Fr.tex(x, true) + ',' + Fr.tex(y, true) + ',' + Fr.tex(z, true) + '\\right)$；到直線 $' + names[which] + '$（即某個坐標軸）的距離「把那個坐標丟掉」，到坐標平面的距離就是缺的那個坐標。',
             p: { x: fr2(x), y: fr2(y), z: fr2(z), which: which, ans: { d2: fr2(d2), pl: fr2(toPlane) } } };
  };

  /* 2-3 角平分線的方向 */
  L2.bisectorT = function (r) {
    var OB = quad(r), OA = quad(r); if (parallel(OA, OB)) OA = [OA[1], OA[2], OA[0]];
    var lb = Math.round(Math.sqrt(n2(OB))), la = Math.round(Math.sqrt(n2(OA)));
    var mult = r.pick([1, 2, 3]); OA = sc(mult, OA); la *= mult;
    var t = F(la, lb);
    return { q: '設 ' + T(ov('OA') + '=' + vt(OA)) + '、' + T(ov('OB') + '=' + vt(OB)) + '，且 ' + T(ov('OC') + '=' + ov('OA') + '+t\\,' + ov('OB')) + '（' + T('t\\gt0') + '）。若 ' + T(ov('OC')) + ' 平分 ' + T('\\angle AOB') + '，求 ' + T('t') + '。',
             a: T('t=' + Fr.tex(t)),
             h: '角平分線的方向 $=$ 兩個<b>單位</b>向量的和。先算長度：' + T('|' + ov('OA') + '|=' + la) + '、' + T('|' + ov('OB') + '|=' + lb) + '，所以一個平分方向是 ' + T('\\dfrac{' + ov('OA') + '}{' + la + '}+\\dfrac{' + ov('OB') + '}{' + lb + '}') + '。題目的 ' + T(ov('OC') + '=' + ov('OA') + '+t\\,' + ov('OB')) + ' 已經把 ' + T(ov('OA')) + ' 的係數定成 ' + T('1') + '，把上面那個方向整條乘 ' + T(String(la)) + ' 之後比對 ' + T(ov('OB')) + ' 的係數，就得到 ' + T('t') + '。',
             p: { OA: OA, OB: OB, ans: fr2(t) } };
  };

  /* 2-4 外角平分線交對邊 */
  L2.extBisector = function (r) {
    var A = rv(r, -5, 5), u = quad(r), v = quad(r); if (parallel(u, v)) v = [v[1], v[2], v[0]];
    var lu = Math.round(Math.sqrt(n2(u))), lv = Math.round(Math.sqrt(n2(v)));
    if (lu === lv) { u = sc(2, u); lu *= 2; }
    var B = add(A, u), C = add(A, v);
    /* 外分：QB:QC = AB:AC = lu:lv，Q = B + (lu/(lu-lv))(C-B) */
    var k = F(lu, lu - lv), Q = [Fr.add(F(B[0]), Fr.mul(k, F(C[0] - B[0]))), Fr.add(F(B[1]), Fr.mul(k, F(C[1] - B[1]))), Fr.add(F(B[2]), Fr.mul(k, F(C[2] - B[2])))];
    return { q: '空間中 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。若 ' + T('\\angle BAC') + ' 的外角平分線交直線 ' + T('BC') + ' 於 ' + T('Q') + '，求 ' + T('Q') + ' 的坐標。',
             a: T('Q' + vtF(Q)),
             h: '$\\overline{AB}=' + lu + '$、$\\overline{AC}=' + lv + '$；外角平分線<b>外分</b>對邊：$\\overline{QB}:\\overline{QC}=' + lu + ':' + lv + '$ ⟹ $Q=B+\\dfrac{' + lu + '}{' + lu + '-' + lv + '}\\,\\overrightarrow{BC}$。',
             p: { A: A, B: B, C: C, ans: Q.map(fr2) } };
  };

  /* 2-5 加權和為零向量 */
  L2.weightedZero = function (r) {
    var A = rv(r, -6, 6), B = rv(r, -6, 6), C = rv(r, -6, 6), al = r.nz(-4, 5), be = r.nz(-4, 5), ga = r.nz(-4, 5);
    var s = al + be + ga; if (s === 0) { ga += 1; s += 1; }
    var D = [F(al * A[0] + be * B[0] + ga * C[0], s), F(al * A[1] + be * B[1] + ga * C[1], s), F(al * A[2] + be * B[2] + ga * C[2], s)];
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。若 ' + T('D') + ' 滿足 ' + T(comb(al, ov('DA'), true) + comb(be, ov('DB'), false) + comb(ga, ov('DC'), false) + '=\\vec 0') + '，求 ' + T('D') + ' 的坐標。',
             a: T('D' + vtF(D)),
             h: '把每個 $\\overrightarrow{DX}$ 寫成 $X-D$：$' + term(al, 'A', true) + term(be, 'B', false) + term(ga, 'C', false) + '=(' + al + term(be, '', false) + term(ga, '', false) + ')D$，係數和 $' + s + '\\ne0$ 才能除過去。',
             p: { A: A, B: B, C: C, al: al, be: be, ga: ga, ans: D.map(fr2) } };
  };

  /* 2-6 鏡面反射 */
  L2.reflectPlane = function (r) {
    var P = rv(r, -5, 5), pl = r.int(0, 2), k = r.pick([1, 2, 3]);
    var dir = sc(-1, P); var refl = dir.slice(); refl[[2, 0, 1][pl]] = -refl[[2, 0, 1][pl]];
    var Rp = sc(k, refl);
    return { q: '空間坐標中，以 ' + T(PLANES[pl]) + ' 平面為鏡面。一光線通過 ' + T('P' + vt(P)) + ' 射向鏡面上的原點 ' + T('O') + '，反射後通過 ' + T('R') + '。若 ' + T('|' + ov('OR') + '|=' + k + '|' + ov('PO') + '|') + '，求 ' + T('R') + ' 的坐標。',
             a: T('R' + vt(Rp)),
             h: '入射方向 $\\overrightarrow{PO}=' + vt(dir) + '$；反射只把垂直鏡面的那個分量（$' + ['z', 'x', 'y'][pl] + '$）變號，再乘倍率 $' + k + '$。',
             p: { P: P, pl: pl, k: k, ans: Rp } };
  };

  /* 2-7 平行六面體中的面心 */
  L2.paraCenter = function (r) {
    /* #6：J 的位置 6 面＋體心共 7 種、(2) 的線段 8 條、(1) 的起點 A／G 兩種 ⟹ 112 種題幹 */
    var VC = { A: [0, 0, 0], B: [1, 0, 0], C: [1, 1, 0], D: [0, 1, 0], E: [0, 0, 1], F: [1, 0, 1], G: [1, 1, 1], H: [0, 1, 1] };
    var faces = [['BCGF', [F(1), F(1, 2), F(1, 2)]], ['DCGH', [F(1, 2), F(1), F(1, 2)]], ['EFGH', [F(1, 2), F(1, 2), F(1)]],
                 ['ABFE', [F(1, 2), F(0), F(1, 2)]], ['ADHE', [F(0), F(1, 2), F(1, 2)]], ['ABCD', [F(1, 2), F(1, 2), F(0)]]];
    var ci = r.int(0, 6);                                     /* 6 ＝ 整個平行六面體的中心 */
    var fname = ci === 6 ? '' : faces[ci][0];
    var J = ci === 6 ? [F(1, 2), F(1, 2), F(1, 2)] : faces[ci][1];
    var SEG = [['AG', [1, 1, 1]], ['EC', [1, 1, -1]], ['BH', [-1, 1, 1]], ['DF', [1, -1, 1]],
               ['CE', [-1, -1, 1]], ['HB', [1, -1, -1]], ['FD', [-1, 1, -1]], ['GA', [-1, -1, -1]]];
    var extra = r.int(0, 7), seg = SEG[extra];
    var kind = r.int(0, 1), from = kind === 0 ? 'A' : 'G', org = VC[from];
    var co = [Fr.sub(J[0], F(org[0])), Fr.sub(J[1], F(org[1])), Fr.sub(J[2], F(org[2]))];
    var jdesc = ci === 6 ? T('J') + ' 為此平行六面體的中心（兩條體對角線的交點）' : T('J') + ' 為面 ' + T(fname) + ' 的中心';
    var diag = ci === 6 ? ['A', 'G'] : (fname[0] === 'A' ? [fname[1], fname[3]] : [fname[0], fname[2]]);   /* 對角頂點不取 A，否則會印出 \overrightarrow{AA} */
    /* 頂點本身就是一條稜（B、D、E）時不寫 \overrightarrow{AB}=\overrightarrow{AB} 這種廢話 */
    var vshow = function (v) { var s = hxVC(VC[v]); return T(s === ov('A' + v) ? s : ov('A' + v) + '=' + s); };
    return { q: T('ABCD') + '-' + T('EFGH') + ' 為平行六面體（' + T('ABCD') + ' 為底面，' + T('\\overline{AE}') + ' 為側稜），' + jdesc + '。(1) 若 ' + T(ov(from + 'J') + '=a\\,' + ov('AB') + '+b\\,' + ov('AD') + '+c\\,' + ov('AE')) + '，求 ' + T('(a,b,c)') + '。(2) 把 ' + T(ov(seg[0])) + ' 用 ' + T(ov('AB') + ',' + ov('AD') + ',' + ov('AE')) + ' 表示。',
             a: '(1) ' + T('(a,b,c)=' + vtF(co)) + '　(2) ' + T(ov(seg[0]) + '=' + hxVC(seg[1])),
             h: '每個頂點都先寫成三稜的組合，例如 ' + T(ov('AG') + '=' + hxVC(VC.G)) + '。(1) ' + (ci === 6 ? '中心是體對角線 ' + T('\\overline{AG}') + ' 的中點' : '面心是該面對角線的中點：' + T(fname) + ' 的一組對角頂點是 ' + T(diag[0]) + ' 與 ' + T(diag[1]) + '，' + diag.map(vshow).join('、')) + '，取平均得 ' + T(ov('AJ')) + (kind === 0 ? '' : '；題目問的是從 ' + T('G') + ' 出發，再用 ' + T(ov('GJ') + '=' + ov('AJ') + '-' + ov('AG'))) + '。(2) ' + T(ov(seg[0]) + '=' + ov('A' + seg[0][1]) + '-' + ov('A' + seg[0][0])) + '，兩邊各自換成三稜的組合再相減。',
             p: { face: fname, extra: extra, kind: kind, ans: { co: co.map(fr2), seg: seg[1].map(function (v) { return fr2(F(v)); }), J: J.map(fr2) } } };
  };

  /* 2-8 含 x 的行列式：不展開就能知道的事 */
  L2.detPoly = function (r) {
    /* 每個元素是 e = u + v x（u,v 小整數，至多兩個非零 v）*/
    function pmul(A, B) { var C = []; for (var i = 0; i < A.length + B.length - 1; i++) C.push(0); for (var i2 = 0; i2 < A.length; i2++) for (var j = 0; j < B.length; j++) C[i2 + j] += A[i2] * B[j]; return C; }
    function padd(A, B, s) { var n = Math.max(A.length, B.length), C = []; for (var i = 0; i < n; i++) C.push((A[i] || 0) + s * (B[i] || 0)); return C; }
    var E, f;
    do {
      E = []; for (var i = 0; i < 3; i++) { E.push([]); for (var j = 0; j < 3; j++) E[i].push([r.int(-3, 3), r() < 0.45 ? r.nz(-2, 2) : 0]); }
      var m = function (i, j) { return E[i][j]; };
      var c = function (a, b) { return pmul(a, b); };
      f = padd(padd(c(m(0, 0), padd(c(m(1, 1), m(2, 2)), c(m(1, 2), m(2, 1)), -1)), c(m(0, 1), padd(c(m(1, 0), m(2, 2)), c(m(1, 2), m(2, 0)), -1)), -1), c(m(0, 2), padd(c(m(1, 0), m(2, 1)), c(m(1, 1), m(2, 0)), -1)), 1);
      while (f.length > 1 && f[f.length - 1] === 0) f.pop();
    } while (f.length < 3 || f[0] === 0);
    var ent = function (e) { var u = e[0], v = e[1]; var s = term(v, 'x', true) + term(u, '', v === 0); return s === '' ? '0' : s; };
    var tex = '\\begin{vmatrix}' + E.map(function (row) { return row.map(ent).join('&'); }).join('\\\\') + '\\end{vmatrix}';
    var f0 = f[0], f1 = f.reduce(function (s, v) { return s + v; }, 0), fm1 = f.reduce(function (s, v, i) { return s + v * (i % 2 ? -1 : 1); }, 0);
    var M0 = E.map(function (row) { return row.map(function (e) { return e[0]; }); });
    var M1 = E.map(function (row) { return row.map(function (e) { return e[0] + e[1]; }); });
    var MV = E.map(function (row) { return row.map(function (e) { return e[1]; }); });
    return { q: '設 ' + T('f(x)=' + tex) + '。(1) 求 ' + T('f(x)') + ' 的常數項。(2) 求 ' + T('f(x)') + ' 的各項係數和。(3) 求各偶次項係數和。(4) 求 ' + T('f(x)') + ' 的次數與領導係數。',
             a: '(1) ' + T(String(f0)) + '　(2) ' + T(String(f1)) + '　(3) ' + T(String((f1 + fm1) / 2)) + '　(4) ' + T((f.length - 1) + '\\text{ 次，領導係數 }' + f[f.length - 1]),
             h: '不要真的乘開：常數項 ' + T('=f(0)') + '、係數和 ' + T('=f(1)') + '、偶次項係數和 ' + T('=\\dfrac{f(1)+f(-1)}{2}') + '，每一個都只是代一個數字進去算一次三階行列式。本題 ' + T('f(0)=' + hxM3(M0)) + '、' + T('f(1)=' + hxM3(M1)) + '。次數與領導係數則看六支乘積裡 ' + T('x') + ' 的最高次——各元素的 ' + T('x') + ' 係數排起來是 ' + T(hxM3(MV)) + '，只有係數不為 ' + T('0') + ' 的位置才有貢獻。',
             p: { E: E, ans: { f0: f0, f1: f1, even: (f1 + fm1) / 2, deg: f.length - 1, lead: f[f.length - 1], poly: f } } };
  };

  /* 2-9 四面體體積與點到平面距離 */
  L2.tetraDist = function (r) {
    var A, B, C, D, d, cr; do { A = rv(r, -3, 3); B = rv(r, -3, 3); C = rv(r, -3, 3); D = rv(r, -3, 3); cr = cross(sub(B, A), sub(C, A)); d = dot(cr, sub(D, A)); } while (d === 0 || isZero(cr));
    var V = F(Math.abs(d), 6), h2 = [d * d, n2(cr)];
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '、' + T('D' + vt(D)) + '。(1) 求四面體 ' + T('ABCD') + ' 的體積。(2) 求 ' + T('D') + ' 到平面 ' + T('ABC') + ' 的距離。',
             a: '(1) ' + T(Fr.tex(V)) + '　(2) ' + T(sqrtFracTex(h2[0], h2[1])),
             h: '先把三個邊向量算出來：' + T(ov('AB') + '=' + vt(sub(B, A))) + '、' + T(ov('AC') + '=' + vt(sub(C, A))) + '、' + T(ov('AD') + '=' + vt(sub(D, A))) + '。(1) ' + T('V=\\dfrac16|\\det(' + ov('AB') + ',' + ov('AC') + ',' + ov('AD') + ')|') + '。(2) 底面積 ' + T('S=\\dfrac12|' + ov('AB') + '\\times' + ov('AC') + '|') + '，再用體積法 ' + T('h=\\dfrac{3V}{S}=\\dfrac{|\\det|}{|' + ov('AB') + '\\times' + ov('AC') + '|}') + '——本章不需要平面方程式。',
             p: { A: A, B: B, C: C, D: D, ans: { V: fr2(V), h2: h2 } } };
  };

  /* 2-10 平行四邊形的第四個頂點 */
  L2.fourthVertex = function (r) {
    var A, B, C; do { A = rv(r, -5, 5); B = rv(r, -5, 5); C = rv(r, -5, 5); } while (parallel(sub(B, A), sub(C, A)) || isZero(sub(B, A)) || isZero(sub(C, A)));
    var D1 = sub(add(A, C), B), D2 = sub(add(A, B), C), D3 = sub(add(B, C), A);
    return { q: '空間中 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。求所有能與 ' + T('A,B,C') + ' 構成平行四邊形的第四個頂點 ' + T('D') + '。',
             a: T(vt(D1)) + '、' + T(vt(D2)) + '、' + T(vt(D3)),
             h: '「誰跟誰是對角」有三種配法，對角線互相平分 ⟹ ' + T('D=A+C-B') + '、' + T('D=A+B-C') + '、' + T('D=B+C-A') + '，三個都要寫。例如第一種的 ' + T('x') + ' 坐標 ' + T('=' + A[0] + term(C[0], '', false) + term(-B[0], '', false)) + '，' + T('y') + '、' + T('z') + ' 同法。',
             p: { A: A, B: B, C: C, ans: [D1, D2, D3] } };
  };

  /* 2-11 正四面體的五個數字 */
  L2.regularTetra = function (r) {
    /* #6：邊長 10 種 × 問的量 7 種 × 第 (2) 小題 2 種問法 ⟹ 140 種題幹 */
    var a = r.pick([1, 2, 3, 4, 5, 6, 8, 9, 10, 12]), which = r.int(0, 6), q2 = r.int(0, 1);
    var items = [
      ['體高', radTex(a, 6, 3), [a, 6, 3]],                                        /* a√6/3 */
      ['體積', radTex(a * a * a, 2, 12), [a * a * a, 2, 12]],                       /* a³√2/12 */
      ['外接球半徑（頂點到中心的距離）', radTex(a, 6, 4), [a, 6, 4]],
      ['內切球半徑（中心到面的距離）', radTex(a, 6, 12), [a, 6, 12]],
      ['一個面上的高', radTex(a, 3, 2), [a, 3, 2]],                                 /* a√3/2 */
      ['一個面的外接圓半徑（該面重心到頂點的距離）', radTex(a, 3, 3), [a, 3, 3]],   /* a√3/3 */
      ['表面積', radTex(a * a, 3, 1), [a * a, 3, 1]]                                /* √3a² */
    ];
    var it = items[which];
    var ask2 = q2 === 0 ? '相鄰兩面所夾兩面角的餘弦值' : '側稜與底面所夾角的餘弦值';
    var ans2 = q2 === 0 ? '\\dfrac{1}{3}' : radTex(1, 3, 3);
    var note = which === 1 ? '（是 ' + T('a^3') + '）' : which === 6 ? '（是 ' + T('a^2') + '）' : '';
    var hint2 = q2 === 0
      ? '(2) 兩面角：取一條稜的中點，往兩個面內各連到對面的頂點，這兩條都是面上的高（長 ' + T('\\dfrac{\\sqrt{3}}{2}a') + '），而它們的另一端距離就是稜長 ' + T('a') + '，用一次餘弦定理即可（與邊長無關）。'
      : '(2) 側稜與底面的夾角落在「體高、底面重心到頂點、側稜」這個直角三角形裡，餘弦 ' + T('=\\dfrac{\\text{重心到頂點}}{\\text{側稜}}') + '（與邊長無關）。';
    return { q: '正四面體的邊長為 ' + T(String(a)) + '。(1) 求' + it[0] + '。(2) 求' + ask2 + '。',
             a: '(1) ' + T(it[1]) + '　(2) ' + T(ans2),
             h: '邊長 ' + T('a') + ' 的正四面體記這幾個數字：面上的高 ' + T('\\dfrac{\\sqrt{3}}{2}a') + '、面的外接圓半徑 ' + T('\\dfrac{\\sqrt{3}}{3}a') + '、體高 ' + T('\\dfrac{\\sqrt{6}}{3}a') + '、體積 ' + T('\\dfrac{\\sqrt{2}}{12}a^3') + '、表面積 ' + T('\\sqrt{3}a^2') + '；中心把體高分成 ' + T('3:1') + '（外接球半徑 ' + T('\\dfrac{\\sqrt{6}}{4}a') + '、內切球半徑 ' + T('\\dfrac{\\sqrt{6}}{12}a') + '）。(1) 把 ' + T('a=' + a) + ' 代進「' + it[0] + '」的式子' + note + '，算完根號要化到最簡、分數要約分。' + hint2,
             p: { a: a, which: which, q2: q2, ans: { num: it[2][0], rad: it[2][1], den: it[2][2] } } };
  };

  /* 2-12 點在直線上的投影 */
  L2.projLine3 = function (r) {
    var A = rv(r, -5, 5), C, B; do { C = rv(r, -5, 5); } while (isZero(sub(C, A))); B = rv(r, -5, 5);
    var AC = sub(C, A), t = F(dot(sub(B, A), AC), n2(AC));
    var H = [Fr.add(F(A[0]), Fr.mul(t, F(AC[0]))), Fr.add(F(A[1]), Fr.mul(t, F(AC[1]))), Fr.add(F(A[2]), Fr.mul(t, F(AC[2])))];
    var AB = sub(B, A);
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。求 ' + T('B') + ' 在直線 ' + T('AC') + ' 上的投影點 ' + T('H') + '，並說明 ' + T('H') + ' 落在線段 ' + T('\\overline{AC}') + ' 的內部、外部或端點。',
             a: T('H' + vtF(H)) + '，' + (t.n < 0 ? '在 $A$ 的外側' : Fr.eq(t, F(0)) ? '就是 $A$' : t.n < t.d ? '在線段內部' : Fr.eq(t, F(1)) ? '就是 $C$' : '在 $C$ 的外側') + '（' + T('t=' + Fr.tex(t)) + '）',
             h: '先算 ' + T(ov('AB') + '=' + vt(AB)) + '、' + T(ov('AC') + '=' + vt(AC)) + '。投影的比例 ' + T('t=\\dfrac{' + ov('AB') + '\\cdot' + ov('AC') + '}{|' + ov('AC') + '|^2}') + '：分子 ' + T('=' + hxDot(AB, AC)) + '、分母 ' + T('=' + hxN2(AC)) + '。投影點 ' + T('=A+t\\,' + ov('AC')) + '；' + T('0\\le t\\le1') + ' 才落在線段上（' + T('t=0') + ' 就是 ' + T('A') + '、' + T('t=1') + ' 就是 ' + T('C') + '）。',
             p: { A: A, B: B, C: C, ans: { t: fr2(t), H: H.map(fr2) } } };
  };

  /* 2-13 點到直線的距離 */
  L2.ptLineDist = function (r) {
    var A = rv(r, -4, 4), B, P, cr; do { B = rv(r, -4, 4); P = rv(r, -4, 4); cr = cross(sub(P, A), sub(B, A)); } while (isZero(sub(B, A)) || isZero(cr));
    var d2 = [n2(cr), n2(sub(B, A))];
    var AP = sub(P, A), AB = sub(B, A), dt = hxCr(AP, AB);
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('P' + vt(P)) + '。求 ' + T('P') + ' 到直線 ' + T('AB') + ' 的距離。',
             a: T(sqrtFracTex(d2[0], d2[1])),
             h: '先算 ' + T(ov('AP') + '=' + vt(AP)) + '、' + T(ov('AB') + '=' + vt(AB)) + '。' + T('d=\\dfrac{|' + ov('AP') + '\\times' + ov('AB') + '|}{|' + ov('AB') + '|}') + '（同一個三角形面積的兩種算法相等）：外積的三個分量是 ' + T('=' + dt[0]) + '、' + T('=-' + dt[1]) + '、' + T('=' + dt[2]) + '，分母用 ' + T('|' + ov('AB') + '|^2=' + hxN2(AB)) + '。也可以先求投影點再算距離。',
             p: { A: A, B: B, P: P, ans: d2 } };
  };

  /* 2-14 平面上的最近點（柯西的等號） */
  L2.cauchyPoint = function (r) {
    var a = r.nz(-4, 4), b = r.nz(-4, 4), c = r.nz(-4, 4), Q = rv(r, -5, 5), d = r.int(-10, 10);
    if (d === dot([a, b, c], Q)) d += 3;          /* 避免 Q 本身就在平面上 */
    /* 最近點 = Q + t n，n=(a,b,c)，t = (d - n·Q)/|n|² */
    var s = a * a + b * b + c * c, t = F(d - dot([a, b, c], Q), s);
    var P = [Fr.add(F(Q[0]), Fr.mul(t, F(a))), Fr.add(F(Q[1]), Fr.mul(t, F(b))), Fr.add(F(Q[2]), Fr.mul(t, F(c)))];
    var mn = F((d - dot([a, b, c], Q)) * (d - dot([a, b, c], Q)), s);
    return { q: '設 ' + T('x,y,z') + ' 為實數且 ' + T(term(a, 'x', true) + term(b, 'y', false) + term(c, 'z', false) + '=' + d) + '，求 ' + T('(x' + term(-Q[0], '', false) + ')^2+(y' + term(-Q[1], '', false) + ')^2+(z' + term(-Q[2], '', false) + ')^2') + ' 的最小值，並求此時的 ' + T('(x,y,z)') + '。',
             a: '最小值 ' + T(Fr.tex(mn)) + '，此時 ' + T(vtF(P)),
             h: '令 $u=x' + term(-Q[0], '', false) + '$ 等三個新變數，條件變成 $' + term(a, 'u', true) + term(b, 'v', false) + term(c, 'w', false) + '=' + (d - dot([a, b, c], Q)) + '$，再用柯西；等號在 $(u,v,w)\\parallel' + vt([a, b, c]) + '$。',
             p: { a: a, b: b, c: c, Q: Q, d: d, ans: { mn: fr2(mn), P: P.map(fr2) } } };
  };

  /* 2-15 長方體中兩條歪斜面對角線的夾角 */
  L2.skewAngleBox = function (r) {
    var a = r.int(2, 7), b = r.int(2, 7), c = r.int(2, 7);
    /* AF=(a,0,c)、BG=(0,b,c)：cos = c²/(√(a²+c²)√(b²+c²)) */
    var cos2 = [c * c * c * c, (a * a + c * c) * (b * b + c * c)];
    return { q: '長方體 ' + T('ABCD') + '-' + T('EFGH') + ' 中 ' + T('\\overline{AB}=' + a) + '、' + T('\\overline{AD}=' + b) + '、' + T('\\overline{AE}=' + c) + '。求歪斜線 ' + T('AF') + ' 與 ' + T('BG') + '（兩條面對角線）所夾角的餘弦值。',
             a: T(sqrtFracTex(cos2[0], cos2[1])),
             h: '歪斜線的夾角＝方向向量的夾角：$\\overrightarrow{AF}=(' + a + ',0,' + c + ')$、$\\overrightarrow{BG}=(0,' + b + ',' + c + ')$，內積 $=' + (c * c) + '$。',
             p: { a: a, b: b, c: c, ans: cos2 } };
  };

  /* 2-16 三角錐的體積比 */
  L2.volumeRatio = function (r) {
    var ratios = [[r.int(1, 4), r.int(1, 4)], [r.int(1, 4), r.int(1, 4)], [r.int(1, 4), r.int(1, 4)]];
    ratios = ratios.map(function (x) { var g = gcd(x[0], x[1]); return [x[0] / g, x[1] / g]; });   /* 2:2、4:4、2:4 → 最簡比 */
    var f = ratios.map(function (x) { return F(x[0], x[0] + x[1]); });
    var v = Fr.mul(Fr.mul(f[0], f[1]), f[2]);
    var nm = ['\\overline{OP}:\\overline{OA}', '\\overline{OQ}:\\overline{OB}', '\\overline{OR}:\\overline{OC}'];
    return { q: '三角錐 ' + T('O') + '-' + T('ABC') + ' 中，在 ' + T('\\overline{OA}') + '、' + T('\\overline{OB}') + '、' + T('\\overline{OC}') + ' 上各取 ' + T('P') + '、' + T('Q') + '、' + T('R') + '，使 ' + T('\\overline{OP}:\\overline{PA}=' + ratios[0][0] + ':' + ratios[0][1]) + '、' + T('\\overline{OQ}:\\overline{QB}=' + ratios[1][0] + ':' + ratios[1][1]) + '、' + T('\\overline{OR}:\\overline{RC}=' + ratios[2][0] + ':' + ratios[2][1]) + '。求 ' + T('V(O\\text{-}PQR):V(O\\text{-}ABC)') + '。',
             a: T(v.n + ':' + v.d),
             h: '題目給的是「分成兩段」的比，要先換成「佔全長的幾分之幾」：' + [0, 1, 2].map(function (i) { return T(nm[i] + '=' + ratios[i][0] + ':' + (ratios[i][0] + ratios[i][1])); }).join('、') + '。三個方向的伸縮比相乘就是體積比（行列式每一列都是線性的），最後約成最簡整數比。',
             p: { ratios: ratios, ans: fr2(v) } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p（與 o.a）重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     用法：用 splice 腳本插在 META（var META_L1 = [）之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     自己加的小工具一律加前綴 sol；patch_gen_11b1 的 hx* 工具（hxPar／hxPr／hxSq／hxN2／hxDot／hxD2／hxCr／hxM3／hxLin）可直接用。
     ══════════════════════════════════════════════════════════ */
  function solF(t) { return F(t[0], t[1]); }                      /* p 裡的 [n,d] 還原成分數 */
  function solFin(o) { return '答案：' + o.a + '。'; }
  function solEq(raw, red) { return raw === red ? raw : raw + '=' + red; }   /* 代入式已是最簡就不再寫一次 */
  function solRt(n2v) { return n2v <= 1 ? String(n2v) : solEq('\\sqrt{' + n2v + '}', sqrtTex(n2v)); }  /* √n 化到最簡（已最簡就不重複；√0、√1 直接寫值） */
  function solSum(list) {                                         /* 一串分數相加的算式（負項寫成減、值為 0 的項略過） */
    var nz = list.filter(function (w) { return w.n !== 0; });
    if (!nz.length) return '0';
    return nz.map(function (w, i) { return (i === 0 || w.n < 0 ? '' : '+') + Fr.tex(w, true); }).join('');
  }
  var SOL_TGT = ['$xy$ 平面', '$yz$ 平面', '$zx$ 平面', '$x$ 軸', '$y$ 軸', '$z$ 軸', '原點'];
  var SOL_FLIP = [[2], [0], [1], [1, 2], [0, 2], [0, 1], [0, 1, 2]];
  var SOL_ZERO = [[2], [0], [1], [1, 2], [0, 2], [0, 1]];

  var L1_H1 = {
    octantDist: '這是「卦限與各種距離」：先用三個坐標的正負定出位置，再記住到軸的距離是把軸名那個坐標丟掉、到坐標平面的距離就是缺席的那個坐標。',
    symProj: '這是「對稱點與投影點」：對平面對稱只有缺席的坐標變號、對軸對稱是軸名以外的兩個變號、對原點全部變號；投影則是把不在上面的坐標歸零。',
    midDiv: '這是「兩點距離、中點與分點」：中點取兩端坐標的平均，內分點用「交叉配」的加權平均——離哪一端近，權重就給哪一端。',
    centroidC: '這是「重心反求頂點」：重心是各頂點坐標的平均，把這個公式反過來解，就得到缺的那一個頂點。',
    equidistAxis: '這是「軸上的等距點」：先設動點只有一個坐標未知、其餘為零，再把兩段距離的平方寫出來令它們相等，平方項會自動消掉。',
    boxGeom: '這是「長方體的體對角線」：把一個頂點當原點、三條稜當三軸，體對角線與底面的夾角看它在底面的投影，與稜的夾角用內積。',
    minSum: '這是「把根式和看成距離」：每一個根號都是空間中兩點的距離，把它畫成同一個坐標平面上的動點到兩個定點，兩定點在異側時最小值就是連線長。',
    vecOps3: '這是「空間向量的基本運算」：加減與係數倍都逐分量做，長度取分量平方和的根號，單位向量再除以長度。',
    parallel3: '這是「平行的待定分量」：平行代表兩個向量的分量成同一個比例，先用兩邊都已知的那個分量定出倍數，再乘回去。',
    collinear3: '這是「三點共線」：共線就是兩個連接向量平行，先用已知的分量定出倍數，再回頭求未知的坐標。',
    divCoef: '這是「係數和判別法」：位置向量寫成兩個端點的線性組合時，係數和等於一就落在直線上，兩個係數都是正的才落在線段內部。',
    coplanarComb: '這是「共平面與線性組合」：把目標向量寫成另外兩個向量的組合，三個分量給三條方程式，用兩條解、剩下一條驗。',
    fourCoplanar: '這是「四點共平面」：從同一個頂點拉出三個向量，第三個要能被前兩個組合出來；先用不含未知數的兩個分量解出係數。',
    triIneq3: '這是「向量的三角不等式」：和的長度夾在兩個長度之差的絕對值與兩個長度之和之間；要求內積就把和的長度平方展開。',
    sumLen: '這是「三向量和的長度」：求長度一律先平方，展開後會出現三個兩兩內積，每個內積都用兩個長度相乘再乘夾角的餘弦。',
    dotAngle3: '這是「內積與夾角」：內積是分量相乘再相加，餘弦值等於內積除以兩個長度的乘積，銳角鈍角完全由內積的正負決定。',
    perpT: '這是「垂直的待定係數」：垂直就是內積等於零，把三項乘開相加會得到未知數的一次方程式。',
    unitPerp: '這是「同時垂直於兩個向量的單位向量」：外積直接給出垂直的方向，先約掉公因數再除以長度，而且答案永遠有正反兩個。',
    proj3: '這是「正射影」：正射影向量的分母是長度的平方、正射影長的分母只除一次；正射影長會跟著內積變號。',
    cauchy3: '這是「柯西不等式求最小值」：把已知的一次式與待求的平方和配成柯西的兩邊，等號成立時兩組數字成比例。',
    cross3: '這是「外積的計算」：三個分量各是一個二階行列式，中間那一項要反過來減；算完用「與原來兩個向量的內積都是零」檢查。',
    area3: '這是「三點決定的三角形面積」：先拉出兩個邊向量，外積的長度就是平行四邊形的面積，三角形再除以二。',
    dihedralBox: '這是「長方體裡的兩面角」：先找到稜，再在兩個面內各作一條垂直於稜的線，這個平面角會落在一個看得見的直角三角形裡。',
    det3calc: '這是「三階行列式的計算」：沿第一列展開成三個二階行列式，或用對角線法把六支乘積分成要加的三支與要減的三支。',
    detProps: '這是「行列式的性質」：每一列都是線性的、有兩列相同就等於零、對調兩列要變號、輪換三列不變，而絕對值就是平行六面體的體積。',
    volume3: '這是「三重積與體積」：三重積就是三個向量排成三列的行列式，平行六面體的體積取絕對值，四面體再除以六。',
    ptPlaneAxes: '這是「牆角型的點到平面距離」：三條稜互相垂直時體積很好算，底面積用外積，最後用體積反解高——本章走體積法，不需要平面方程式。'
  };

  var L1_SOL = {};

  /* ── §2 空間坐標 ── */
  L1_SOL.octantDist = function (p, o) {
    var P = p.P, oct = p.ans.oct, qd = oct > 4 ? oct - 4 : oct;
    var rest = [0, 1, 2].filter(function (i) { return i !== p.ax; }), mi = [2, 0, 1][p.pl];
    return ['先看 ' + T('z=' + P[2]) + '：' + (P[2] > 0 ? '為正 ⟹ 在上半（第一～四卦限）' : '為負 ⟹ 在下半（第五～八卦限）') + '；' + T('(x,y)=(' + P[0] + ',' + P[1] + ')') + ' 落在第' + CN[qd] + '象限，所以 ' + T('P') + ' 在第' + CN[oct] + '卦限。',
      '到原點的距離用三個坐標的平方和：' + T('\\overline{OP}^2=' + hxN2(P) + '=' + p.ans.r2) + '，開根號得 ' + T(solRt(p.ans.r2)) + '。',
      '到 ' + T(AXES[p.ax]) + ' 軸的距離「把 ' + T(AXES[p.ax]) + ' 丟掉」：' + T('\\sqrt{' + hxSq(P[rest[0]]) + '+' + hxSq(P[rest[1]]) + '}=' + solRt(p.ans.ax2)) + '；到 ' + T(PLANES[p.pl]) + ' 平面的距離只看缺席的那個坐標 ' + T('|' + P[mi] + '|=' + p.ans.pl) + '。' + solFin(o)];
  };

  L1_SOL.symProj = function (p, o) {
    var P = p.P, S = p.ans.S, Q = p.ans.Q, d = sub(S, P);
    var nm = function (k) { return T(AXES[k] + '=' + P[k]); };
    return ['對' + (p.i === 6 ? '' : ' ') + SOL_TGT[p.i] + '對稱，要變號的坐標是 ' + SOL_FLIP[p.i].map(nm).join('、') + '，其餘不動 ⟹ 對稱點 ' + T(vt(S)) + '。',
      '投影到 ' + SOL_TGT[p.j] + '，要歸零的坐標是 ' + SOL_ZERO[p.j].map(nm).join('、') + ' ⟹ 投影點 ' + T(vt(Q)) + '。',
      '對稱點與 ' + T('P') + ' 只在變號的那幾個坐標上不同：兩點的差是 ' + T(vt(d)) + '，距離 ' + T('\\sqrt{' + hxN2(d) + '}=' + solRt(p.ans.d2)) + '。' + solFin(o)];
  };

  L1_SOL.midDiv = function (p, o) {
    var A = p.A, B = p.B, m = p.m, n = p.n, AB = sub(B, A);
    var M = p.ans.M.map(solF), Pt = p.ans.P.map(solF);
    return [T(ov('AB') + '=' + vt(AB)) + '，' + T('\\overline{AB}^2=' + hxN2(AB) + '=' + p.ans.d2) + '，所以 ' + T('\\overline{AB}=' + solRt(p.ans.d2)) + '。',
      '中點取兩端坐標的平均：' + T('M' + vtF(M)) + '。',
      '內分 ' + T(m + ':' + n) + ' 要「交叉配」：' + T('P=\\dfrac{' + term(n, 'A', true) + term(m, 'B', false) + '}{' + (m + n) + '}') + '，' + T('x') + ' 坐標 ' + T('=\\dfrac{' + hxPr([n, A[0]]) + '+' + hxPr([m, B[0]]) + '}{' + (m + n) + '}=' + Fr.tex(Pt[0], true)) + '，三個坐標同法 ⟹ ' + T('P' + vtF(Pt)) + '。' + solFin(o)];
  };

  L1_SOL.centroidC = function (p, o) {
    var A = p.A, B = p.B, C = p.ans.C, D = p.D, G = p.G.map(solF), G4 = p.ans.G4.map(solF);
    return ['重心是三個頂點坐標的平均：' + T('G=\\dfrac{A+B+C}{3}') + '，反解得 ' + T('C=3G-A-B') + '。',
      '逐坐標算：' + T('x') + ' 坐標 ' + T('=3\\cdot\\left(' + Fr.tex(G[0], true) + '\\right)' + term(-A[0], '', false) + term(-B[0], '', false) + '=' + C[0]) + '，' + T('y') + '、' + T('z') + ' 同法 ⟹ ' + T('C' + vt(C)) + '。',
      '四面體重心是四個頂點坐標的平均：' + T('\\dfrac{A+B+C+D}{4}') + '，' + T('x') + ' 坐標 ' + T('=\\dfrac{' + A[0] + term(B[0], '', false) + term(C[0], '', false) + term(D[0], '', false) + '}{4}=' + Fr.tex(G4[0], true)) + '，三個坐標同法 ⟹ ' + T(vtF(G4)) + '。' + solFin(o)];
  };

  L1_SOL.equidistAxis = function (p, o) {
    var A = p.A, B = p.B, ax = p.ax, tv_ = solF(p.ans.t), PA2 = solF(p.ans.PA2);
    var Pt = [F(0), F(0), F(0)]; Pt[ax] = tv_;
    var ex = function (X) { return [0, 1, 2].map(function (k) { return k === ax ? (X[k] === 0 ? 't^2' : '(t' + term(-X[k], '', false) + ')^2') : hxSq(X[k]); }).join('+'); };
    var co = 2 * (B[ax] - A[ax]), rhs = n2(B) - n2(A);
    return ['設 ' + T('P') + ' 的 ' + T(AXES[ax]) + ' 坐標為 ' + T('t') + '、其餘為 ' + T('0') + '，則 ' + T('\\overline{PA}^2=' + ex(A)) + '、' + T('\\overline{PB}^2=' + ex(B)) + '。',
      '令兩者相等，' + T('t^2') + ' 相消後只剩一次式：' + T(term(co, 't', true) + '=' + rhs) + ' ⟹ ' + T('t=' + Fr.tex(tv_)) + '，也就是 ' + T('P' + vtF(Pt)) + '。',
      '代回去算 ' + T('\\overline{PA}^2=' + ex(A)) + ' 的值：' + T('\\overline{PA}^2=' + Fr.tex(PA2)) + '。' + solFin(o)];
  };

  L1_SOL.boxGeom = function (p, o) {
    var a = p.a, b = p.b, c = p.c, s = p.ans.s, ab2 = a * a + b * b;
    return ['取 ' + T('A') + ' 為原點、三條稜為三軸：' + T(ov('AG') + '=' + vt([a, b, c])) + '，體對角線 ' + T('\\overline{AG}=\\sqrt{' + hxN2([a, b, c]) + '}=' + solRt(s)) + '。',
      T(ov('AG')) + ' 在底面的投影是 ' + T(ov('AC') + '=' + vt([a, b, 0])) + '（長 ' + T(solRt(ab2)) + '），與底面的夾角落在直角三角形 ' + T('A') + '–' + T('C') + '–' + T('G') + ' 裡：' + T('\\cos\\theta=\\dfrac{\\overline{AC}}{\\overline{AG}}=\\sqrt{\\dfrac{' + ab2 + '}{' + s + '}}=' + sqrtFracTex(ab2, s)) + '。',
      '與稜 ' + T(ov('AB') + '=' + vt([a, 0, 0])) + ' 的夾角用內積：' + T('\\cos\\varphi=\\dfrac{' + ov('AG') + '\\cdot' + ov('AB') + '}{|' + ov('AG') + '||' + ov('AB') + '|}=\\dfrac{' + (a * a) + '}{' + a + '\\sqrt{' + s + '}}=' + sqrtFracTex(a * a, s)) + '。' + solFin(o)];
  };

  L1_SOL.minSum = function (p, o) {
    var A = p.A, B = p.B, d = sub(A, B);
    return ['把每個根號讀成距離：第一個根號是 ' + T('xy') + ' 平面上的動點 ' + T('(x,y,0)') + ' 到 ' + T('A' + vt(A)) + ' 的距離（常數項 ' + T(hxSq(A[2])) + ' 就是高的平方），第二個是到 ' + T('B' + vt(B)) + ' 的距離。',
      T('A') + ' 的 ' + T('z') + ' 坐標為正、' + T('B') + ' 的為負，兩點在 ' + T('xy') + ' 平面的異側，所以「到兩點的距離和」最小值就是線段 ' + T('\\overline{AB}') + ' 本身（動點取 ' + T('\\overline{AB}') + ' 與平面的交點）。',
      T(ov('BA') + '=' + vt(d)) + '，' + T('\\overline{AB}=\\sqrt{' + hxN2(d) + '}=' + solRt(p.ans)) + '。' + solFin(o)];
  };

  /* ── §3 空間向量 ── */
  L1_SOL.vecOps3 = function (p, o) {
    var a = p.a, b = p.b, k1 = p.k1, k2 = p.k2, c = p.ans.c, ab = add(a, b), na = p.ans.na;
    var s = simpSqrt(na), gu = gcd(gcd(gcd(a[0], a[1]), a[2]), s.c);
    var unit = s.r === 1 ? vtF([F(a[0], s.c), F(a[1], s.c), F(a[2], s.c)]) : '\\dfrac{1}{' + (s.c / gu === 1 ? '' : s.c / gu) + '\\sqrt{' + s.r + '}}' + vt(a.map(function (v) { return v / gu; }));
    return ['係數倍與加減都逐分量做：' + T('x') + ' 分量 ' + T('=' + hxPr([k1, a[0]]) + '+' + hxPr([k2, b[0]]) + '=' + c[0]) + '，三個分量同法 ⟹ ' + T(vt(c)) + '。',
      T('|\\vec a|=\\sqrt{' + hxN2(a) + '}=' + solRt(na)) + '；先加出 ' + T('\\vec a+\\vec b=' + vt(ab)) + ' 再取長度 ' + T('\\sqrt{' + hxN2(ab) + '}=' + solRt(p.ans.nab)) + '。',
      '同向的單位向量是 ' + T('\\dfrac{\\vec a}{|\\vec a|}') + '：把 ' + T(vt(a)) + ' 除以 ' + T(solRt(na)) + '，分子的公因數與根號外的係數一起約掉 ⟹ ' + T(unit) + '。' + solFin(o)];
  };

  L1_SOL.parallel3 = function (p, o) {
    var b = p.b, kf = F(p.k), i = p.i, j = p.j, kk = 3 - i - j, mv = p.ans.m, nv = p.ans.n;
    return ['平行 ⟹ 兩個向量的三個分量成同一個比例 ' + T('(m,n,\\ldots)=k' + vt(b)) + '。',
      '兩邊都是數字的是第 ' + (kk + 1) + ' 個分量：' + T(p.known + '=k\\cdot' + hxPar(b[kk])) + ' ⟹ ' + T('k=' + Fr.tex(kf)) + '。',
      '把 ' + T('k') + ' 乘回另外兩個分量：' + T('m=' + hxPr([Fr.tex(kf, true), b[i]]) + '=' + mv) + '、' + T('n=' + hxPr([Fr.tex(kf, true), b[j]]) + '=' + nv) + '，' + T('m+n=' + (mv + nv)) + '。' + solFin(o)];
  };

  L1_SOL.collinear3 = function (p, o) {
    var A = p.A, B = p.B, Cn = p.C, hide = p.hide, AB = sub(B, A), kf = solF(p.ans.k);
    var kn = [0, 1, 2].filter(function (t) { return t !== hide; });
    return ['共線 ⟺ ' + T(ov('AC') + '=k\\,' + ov('AB')) + '。先算 ' + T(ov('AB') + '=' + vt(AB)) + '。',
      T(ov('AC')) + ' 已知的分量是第 ' + kn.map(function (u) { return u + 1; }).join('、') + ' 個：' + kn.map(function (u) { return T(String(Cn[u] - A[u])); }).join('、') + '；與 ' + T(ov('AB')) + ' 的同一個分量相比 ' + T(String(Cn[kn[0]] - A[kn[0]]) + '=k\\cdot' + hxPar(AB[kn[0]])) + ' ⟹ ' + T('k=' + Fr.tex(kf)) + '。',
      '再看第 ' + (hide + 1) + ' 個分量：' + T('c' + term(-A[hide], '', false) + '=' + hxPr([Fr.tex(kf, true), AB[hide]])) + ' ⟹ ' + T('c=' + p.ans.c) + '。' + solFin(o)];
  };

  L1_SOL.divCoef = function (p, o) {
    var A = p.A, B = p.B, x = solF(p.x), y = solF(p.y), Pt = p.ans.P.map(solF);
    return ['係數和 ' + T(Fr.tex(x, true) + (y.n < 0 ? '' : '+') + Fr.tex(y, true) + '=1') + '，所以 ' + T('P') + ' 一定落在直線 ' + T('AB') + ' 上。',
      '把係數乘進坐標：' + T('x') + ' 坐標 ' + T('=' + hxPr([Fr.tex(x, true), A[0]]) + '+' + hxPr([Fr.tex(y, true), B[0]]) + '=' + Fr.tex(Pt[0], true)) + '，三個坐標同法 ⟹ ' + T('P' + vtF(Pt)) + '。',
      '兩個係數' + (p.ans.ext ? '有一個是負的 ⟹ ' + T('P') + ' 不在線段上（外分）' : '都是正的 ⟹ ' + T('P') + ' 在線段上（內分）') + '；' + T('\\overline{AP}:\\overline{PB}=|y|:|x|=' + p.ans.m + ':' + p.ans.n) + '（已約成最簡整數比）。' + solFin(o)];
  };

  L1_SOL.coplanarComb = function (p, o) {
    var u = p.u, v = p.v, w = p.w, pv = p.ans.p, qv = p.ans.q;
    var eq = function (i) { return hxLin([[u[i], 'p'], [v[i], 'q']]) + '=' + w[i]; };
    return ['先假設 ' + T('\\vec w=p\\,\\vec u+q\\,\\vec v') + '，三個分量各給一條方程式：' + T(eq(0)) + '、' + T(eq(1)) + '、' + T(eq(2)) + '。',
      '兩個未知數用前兩條解：' + T('p=' + pv) + '、' + T('q=' + qv) + '，也就是 ' + T('(p,q)=(' + pv + ',' + qv + ')') + '。',
      '把 ' + T('(p,q)') + ' 代進第三條驗算：' + T(hxPr([pv, u[2]]) + '+' + hxPr([qv, v[2]]) + '=' + w[2]) + ' 成立 ⟹ 三個向量共平面，即 ' + T('\\det(\\vec u,\\vec v,\\vec w)=0') + '。' + solFin(o)];
  };

  L1_SOL.fourCoplanar = function (p, o) {
    var A = p.A, B = p.B, C = p.C, D = p.D, hide = p.hide, s = p.ans.s, t = p.ans.t;
    var AB = sub(B, A), AC = sub(C, A), kn = [0, 1, 2].filter(function (i) { return i !== hide; });
    return ['從 ' + T('A') + ' 拉出三個向量：' + T(ov('AB') + '=' + vt(AB)) + '、' + T(ov('AC') + '=' + vt(AC)) + '；四點共平面 ⟺ ' + T(ov('AD') + '=s\\,' + ov('AB') + '+t\\,' + ov('AC')) + '。',
      '先用不含 ' + T('k') + ' 的兩個分量列式：' + kn.map(function (i) { return T(hxLin([[AB[i], 's'], [AC[i], 't']]) + '=' + (D[i] - A[i])); }).join('、') + ' ⟹ ' + T('(s,t)=(' + s + ',' + t + ')') + '。',
      '代回含 ' + T('k') + ' 的那一條：' + T('k' + term(-A[hide], '', false) + '=' + hxPr([s, AB[hide]]) + '+' + hxPr([t, AC[hide]])) + ' ⟹ ' + T('k=' + p.ans.k) + '。' + solFin(o)];
  };

  L1_SOL.triIneq3 = function (p, o) {
    var la = p.la, lb = p.lb, m = p.m, dv = solF(p.ans.dot);
    return ['三角不等式：' + T('\\big||\\vec a|-|\\vec b|\\big|\\le|\\vec a+\\vec b|\\le|\\vec a|+|\\vec b|') + '。本題 ' + T('|' + la + '-' + lb + '|=' + p.ans.lo) + '、' + T(la + '+' + lb + '=' + p.ans.hi) + ' ⟹ ' + T(p.ans.lo + '\\le|\\vec a+\\vec b|\\le' + p.ans.hi) + '。',
      '求內積先把和的長度平方：' + T('|\\vec a+\\vec b|^2=|\\vec a|^2+2\\vec a\\cdot\\vec b+|\\vec b|^2') + '，代入得 ' + T(hxSq(m) + '=' + hxSq(la) + '+2\\vec a\\cdot\\vec b+' + hxSq(lb)) + '。',
      '移項：' + T('2\\vec a\\cdot\\vec b=' + (m * m) + '-' + (la * la) + '-' + (lb * lb) + '=' + (m * m - la * la - lb * lb)) + ' ⟹ ' + T('\\vec a\\cdot\\vec b=' + Fr.tex(dv)) + '。' + solFin(o)];
  };

  L1_SOL.sumLen = function (p, o) {
    var l = p.l, dg = p.degs, s2 = solF(p.ans);
    var CT = { 60: '\\dfrac{1}{2}', 90: '0', 120: '-\\dfrac{1}{2}' }, CV = { 60: F(1, 2), 90: F(0), 120: F(-1, 2) };
    var pr = [[0, 1], [1, 2], [2, 0]], dots = pr.map(function (e, i) { return Fr.mul(F(l[e[0]] * l[e[1]]), CV[dg[i]]); });
    var sq = l[0] * l[0] + l[1] * l[1] + l[2] * l[2];
    var nm = ['\\vec a\\cdot\\vec b', '\\vec b\\cdot\\vec c', '\\vec c\\cdot\\vec a'];
    return ['求長度一律先平方：' + T('|\\vec a+\\vec b+\\vec c|^2=' + hxN2(l) + '+2(' + nm.join('+') + ')=' + sq + '+2(' + nm.join('+') + ')') + '。',
      '每個內積都是「兩個長度相乘再乘夾角餘弦」：' + pr.map(function (e, i) { return T(nm[i] + '=' + hxPr([l[e[0]], l[e[1]], CT[dg[i]]]) + '=' + Fr.tex(dots[i], true)); }).join('、') + '。',
      '加起來：' + T('|\\vec a+\\vec b+\\vec c|^2=' + sq + '+2\\left(' + solSum(dots) + '\\right)=' + Fr.tex(s2)) + '，開根號得 ' + T(solRt(s2.n)) + '。' + solFin(o)];
  };

  /* ── §4 內積、外積、正射影 ── */
  L1_SOL.dotAngle3 = function (p, o) {
    var a = p.a, b = p.b, d = p.ans.dot, na = n2(a), nb = n2(b);
    var cosT = d === 0 ? '0' : sqrtFracTex(d * d, na * nb, d < 0);
    return ['內積是三組分量相乘再相加：' + T('\\vec a\\cdot\\vec b=' + hxDot(a, b) + '=' + d) + '。',
      T('|\\vec a|^2=' + hxN2(a) + '=' + na) + '、' + T('|\\vec b|^2=' + hxN2(b) + '=' + nb) + '，所以 ' + T('\\cos\\theta=\\dfrac{' + d + '}{\\sqrt{' + na + '}\\sqrt{' + nb + '}}=' + cosT) + '；內積' + (d > 0 ? '為正 ⟹ 銳角' : d < 0 ? '為負 ⟹ 鈍角' : '為零 ⟹ 直角') + '。',
      T('|\\vec a+\\vec b|^2=|\\vec a|^2+|\\vec b|^2+2\\vec a\\cdot\\vec b=' + na + '+' + nb + '+' + hxPr([2, d]) + '=' + p.ans.nab) + '。' + solFin(o)];
  };

  L1_SOL.perpT = function (p, o) {
    var b = p.b, av = p.av, i = p.i, tv_ = solF(p.ans), ss = '', cst = 0;
    for (var k = 0; k < 3; k++) {
      if (k === i) ss += term(b[k], 't', ss === '');
      else { ss += (ss === '' ? '' : '+') + hxPr([av[k], b[k]]); cst += av[k] * b[k]; }
    }
    return ['垂直 ⟺ 內積等於 ' + T('0') + '：把兩個向量的三組分量乘開相加 ' + T(ss + '=0') + '。',
      '整理成 ' + T('t') + ' 的一次方程式：' + T(term(b[i], 't', true) + term(cst, '', false) + '=0') + '。',
      '移項再除以 ' + T('t') + ' 的係數：' + T('t=' + Fr.tex(tv_)) + '。' + solFin(o)];
  };

  L1_SOL.unitPerp = function (p, o) {
    var a = p.a, b = p.b, c = cross(a, b), cr = p.ans.dir, nc = p.ans.nc;
    var g = gcd(gcd(Math.abs(c[0]), Math.abs(c[1])), Math.abs(c[2])) || 1;
    var dt = hxCr(a, b);
    return ['「同時垂直於兩個向量」就是外積的方向。三個分量各是一個二階行列式：' + T('=' + dt[0]) + '、' + T('=-' + dt[1]) + '、' + T('=' + dt[2]) + ' ⟹ ' + T('\\vec a\\times\\vec b=' + vt(c)) + '。',
      (g === 1 ? '三個分量已經互質' : '三個分量同除公因數 ' + T(String(g))) + '，方向取 ' + T(vt(cr)) + '，長度 ' + T('\\sqrt{' + hxN2(cr) + '}=' + solRt(nc)) + '。',
      '除以長度就是單位向量，而「同時垂直」永遠有正反兩個方向：' + T('\\pm\\dfrac{1}{' + sqrtTex(nc) + '}' + vt(cr)) + '。' + solFin(o)];
  };

  L1_SOL.proj3 = function (p, o) {
    var a = p.a, b = p.b, d = dot(a, b), nb = n2(b), k = solF(p.ans.k);
    var pv = [Fr.mul(k, F(b[0])), Fr.mul(k, F(b[1])), Fr.mul(k, F(b[2]))];
    var lenT = d === 0 ? '0' : sqrtFracTex(d * d, nb, d < 0);
    return ['先算兩個數字：' + T('\\vec a\\cdot\\vec b=' + hxDot(a, b) + '=' + d) + '、' + T('|\\vec b|^2=' + hxN2(b) + '=' + nb) + '。',
      '正射影向量的分母是長度的平方：' + T('\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|^2}\\vec b=\\dfrac{' + d + '}{' + nb + '}' + vt(b) + '=' + vtF(pv)) + '。',
      '正射影長只除一次長度（會跟著內積變號）：' + T('\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|}=\\dfrac{' + d + '}{\\sqrt{' + nb + '}}=' + lenT) + '。' + solFin(o)];
  };

  L1_SOL.cauchy3 = function (p, o) {
    var a = p.a, b = p.b, c = p.c, d = p.d, s = a * a + b * b + c * c;
    var mn = solF(p.ans.mn), Pv = p.ans.P.map(solF), kf = F(d, s);
    return ['柯西不等式：' + T('(x^2+y^2+z^2)\\left(' + hxSq(a) + '+' + hxSq(b) + '+' + hxSq(c) + '\\right)\\ge\\left(' + term(a, 'x', true) + term(b, 'y', false) + term(c, 'z', false) + '\\right)^2') + '，右邊由條件等於 ' + T(hxSq(d) + '=' + (d * d)) + '。',
      '左邊的括號是 ' + T(String(s)) + '，所以 ' + T('x^2+y^2+z^2\\ge\\dfrac{' + (d * d) + '}{' + s + '}=' + Fr.tex(mn)) + '，最小值就是 ' + T(Fr.tex(mn)) + '。',
      '等號在 ' + T('(x,y,z)\\parallel' + vt([a, b, c])) + '：設 ' + T('(x,y,z)=t' + vt([a, b, c])) + ' 代回條件得 ' + T('t=\\dfrac{' + d + '}{' + s + '}=' + Fr.tex(kf)) + ' ⟹ ' + T(vtF(Pv)) + '。' + solFin(o)];
  };

  L1_SOL.cross3 = function (p, o) {
    var a = p.a, b = p.b, c = p.ans.c, nc = p.ans.nc, dt = hxCr(a, b), d = dot(a, b);
    var na = n2(a), nb = n2(b);
    return ['外積的三個分量各是一個二階行列式（中間那一項反過來減）：' + T('=' + dt[0]) + '、' + T('=-' + dt[1]) + '、' + T('=' + dt[2]) + ' ⟹ ' + T('\\vec a\\times\\vec b=' + vt(c)) + '。',
      T('|\\vec a\\times\\vec b|=\\sqrt{' + hxN2(c) + '}=' + solRt(nc)) + '（可以順手檢查它與 ' + T('\\vec a') + '、' + T('\\vec b') + ' 的內積都是 ' + T('0') + '）。',
      '驗證恆等式：左邊 ' + T(nc + '+' + hxSq(d) + '=' + nc + '+' + (d * d) + '=' + (na * nb)) + '，右邊 ' + T('|\\vec a|^2|\\vec b|^2=' + hxPr([na, nb]) + '=' + (na * nb)) + '，兩邊相同。' + solFin(o)];
  };

  L1_SOL.area3 = function (p, o) {
    var A = p.A, B = p.B, C = p.C, cr = p.ans.cr, n = p.ans.n;
    var AB = sub(B, A), AC = sub(C, A), dt = hxCr(AB, AC), s = simpSqrt(n);
    var areaT = s.c % 2 === 0 ? sqrtTex(n / 4) : '\\dfrac{' + sqrtTex(n) + '}{2}';
    return ['先拉出兩個邊向量：' + T(ov('AB') + '=' + vt(AB)) + '、' + T(ov('AC') + '=' + vt(AC)) + '。',
      '外積的三個分量各是一個二階行列式：' + T('=' + dt[0]) + '、' + T('=-' + dt[1]) + '、' + T('=' + dt[2]) + ' ⟹ ' + T(ov('AB') + '\\times' + ov('AC') + '=' + vt(cr)) + '。',
      '外積的長度是平行四邊形面積：' + T('\\sqrt{' + hxN2(cr) + '}=' + solRt(n)) + '，三角形再除以 ' + T('2') + '：' + T('\\triangle ABC=' + solEq('\\dfrac{' + sqrtTex(n) + '}{2}', areaT)) + '。' + solFin(o)];
  };

  L1_SOL.dihedralBox = function (p, o) {
    var a = p.a, b = p.b, c = p.c, w = p.which;
    var edge = w === 0 ? 'AB' : 'AD', other = w === 0 ? 'AD' : 'AB', slant = w === 0 ? 'AH' : 'AF', up = w === 0 ? 'DH' : 'BF';
    var el = w === 0 ? b : a, hyp = el * el + c * c;
    return ['兩面角的稜是 ' + T('\\overline{' + edge + '}') + '：在底面內取 ' + T('\\overline{' + other + '}') + '、在另一個面內取 ' + T('\\overline{' + slant + '}') + '，兩者都與稜垂直，所以它們的夾角就是平面角。',
      '這個角落在直角三角形裡：' + T('\\overline{' + other + '}=' + el) + '、' + T('\\overline{' + up + '}=' + c) + '（鉛直），斜邊 ' + T('\\overline{' + slant + '}=\\sqrt{' + hxSq(el) + '+' + hxSq(c) + '}=' + solRt(hyp)) + '。',
      '餘弦是鄰邊比斜邊：' + T('\\cos\\theta=\\dfrac{' + el + '}{\\sqrt{' + hyp + '}}=' + sqrtFracTex(p.ans[0], p.ans[1])) + '。' + solFin(o)];
  };

  /* ── §5 行列式與體積 ── */
  L1_SOL.det3calc = function (p, o) {
    var M = p.M, g = function (i, j) { return M[i][j]; };
    var pos = [[g(0, 0), g(1, 1), g(2, 2)], [g(0, 1), g(1, 2), g(2, 0)], [g(0, 2), g(1, 0), g(2, 1)]];
    var neg = [[g(0, 2), g(1, 1), g(2, 0)], [g(0, 1), g(1, 0), g(2, 2)], [g(0, 0), g(1, 2), g(2, 1)]];
    var sp = pos.reduce(function (t2, e) { return t2 + e[0] * e[1] * e[2]; }, 0);
    var sn = neg.reduce(function (t2, e) { return t2 + e[0] * e[1] * e[2]; }, 0);
    var show = function (list) { return list.map(function (e) { return T(hxPr(e) + '=' + (e[0] * e[1] * e[2])); }).join('、'); };
    return ['用對角線法：往右下的三支乘積是 ' + show(pos) + '，相加得 ' + T(String(sp)) + '。',
      '往左下的三支乘積是 ' + show(neg) + '，相加得 ' + T(String(sn)) + '。',
      '前者減後者：' + T(sp + term(-sn, '', false) + '=' + p.ans) + '。' + solFin(o)];
  };

  L1_SOL.detProps = function (p, o) {
    var k = p.p * p.t - p.q * p.s, D = p.D;
    var row1 = comb(p.p, '\\vec a', true) + comb(p.q, '\\vec b', false), row2 = comb(p.s, '\\vec a', true) + comb(p.t, '\\vec b', false);
    return ['行列式每一列都是線性的，而且有兩列相同就等於 ' + T('0') + '。展開 ' + T('\\det(' + row1 + ',\\ ' + row2 + ',\\ \\vec c)') + ' 之後只剩 ' + T('\\left(' + hxPr([p.p, p.t]) + '-' + hxPr([p.q, p.s]) + '\\right)\\det(\\vec a,\\vec b,\\vec c)') + '。',
      '代入 ' + T('\\det(\\vec a,\\vec b,\\vec c)=' + D) + '：' + T(hxPr([k, D]) + '=' + p.ans.v1) + '。',
      (p.sw ? '對調第一列與第三列要變號：' + T('\\det(\\vec c,\\vec b,\\vec a)=-\\left(' + D + '\\right)=' + p.ans.v2) : '把三列輪換一次（' + T('\\vec b,\\vec c,\\vec a') + '）值不變：' + T('\\det(\\vec b,\\vec c,\\vec a)=' + p.ans.v2)) + '。平行六面體體積就是 (1) 的絕對值 ' + T('|' + p.ans.v1 + '|=' + p.ans.v3) + '。' + solFin(o)];
  };

  L1_SOL.volume3 = function (p, o) {
    var u = p.u, v = p.v, w = p.w, d = p.ans.d, vw = cross(v, w), dt = hxCr(v, w);
    return ['先算 ' + T('\\vec v\\times\\vec w') + '：三個分量各是一個二階行列式 ' + T('=' + dt[0]) + '、' + T('=-' + dt[1]) + '、' + T('=' + dt[2]) + ' ⟹ ' + T(vt(vw)) + '。',
      '再與 ' + T('\\vec u') + ' 內積：' + T('\\vec u\\cdot(\\vec v\\times\\vec w)=' + hxDot(u, vw) + '=' + d) + '（這就是三個向量排成三列的三階行列式）。',
      '平行六面體體積取絕對值 ' + T('|' + d + '|=' + Math.abs(d)) + '；四面體是它的六分之一 ' + T('\\dfrac{' + Math.abs(d) + '}{6}=' + Fr.tex(F(Math.abs(d), 6))) + '。' + solFin(o)];
  };

  L1_SOL.ptPlaneAxes = function (p, o) {
    var a = p.a, b = p.b, c = p.c, N = p.ans.N, V = F(a * b * c, 6);
    return ['牆角型：' + T('\\overline{OA}') + '、' + T('\\overline{OB}') + '、' + T('\\overline{OC}') + ' 三條稜互相垂直，' + T('V=\\dfrac{1}{6}' + hxPr([a, b, c]) + '=\\dfrac{' + (a * b * c) + '}{6}=' + Fr.tex(V)) + '。',
      T(ov('AB') + '=' + vt([-a, b, 0])) + '、' + T(ov('AC') + '=' + vt([-a, 0, c])) + '，外積 ' + T('=' + vt([b * c, c * a, a * b])) + '，長度 ' + T('\\sqrt{' + hxN2([b * c, c * a, a * b]) + '}=' + solRt(N)) + '，所以 ' + T('S=' + solEq('\\dfrac{' + sqrtTex(N) + '}{2}', radTex(1, N, 2))) + '。',
      '用體積法反解高（本章不需要平面方程式）：' + T('d=\\dfrac{3V}{S}=\\dfrac{' + (a * b * c) + '}{\\sqrt{' + N + '}}=' + sqrtFracTex(a * a * b * b * c * c, N)) + '。' + solFin(o)];
  };

  var META_L1 = [
      ['octantDist', '§2 卦限與距離'], ['symProj', '§2 對稱點與投影點'], ['midDiv', '§2 分點與中點'], ['centroidC', '§2 重心反求頂點'], ['equidistAxis', '§2 軸上等距點'], ['boxGeom', '§2 長方體體對角線'], ['minSum', '§2 坐標化解最小值'],
      ['vecOps3', '§3 向量基本運算'], ['parallel3', '§3 平行：待定分量'], ['collinear3', '§3 三點共線'], ['divCoef', '§3 係數和判別法'], ['coplanarComb', '§3 共平面與線性組合'], ['fourCoplanar', '§3 四點共平面'], ['triIneq3', '§3 三角不等式'], ['sumLen', '§3 三向量和的長度'],
      ['dotAngle3', '§4 內積與夾角'], ['perpT', '§4 垂直：待定係數'], ['unitPerp', '§4 同時垂直的單位向量'], ['proj3', '§4 正射影'], ['cauchy3', '§4 柯西不等式'], ['cross3', '§4 外積計算'], ['area3', '§4 三角形面積'], ['dihedralBox', '§4 長方體的兩面角'],
      ['det3calc', '§5 三階行列式'], ['detProps', '§5 行列式性質'], ['volume3', '§5 平行六面體與四面體體積'], ['ptPlaneAxes', '§5 牆角型：點到平面（體積法）']
  ];
  var META_L2 = [
      ['lineFaceAngle', '§2 兩體對角線的夾角'], ['cubeCoefDist', '§3 係數就是坐標'], ['bisectorT', '§4 角平分線方向'], ['extBisector', '§4 外角平分線交對邊'], ['weightedZero', '§3 加權和為零向量'],
      ['reflectPlane', '§2 鏡面反射'], ['paraCenter', '§3 平行六面體的面心'], ['detPoly', '§5 含 x 的行列式'], ['tetraDist', '§5 四面體體積與點到平面'], ['fourthVertex', '§3 平行四邊形第四頂點'],
      ['regularTetra', '§1 正四面體的五個數字'], ['projLine3', '§4 點在直線上的投影'], ['ptLineDist', '§4 點到直線的距離'], ['cauchyPoint', '§4 平面上的最近點'], ['skewAngleBox', '§1 歪斜線的夾角'], ['volumeRatio', '§5 三角錐體積比']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     ─────────────────────────────────────────────────────────
     同題型換數字／情境，答案一律精確：整數、F()（分數）、sqrtTex／sqrtFracTex／radTex（最簡根式、分母有理化）。
     本章工具只到「坐標＋向量＋內積＋外積＋三階行列式」：
       點到平面的距離一律走體積法（V=|det|/6、S=|外積|/2、d=3V/S）或坐標化＋投影，
       點到直線的距離走外積（|AP×AB|/|AB|）或投影點——
       平面方程式、直線參數式／比例式、點到平面公式都在 g11b-ch02，矩陣在本冊第四章，一律不用。
     p 只放輸入參數與旗標（答案另放 p.ans，驗算器不讀）。
     每型開頭先丟掉一次 r()：連號種子的 LCG 首值幾乎相同，變體旗標不能靠它。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};

  /* ── 小工具（名稱一律加 l3 前綴） ── */
  function l3isSq(n) { var t = Math.round(Math.sqrt(n)); return t * t === n; }
  function l3cf(k, v) { return (k === 1 ? '' : String(k)) + v; }          /* 係數 1 不印 */
  function l3rat(m, n) { var g = gcd(m, n) || 1; return (m / g) + ':' + (n / g); }
  function l3tr(M) { return [[M[0][0], M[1][0], M[2][0]], [M[0][1], M[1][1], M[2][1]], [M[0][2], M[1][2], M[2][2]]]; }
  function l3mat(M) {
    return '\\begin{vmatrix}' + M[0].join('&') + '\\\\' + M[1].join('&') + '\\\\' + M[2].join('&') + '\\end{vmatrix}';
  }
  /* 分數向量的排版：整點就用 (a,b,c)，有分數才用 \left(…\right) */
  function l3vf(v) {
    if (v[0].d === 1 && v[1].d === 1 && v[2].d === 1) return vt([v[0].n, v[1].n, v[2].n]);
    return vtF(v);
  }
  /* A + t(B−A)（A、B 為整點，t 為 F） */
  function l3lerp(A, B, t) {
    return [0, 1, 2].map(function (i) { return Fr.add(F(A[i]), Fr.mul(t, F(B[i] - A[i]))); });
  }
  function l3mid(A, B) { return [F(A[0] + B[0], 2), F(A[1] + B[1], 2), F(A[2] + B[2], 2)]; }
  /* 30°／45°／60° 的 sin、cos，寫成 c√r/d */
  var L3TV = { 30: { s: [1, 1, 2], c: [1, 3, 2] }, 45: { s: [1, 2, 2], c: [1, 2, 2] }, 60: { s: [1, 3, 2], c: [1, 1, 2] } };

  /* ══ L3-1　直徑上的圓周角 ⟹ ∠ACB=90°；桿垂直地面 ⟹ 兩次畢氏 ══ */
  var L31T = (function () {
    var o = [], d, h, L;
    for (d = 2; d <= 48; d += 2) for (h = 3; h <= 48; h++) {
      L = Math.round(Math.sqrt(d * d + h * h));
      if (L * L === d * d + h * h && L <= 60) o.push([d, h, L]);
    }
    return o;
  })();
  L3.polePythag = function (r) {
    r();
    var t = r.pick(L31T), D = t[0], hp = t[1], SL = t[2];
    var th = r.pick([30, 45, 60]), at = r.int(0, 1), v = r.int(0, 2);
    var tv = at === 0 ? L3TV[th].c : L3TV[th].s;          /* ∠CAB=θ ⟹ AC=AB·cosθ；∠CBA=θ ⟹ AC=AB·sinθ */
    var ACt = radTex(D * tv[0], tv[1], tv[2]);
    var AC2 = D * D * tv[0] * tv[0] * tv[1] / (tv[2] * tv[2]);
    var PC2 = hp * hp + AC2;
    var ang = at === 0 ? '\\angle CAB=' + th + '°' : '\\angle CBA=' + th + '°';
    var fn = at === 0 ? '\\cos' : '\\sin';
    var setup = '地面上 ' + T('A') + '、' + T('B') + ' 兩點相距 ' + T(String(D)) + ' 公尺，' + T('C') + ' 在以 ' + T('\\overline{AB}') + ' 為直徑的圓上且 ' + T(ang)
              + '。在 ' + T('A') + ' 點立一根垂直於地面的木桿，桿頂 ' + T('P') + ' 到 ' + T('B') + ' 的距離為 ' + T(String(SL)) + ' 公尺。';
    var hb = '$\\overline{PA}\\perp$ 地面 ⟹ $\\overline{PA}\\perp\\overline{AB}$，桿高 $\\overline{PA}=\\sqrt{' + SL + '^2-' + D + '^2}$。'
           + '$\\overline{AB}$ 是直徑 ⟹ $\\angle ACB=90°$（直徑上的圓周角）⟹ $\\overline{AC}=' + D + fn + th + '°$。'
           + '$\\overline{PA}$ 垂直地面 ⟹ $\\overline{PA}\\perp\\overline{AC}$，再用一次畢氏：$\\overline{PC}=\\sqrt{\\overline{PA}^2+\\overline{AC}^2}$——兩次畢氏接力，不要去算 $\\overline{BC}$。';
    if (v === 0)
      return { q: setup + '求桿頂 ' + T('P') + ' 到 ' + T('C') + ' 的繩索長。',
               a: T(sqrtTex(PC2)) + ' 公尺',
               h: hb, p: { D: D, hp: hp, SL: SL, th: th, at: at, v: 0, ans: { PC2: PC2 } } };
    if (v === 1)
      return { q: setup + '求 (1) 木桿的高　(2) 桿頂 ' + T('P') + ' 到 ' + T('C') + ' 的繩索長。',
               a: '(1) ' + T(String(hp)) + ' 公尺　(2) ' + T(sqrtTex(PC2)) + ' 公尺',
               h: hb, p: { D: D, hp: hp, SL: SL, th: th, at: at, v: 1, ans: { PA: hp, PC2: PC2 } } };
    return { q: setup + '求 (1) ' + T('\\overline{AC}') + '　(2) 桿頂 ' + T('P') + ' 到 ' + T('C') + ' 的繩索長。',
             a: '(1) ' + T(ACt) + ' 公尺　(2) ' + T(sqrtTex(PC2)) + ' 公尺',
             h: hb, p: { D: D, hp: hp, SL: SL, th: th, at: at, v: 2, ans: { AC2: AC2, PC2: PC2 } } };
  };

  /* ══ L3-2　螞蟻爬表面到頂面中心：兩種展開各算一次取小 ══ */
  L3.antUnfold = function (r) {
    r();
    var a, b; do { a = 2 * r.int(1, 6); b = 2 * r.int(1, 6); } while (a === b);
    var H = r.int(3, 14), v = r.int(0, 2);
    var da2 = (a / 2) * (a / 2) + (H + b / 2) * (H + b / 2);      /* 經 a×H 的側面 */
    var db2 = (b / 2) * (b / 2) + (H + a / 2) * (H + a / 2);      /* 經 b×H 的側面 */
    var mn = Math.min(da2, db2), face = da2 <= db2 ? a + '\\times' + H : b + '\\times' + H;
    var setup = '一個長方體的底面是 ' + T(a + '\\times' + b) + ' 的矩形，高為 ' + T(String(H)) + '，' + T('P') + ' 為頂面的中心。'
              + '一隻螞蟻從底面的一個頂點 ' + T('A') + ' 沿著表面爬到 ' + T('P') + '。';
    var hb = '把「側面＋頂面」攤平成同一個平面，爬行路徑就變成平面上的線段。'
           + '經 $' + a + '\\times' + H + '$ 的側面攤平：水平位移 $' + (a / 2) + '$、鉛直位移 $' + H + '+' + (b / 2) + '$；'
           + '經 $' + b + '\\times' + H + '$ 的側面攤平：水平位移 $' + (b / 2) + '$、鉛直位移 $' + H + '+' + (a / 2) + '$。'
           + '兩種都用 $\\sqrt{\\text{水平}^2+\\text{鉛直}^2}$ 算一次再取小的——只算一種是最常見的失分點。';
    if (v === 0)
      return { q: setup + '求最短路徑長。', a: T(sqrtTex(mn)), h: hb,
               p: { a: a, b: b, H: H, v: 0, ans: mn } };
    if (v === 1)
      return { q: setup + '求 (1) 經 ' + T(a + '\\times' + H) + ' 側面展開時的路徑長　(2) 最短路徑長。',
               a: '(1) ' + T(sqrtTex(da2)) + '　(2) ' + T(sqrtTex(mn)), h: hb,
               p: { a: a, b: b, H: H, v: 1, ans: { da2: da2, mn: mn } } };
    return { q: setup + '求 (1) 最短路徑長　(2) 這條最短路徑經過哪一個側面（用該側面的兩邊長表示）。',
             a: '(1) ' + T(sqrtTex(mn)) + '　(2) ' + T(face) + ' 的側面', h: hb,
             p: { a: a, b: b, H: H, v: 2, ans: { mn: mn, face: face } } };
  };

  /* ══ L3-3　正立方體的牆角截面：三邊 √(p²+q²) 型，內積分子恆正 ⟹ 恆為銳角三角形 ══ */
  L3.cornerSection = function (r) {
    r();
    var n = r.pick([4, 5, 6, 7, 8, 9]), p1, p2, p3, v = r.int(0, 2), A2, tries = 0;
    do {
      p1 = r.int(1, n); p2 = r.int(1, n); p3 = r.int(1, n);
      A2 = p1 * p1 * p2 * p2 + p2 * p2 * p3 * p3 + p3 * p3 * p1 * p1;       /* |PQ×PR|² */
      tries++;
    } while ((p1 === p2 && p2 === p3)
             || ((simpSqrt(A2).r > 1500 || (v === 0 && simpSqrt((p1 * p1 + p2 * p2) * (p1 * p1 + p3 * p3)).r > 1500)) && tries < 150));
    var area = sqrtFracTex(A2, 4), dist = sqrtFracTex(p1 * p1 * p2 * p2 * p3 * p3, A2);
    var cosP = sqrtFracTex(p1 * p1 * p1 * p1, (p1 * p1 + p2 * p2) * (p1 * p1 + p3 * p3));
    var setup = '正立方體的邊長為 ' + T(String(n)) + '，' + T('O') + ' 是它的一個頂點。在以 ' + T('O') + ' 為端點的三條稜上分別取 ' + T('P') + '、' + T('Q') + '、' + T('R') + '，'
              + '使 ' + T('\\overline{OP}=' + p1) + '、' + T('\\overline{OQ}=' + p2) + '、' + T('\\overline{OR}=' + p3) + '。';
    var hb = '三條稜兩兩垂直 ⟹ 以 $O$ 為原點、三條稜為坐標軸：$P(' + p1 + ',0,0)$、$Q(0,' + p2 + ',0)$、$R(0,0,' + p3 + ')$。'
           + '$\\overrightarrow{PQ}=(' + (-p1) + ',' + p2 + ',0)$、$\\overrightarrow{PR}=(' + (-p1) + ',0,' + p3 + ')$ ⟹ $\\overrightarrow{PQ}\\times\\overrightarrow{PR}=(' + (p2 * p3) + ',' + (p1 * p3) + ',' + (p1 * p2) + ')$。'
           + '面積 $=\\dfrac12|\\overrightarrow{PQ}\\times\\overrightarrow{PR}|$；'
           + '$\\cos\\angle QPR=\\dfrac{\\overrightarrow{PQ}\\cdot\\overrightarrow{PR}}{|\\overrightarrow{PQ}||\\overrightarrow{PR}|}$，分子 $=' + (p1 * p1) + '\\gt0$ ⟹ 這種截面三角形恆為銳角三角形。';
    if (v === 0)
      return { q: setup + '求 (1) ' + T('\\triangle PQR') + ' 的面積　(2) ' + T('\\cos\\angle QPR') + '。',
               a: '(1) ' + T(area) + '　(2) ' + T(cosP), h: hb,
               p: { n: n, p: [p1, p2, p3], v: 0, ans: { A2: A2 } } };
    if (v === 1)
      return { q: setup + '求 (1) ' + T('\\overline{PQ}') + '、' + T('\\overline{QR}') + '、' + T('\\overline{RP}') + '　(2) ' + T('\\triangle PQR') + ' 的面積。',
               a: '(1) ' + T('\\overline{PQ}=' + sqrtTex(p1 * p1 + p2 * p2)) + '、' + T('\\overline{QR}=' + sqrtTex(p2 * p2 + p3 * p3)) + '、' + T('\\overline{RP}=' + sqrtTex(p3 * p3 + p1 * p1)) + '　(2) ' + T(area),
               h: hb, p: { n: n, p: [p1, p2, p3], v: 1, ans: { A2: A2 } } };
    return { q: setup + '求 (1) ' + T('\\triangle PQR') + ' 的面積　(2) ' + T('O') + ' 到平面 ' + T('PQR') + ' 的距離。',
             a: '(1) ' + T(area) + '　(2) ' + T(dist),
             h: hb + '第 (2) 小題走體積法：$V=\\dfrac16(' + p1 + ')(' + p2 + ')(' + p3 + ')$（牆角型），距離 $=\\dfrac{3V}{S}$。',
             p: { n: n, p: [p1, p2, p3], v: 2, ans: { A2: A2 } } };
  };

  /* ══ L3-4　三稜兩兩垂直 ⟹ 直接放坐標；頂點到對稜的距離用外積 ══ */
  /* (b,c) 取畢氏數對讓 √(b²+c²) 是整數，再挑 h 使最後的根號留下的數不超過 1200 */
  var L34P = (function () {
    var o = [], b, c, h, e, N;
    for (b = 2; b <= 15; b++) for (c = 2; c <= 15; c++) {
      if (b === c) continue;
      e = Math.round(Math.sqrt(b * b + c * c));
      if (e * e !== b * b + c * c) continue;
      for (h = 1; h <= 12; h++) {
        N = h * h * (b * b + c * c) + b * b * c * c;
        if (simpSqrt(N).r <= 1200) o.push([b, c, h]);
      }
    }
    return o;
  })();
  L3.tetraEdgeDist = function (r) {
    r();
    var pk = r.pick(L34P), b = pk[0], c = pk[1], hh = pk[2], v = r.int(0, 2);
    var Dn = b * b + c * c;
    var dD = sqrtFracTex(b * b * c * c, Dn), dA = sqrtFracTex(hh * hh * Dn + b * b * c * c, Dn);
    var V = F(b * c * hh, 6);
    var setup = '四面體 ' + T('ABCD') + ' 中 ' + T('\\overline{AD}\\perp') + ' 平面 ' + T('BCD') + '，' + T('\\overline{BD}\\perp\\overline{CD}') + '，'
              + T('\\overline{AD}=' + hh) + '、' + T('\\overline{BD}=' + b) + '、' + T('\\overline{CD}=' + c) + '。';
    var hb = '三條稜兩兩垂直 ⟹ 以 $D$ 為原點：$B(' + b + ',0,0)$、$C(0,' + c + ',0)$、$A(0,0,' + hh + ')$。'
           + '$\\overrightarrow{BA}=(' + (-b) + ',0,' + hh + ')$、$\\overrightarrow{BC}=(' + (-b) + ',' + c + ',0)$ ⟹ $\\overrightarrow{BA}\\times\\overrightarrow{BC}=(' + (-hh * c) + ',' + (-hh * b) + ',' + (-b * c) + ')$，'
           + '距離 $=\\dfrac{|\\overrightarrow{BA}\\times\\overrightarrow{BC}|}{|\\overrightarrow{BC}|}$。'
           + '三垂線的走法也一樣快：先算 $D$ 到 $\\overline{BC}$ 的距離 $\\dfrac{(' + b + ')(' + c + ')}{\\sqrt{' + b + '^2+' + c + '^2}}$，再和高 $' + hh + '$ 用一次畢氏。';
    if (v === 0)
      return { q: setup + '求 ' + T('A') + ' 到稜 ' + T('\\overline{BC}') + ' 的距離。', a: T(dA), h: hb,
               p: { b: b, c: c, hh: hh, v: 0, ans: dA } };
    if (v === 1)
      return { q: setup + '求 (1) ' + T('D') + ' 到 ' + T('\\overline{BC}') + ' 的距離　(2) ' + T('A') + ' 到 ' + T('\\overline{BC}') + ' 的距離。',
               a: '(1) ' + T(dD) + '　(2) ' + T(dA), h: hb,
               p: { b: b, c: c, hh: hh, v: 1, ans: { dD: dD, dA: dA } } };
    return { q: setup + '求 (1) 四面體 ' + T('ABCD') + ' 的體積　(2) ' + T('A') + ' 到稜 ' + T('\\overline{BC}') + ' 的距離。',
             a: '(1) ' + T(Fr.tex(V)) + '　(2) ' + T(dA),
             h: hb + '體積用牆角型 $V=\\dfrac16\\overline{BD}\\cdot\\overline{CD}\\cdot\\overline{AD}$。',
             p: { b: b, c: c, hh: hh, v: 2, ans: { V: fr2(V), dA: dA } } };
  };

  /* ══ L3-5　三垂線定理：AB⊥平面、BC⊥L ⟹ AC⊥L，三個直角三角形接力 ══ */
  L3.threePerpLine = function (r) {
    r();
    var v = r.int(0, 2), BC, CD, AB2, AD, tries = 0;
    if (r.int(0, 1) === 0) { var pk = r.pick([[3, 4], [4, 3], [6, 8], [8, 6], [5, 12], [12, 5], [9, 12], [12, 9]]); BC = pk[0]; CD = pk[1]; }
    else { do { BC = r.int(2, 12); CD = r.int(2, 12); } while (BC === CD); }
    if (v === 2) { AB2 = r.int(2, 12); }                       /* v=2 時 AB2 就是 AB 本身 */
    else { do { AD = r.int(6, 40); tries++; } while (AD * AD - BC * BC - CD * CD < 3 && tries < 200); }
    var setup0 = '直線 ' + T('AB') + ' 垂直平面 ' + T('E') + ' 於 ' + T('B') + '，' + T('L') + ' 是平面 ' + T('E') + ' 上的一條直線，' + T('D') + ' 在 ' + T('L') + ' 上，且 ' + T('\\overline{BC}\\perp L') + ' 於 ' + T('C') + '。';
    var hb = '$\\overline{AB}\\perp$ 平面 $E$ 且 $\\overline{BC}\\perp L$ ⟹ 三垂線定理給出 $\\overline{AC}\\perp L$。'
           + '於是三個直角三角形接力：$\\overline{BD}^2=\\overline{BC}^2+\\overline{CD}^2=' + (BC * BC) + '+' + (CD * CD) + '$、'
           + '$\\overline{AC}^2=\\overline{AB}^2+\\overline{BC}^2$、$\\overline{AD}^2=\\overline{AB}^2+\\overline{BD}^2=\\overline{AC}^2+\\overline{CD}^2$——三條式子選兩條用就夠了。';
    if (v === 2) {
      var AB = AB2;
      return { q: setup0 + '若 ' + T('\\overline{AB}=' + AB) + '、' + T('\\overline{BC}=' + BC) + '、' + T('\\overline{CD}=' + CD) + '，求 (1) ' + T('\\overline{AC}') + '　(2) ' + T('\\overline{AD}') + '。',
               a: '(1) ' + T(sqrtTex(AB * AB + BC * BC)) + '　(2) ' + T(sqrtTex(AB * AB + BC * BC + CD * CD)), h: hb,
               p: { v: 2, AB: AB, BC: BC, CD: CD, ans: { AC2: AB * AB + BC * BC, AD2: AB * AB + BC * BC + CD * CD } } };
    }
    var ab2 = AD * AD - BC * BC - CD * CD;
    if (v === 0)
      return { q: setup0 + '若 ' + T('\\overline{AD}=' + AD) + '、' + T('\\overline{BC}=' + BC) + '、' + T('\\overline{CD}=' + CD) + '，求 ' + T('\\overline{AB}') + '。',
               a: T(sqrtTex(ab2)), h: hb, p: { v: 0, AD: AD, BC: BC, CD: CD, ans: ab2 } };
    return { q: setup0 + '若 ' + T('\\overline{AD}=' + AD) + '、' + T('\\overline{BC}=' + BC) + '、' + T('\\overline{CD}=' + CD) + '，求 (1) ' + T('\\overline{BD}') + '　(2) ' + T('\\overline{AB}') + '。',
             a: '(1) ' + T(sqrtTex(BC * BC + CD * CD)) + '　(2) ' + T(sqrtTex(ab2)), h: hb,
             p: { v: 1, AD: AD, BC: BC, CD: CD, ans: { BD2: BC * BC + CD * CD, AB2: ab2 } } };
  };

  /* ══ L3-6　投影點 ＝ B+t·BC，t=(BA·BC)/|BC|² ══ */
  L3.cubeProj = function (r) {
    r();
    var n = r.int(1, 4), V = rp(r, -5, 5), vs = [], i, j, k;
    for (i = 0; i < 2; i++) for (j = 0; j < 2; j++) for (k = 0; k < 2; k++) vs.push([V[0] + n * i, V[1] + n * j, V[2] + n * k]);
    var A, B, C, t, sh, tries = 0;
    do {
      sh = r.shuffle(vs); A = sh[0]; B = sh[1]; C = sh[2];
      t = F(dot(sub(A, B), sub(C, B)), n2(sub(C, B))); tries++;
    } while ((t.n === 0 || Fr.eq(t, F(1))) && tries < 80);
    var BC = sub(C, B), BA = sub(A, B), cr = cross(BA, BC);
    var H = l3lerp(B, C, t), v = r.int(0, 2);
    var dist = sqrtFracTex(n2(cr), n2(BC)), area = sqrtFracTex(n2(cross(sub(B, A), sub(C, A))), 4);
    var setup = '正立方體的三個頂點為 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。';
    var hb = '$\\overrightarrow{BC}=' + vt(BC) + '$、$\\overrightarrow{BA}=' + vt(BA) + '$，投影點 $H=B+t\\,\\overrightarrow{BC}$，其中 $t=\\dfrac{\\overrightarrow{BA}\\cdot\\overrightarrow{BC}}{|\\overrightarrow{BC}|^2}$；'
           + '本題 $\\overrightarrow{BA}\\cdot\\overrightarrow{BC}=' + dot(BA, BC) + '$、$|\\overrightarrow{BC}|^2=' + n2(BC) + '$。'
           + '（正立方體的三個頂點之間只會出現稜、面對角線、體對角線三種長度，可以先用距離檢查自己有沒有抄錯坐標。）';
    if (v === 0)
      return { q: setup + '求 ' + T('A') + ' 在直線 ' + T('BC') + ' 上的投影點 ' + T('H') + '。',
               a: T('H' + l3vf(H)), h: hb, p: { A: A, B: B, C: C, v: 0, ans: { t: fr2(t) } } };
    if (v === 1)
      return { q: setup + '求 (1) ' + T('A') + ' 在直線 ' + T('BC') + ' 上的投影點 ' + T('H') + '　(2) ' + T('A') + ' 到直線 ' + T('BC') + ' 的距離。',
               a: '(1) ' + T('H' + l3vf(H)) + '　(2) ' + T(dist),
               h: hb + '距離也可以直接用 $\\dfrac{|\\overrightarrow{BA}\\times\\overrightarrow{BC}|}{|\\overrightarrow{BC}|}$。',
               p: { A: A, B: B, C: C, v: 1, ans: { t: fr2(t) } } };
    return { q: setup + '求 (1) ' + T('A') + ' 在直線 ' + T('BC') + ' 上的投影點 ' + T('H') + '　(2) ' + T('\\triangle ABC') + ' 的面積。',
             a: '(1) ' + T('H' + l3vf(H)) + '　(2) ' + T(area),
             h: hb + '面積用外積：$\\dfrac12|\\overrightarrow{AB}\\times\\overrightarrow{AC}|$。',
             p: { A: A, B: B, C: C, v: 2, ans: { t: fr2(t) } } };
  };

  /* ══ L3-7　兩個分點再求距離：分點公式各寫一次，權重要交叉 ══ */
  L3.twoDivSeg = function (r) {
    r();
    var m, nn, p, q;
    do { m = r.int(1, 3); nn = r.int(1, 3); } while (gcd(m, nn) !== 1);
    do { p = r.int(1, 3); q = r.int(1, 3); } while (gcd(p, q) !== 1);
    var E = rp(r, -4, 4), dv = quad(r), G = add(E, dv);
    var u = rv(r, -3, 3), w = rv(r, -3, 3), v = r.int(0, 2);
    var A = sub(E, sc(m, u)), B = add(E, sc(nn, u)), C = sub(G, sc(p, w)), Dp = add(G, sc(q, w));
    var setup = T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '、' + T('D' + vt(Dp)) + '。'
              + T('E') + '、' + T('F') + ' 分別在 ' + T('\\overline{AB}') + '、' + T('\\overline{CD}') + ' 上，且 '
              + T('\\overline{AE}:\\overline{EB}=' + m + ':' + nn) + '、' + T('\\overline{CF}:\\overline{FD}=' + p + ':' + q) + '。';
    var hb = '分點公式的權重要交叉：離 $B$ 近就給 $B$ 大的權重 ⟹ $E=\\dfrac{' + l3cf(nn, 'A') + '+' + l3cf(m, 'B') + '}{' + (m + nn) + '}$、'
           + '$F=\\dfrac{' + l3cf(q, 'C') + '+' + l3cf(p, 'D') + '}{' + (p + q) + '}$。'
           + '也可以走向量版：$\\overrightarrow{AB}=' + vt(sub(B, A)) + '$、$\\overrightarrow{CD}=' + vt(sub(Dp, C)) + '$ ⟹ $E=A+\\dfrac{' + m + '}{' + (m + nn) + '}\\overrightarrow{AB}$、$F=C+\\dfrac{' + p + '}{' + (p + q) + '}\\overrightarrow{CD}$。'
           + '兩個分點都化成坐標之後，$\\overline{EF}$ 就只是普通的兩點距離——把比例寫反是這一題唯一的陷阱。';
    if (v === 0)
      return { q: setup + '求 ' + T('\\overline{EF}') + '。', a: T(sqrtTex(n2(dv))), h: hb,
               p: { A: A, B: B, C: C, D: Dp, m: m, n: nn, p: p, q: q, v: 0, ans: n2(dv) } };
    if (v === 1)
      return { q: setup + '求 (1) ' + T('E') + '　(2) ' + T('F') + '　(3) ' + T('\\overline{EF}') + '。',
               a: '(1) ' + T('E' + vt(E)) + '　(2) ' + T('F' + vt(G)) + '　(3) ' + T(sqrtTex(n2(dv))), h: hb,
               p: { A: A, B: B, C: C, D: Dp, m: m, n: nn, p: p, q: q, v: 1, ans: { E: E, F: G, d2: n2(dv) } } };
    return { q: setup + '求 (1) ' + T('\\overline{EF}') + '　(2) ' + T('\\overline{EF}') + ' 的中點。',
             a: '(1) ' + T(sqrtTex(n2(dv))) + '　(2) ' + T(l3vf(l3mid(E, G))), h: hb,
             p: { A: A, B: B, C: C, D: Dp, m: m, n: nn, p: p, q: q, v: 2, ans: { d2: n2(dv) } } };
  };

  /* ══ L3-8　三頂點還原正立方體：三段距離平方比 1:2:3，體對角線的中點就是中心 ══ */
  var L38E = [[[1, 0, 0], [0, 1, 0], [0, 0, 1], [2, 4, 6]],
              [[1, 2, 2], [2, 1, -2], [2, -2, 1], [2, 4]],
              [[1, 2, 2], [2, -2, 1], [-2, -1, 2], [2, 4]],
              [[2, 1, 2], [1, 2, -2], [-2, 2, 1], [2, 4]],
              [[2, 2, 1], [2, -1, -2], [1, -2, 2], [2, 4]],
              [[2, 3, 6], [3, -6, 2], [6, 2, -3], [2]],
              [[6, 2, 3], [2, 3, -6], [-3, 6, 2], [2]]];
  L3.cubeCenter = function (r) {
    r();
    var E = r.pick(L38E), k = r.pick(E[3]), pm = r.shuffle([0, 1, 2]);
    var e = [sc(k * r.sign(), E[pm[0]]), sc(k * r.sign(), E[pm[1]]), sc(k * r.sign(), E[pm[2]])];
    var V = rp(r, -6, 6);
    var P1 = V, P2 = add(V, add(e[0], e[1])), P3 = add(V, add(e[0], add(e[1], e[2])));
    var ctr = [(P1[0] + P3[0]) / 2, (P1[1] + P3[1]) / 2, (P1[2] + P3[2]) / 2];
    var side = k * Math.round(Math.sqrt(n2(E[0]))), v = r.int(0, 2);
    var pts = r.shuffle([P1, P2, P3]), A = pts[0], B = pts[1], C = pts[2];
    var dAB = n2(sub(B, A)), dBC = n2(sub(C, B)), dCA = n2(sub(A, C));
    var setup = '正立方體的三個頂點為 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。';
    var hb = '正立方體任兩頂點的距離只有稜 $a$、面對角線 $\\sqrt2\\,a$、體對角線 $\\sqrt3\\,a$ 三種 ⟹ 三段距離的平方比一定是 $1:2:3$。'
           + '先把三個差向量寫出來：$\\overrightarrow{AB}=' + vt(sub(B, A)) + '$、$\\overrightarrow{BC}=' + vt(sub(C, B)) + '$、$\\overrightarrow{CA}=' + vt(sub(A, C)) + '$ ⟹ '
           + '$\\overline{AB}^2=' + dAB + '$、$\\overline{BC}^2=' + dBC + '$、$\\overline{CA}^2=' + dCA + '$。'
           + '平方最大的那一段就是體對角線，而體對角線的中點就是正立方體的中心（不必找出其他五個頂點）。';
    if (v === 0)
      return { q: setup + '求此正立方體的中心。', a: T(vt(ctr)), h: hb,
               p: { A: A, B: B, C: C, v: 0, ans: { ctr: ctr } } };
    if (v === 1)
      return { q: setup + '求 (1) 此正立方體的邊長　(2) 此正立方體的中心。',
               a: '(1) ' + T(String(side)) + '　(2) ' + T(vt(ctr)), h: hb,
               p: { A: A, B: B, C: C, v: 1, ans: { side: side, ctr: ctr } } };
    return { q: setup + '求 (1) 此正立方體的中心　(2) 此正立方體的體積。',
             a: '(1) ' + T(vt(ctr)) + '　(2) ' + T(String(side * side * side)),
             h: hb + '邊長 $a$ 由平方最小的那一段開出來，體積就是 $a^3$。',
             p: { A: A, B: B, C: C, v: 2, ans: { ctr: ctr, vol: side * side * side } } };
  };

  /* ══ L3-9　線段交坐標平面：寫成 A+t·AB，令缺席的坐標為 0 解 t ══ */
  L3.segPlaneHit = function (r) {
    r();
    var k = r.int(0, 2), v = r.int(0, 2), lim = v === 2 ? 6 : 9, tries = 0;
    var A, B, den, nums, oc2;
    do {
      A = rp(r, -lim, lim); B = rp(r, -lim, lim);
      A[k] = r.int(1, lim); B[k] = -r.int(1, lim);
      den = A[k] - B[k];
      nums = [0, 1, 2].map(function (i) { return A[k] * B[i] - A[i] * B[k]; });
      oc2 = nums[0] * nums[0] + nums[1] * nums[1] + nums[2] * nums[2];
      tries++;
    } while (((A[(k + 1) % 3] === B[(k + 1) % 3] && A[(k + 2) % 3] === B[(k + 2) % 3])
              || (v === 2 && simpSqrt(oc2 * den * den).r > 1500)) && tries < 150);
    var t = F(A[k], den), C = l3lerp(A, B, t);
    var PL = ['yz', 'zx', 'xy'][k];
    var setup = T('A' + vt(A)) + '、' + T('B' + vt(B)) + '。若線段 ' + T('\\overline{AB}') + ' 交 ' + T(PL) + ' 平面於 ' + T('C') + '，';
    var hb = '$' + PL + '$ 平面就是 $' + AXES[k] + '=0$。把 $C$ 寫成 $C=A+t\\,\\overrightarrow{AB}$，'
           + '只看 $' + AXES[k] + '$ 分量：$' + A[k] + '+t(' + B[k] + '-' + A[k] + ')=0$ ⟹ 先解出 $t$ 再代回另外兩個分量。'
           + '$A$、$B$ 的 $' + AXES[k] + '$ 坐標一正一負 ⟹ $0\\lt t\\lt1$，交點真的落在線段上；'
           + '而 $\\overline{AC}:\\overline{CB}=t:(1-t)$，也就是兩個 $' + AXES[k] + '$ 坐標的絕對值比。';
    if (v === 0)
      return { q: setup + '求 ' + T('C') + '。', a: T('C' + l3vf(C)), h: hb,
               p: { A: A, B: B, k: k, v: 0, ans: { t: fr2(t) } } };
    if (v === 1)
      return { q: setup + '求 (1) ' + T('C') + '　(2) ' + T('\\overline{AC}:\\overline{CB}') + '。',
               a: '(1) ' + T('C' + l3vf(C)) + '　(2) ' + T(l3rat(A[k], -B[k])), h: hb,
               p: { A: A, B: B, k: k, v: 1, ans: { t: fr2(t) } } };
    return { q: setup + '求 (1) ' + T('C') + '　(2) ' + T('\\overline{OC}') + '（' + T('O') + ' 為原點）。',
             a: '(1) ' + T('C' + l3vf(C)) + '　(2) ' + T(sqrtFracTex(oc2, den * den)), h: hb,
             p: { A: A, B: B, k: k, v: 2, ans: { t: fr2(t) } } };
  };

  /* ══ L3-10　到三軸的距離：三條「兩個平方和」全部加起來除以 2 ══ */
  var L310S = [[1, 1, 1], [-1, 1, 1], [-1, -1, 1], [1, -1, 1], [1, 1, -1], [-1, 1, -1], [-1, -1, -1], [1, -1, -1]];
  L3.axisDistFind = function (r) {
    r();
    var x, y, z, v = r.int(0, 2);
    do { x = r.int(1, 12); y = r.int(1, 12); z = r.int(1, 12); } while (x === y && y === z);
    var oc = v === 1 ? r.int(1, 8) : 1, sg = L310S[oc - 1];
    var P = [sg[0] * x, sg[1] * y, sg[2] * z];
    var s1 = y * y + z * z, s2 = x * x + z * z, s3 = x * x + y * y, tot = s1 + s2 + s3;
    var setup = '第' + CN[oc] + '卦限的點 ' + T('P') + ' 到 ' + T('x') + ' 軸、' + T('y') + ' 軸、' + T('z') + ' 軸的距離分別為 '
              + T(sqrtTex(s1)) + '、' + T(sqrtTex(s2)) + '、' + T(sqrtTex(s3)) + '。';
    var hb = '設 $P(x,y,z)$，到 $x$ 軸的距離「把 $x$ 丟掉」⟹ $y^2+z^2=' + s1 + '$、$x^2+z^2=' + s2 + '$、$x^2+y^2=' + s3 + '$。'
           + '三式相加得 $2(x^2+y^2+z^2)=' + s1 + '+' + s2 + '+' + s3 + '$——先求出 $x^2+y^2+z^2$，再拿它逐一減掉每一式就得到 $x^2$、$y^2$、$z^2$。'
           + '最後由「第' + CN[oc] + '卦限」決定三個坐標的正負。';
    if (v === 2)
      return { q: setup + '求 (1) ' + T('\\overline{OP}') + '（' + T('O') + ' 為原點）　(2) ' + T('P') + '。',
               a: '(1) ' + T(sqrtTex(tot / 2)) + '　(2) ' + T('P' + vt(P)), h: hb,
               p: { P: P, v: 2, ans: { OP2: tot / 2 } } };
    return { q: setup + '求 ' + T('P') + '。', a: T('P' + vt(P)), h: hb,
             p: { P: P, oc: oc, v: v, ans: { P: P } } };
  };

  /* ══ L3-11　底面矩形＋四根不等高的柱子：四個頂點坐標一寫出來就全部解決 ══ */
  L3.pillarsRect = function (r) {
    r();
    var v = r.int(0, 2), aa, bb, h1, h2, h3, h4, tries = 0, ok;
    /* 先挑到「該小題用到的外積長恰好是整數或半整數」的一組，讓面積不會出現又長又醜的根號 */
    do {
      aa = r.int(3, 9); bb = r.int(3, 9);
      h1 = r.int(3, 12); h2 = r.int(3, 12); h3 = r.int(3, 12); h4 = r.int(3, 12);
      ok = !(h1 + h3 === h2 + h4) && !(h1 === h2 && h2 === h3 && h3 === h4);
      if (ok && v === 0) ok = l3isSq(n2(cross([aa, bb, h3 - h1], [0, bb, h4 - h1])));
      if (ok && v === 1) ok = l3isSq(n2(cross([aa, 0, h2 - h1], [aa, bb, h3 - h1])));
      tries++;
    } while (!ok && tries < 400);
    var P = [0, 0, h1], Q = [aa, 0, h2], R = [aa, bb, h3], S = [0, bb, h4];
    var QS2 = n2(sub(S, Q)), PR2 = n2(sub(R, P));
    var cr1 = cross(sub(R, P), sub(S, P)), cr2 = cross(sub(Q, P), sub(R, P));
    var vol = F(aa * bb * Math.abs(h2 + h4 - h1 - h3), 6);
    var setup = '一件雕刻品的底面 ' + T('ABCD') + ' 為矩形，' + T('\\overline{AB}=' + aa) + '、' + T('\\overline{BC}=' + bb) + '；'
              + T('\\overline{AP}') + '、' + T('\\overline{BQ}') + '、' + T('\\overline{CR}') + '、' + T('\\overline{DS}') + ' 都垂直於底面且在同一側，'
              + T('\\overline{AP}=' + h1) + '、' + T('\\overline{BQ}=' + h2) + '、' + T('\\overline{CR}=' + h3) + '、' + T('\\overline{DS}=' + h4) + '。';
    var hb = '把底面放進坐標平面：$A(0,0,0)$、$B(' + aa + ',0,0)$、$C(' + aa + ',' + bb + ',0)$、$D(0,' + bb + ',0)$ ⟹ '
           + '$P(0,0,' + h1 + ')$、$Q(' + aa + ',0,' + h2 + ')$、$R(' + aa + ',' + bb + ',' + h3 + ')$、$S(0,' + bb + ',' + h4 + ')$。'
           + '四個頂點一寫出來，長度就是兩點距離、三角形面積就是兩個邊向量外積長的一半、四面體體積就是 $\\dfrac16|\\det|$。';
    if (v === 0)
      return { q: setup + '求 (1) ' + T('\\overline{QS}') + '　(2) ' + T('\\triangle PRS') + ' 的面積。',
               a: '(1) ' + T(sqrtTex(QS2)) + '　(2) ' + T(sqrtFracTex(n2(cr1), 4)),
               h: hb + '第 (2) 小題：$\\overrightarrow{PR}=' + vt(sub(R, P)) + '$、$\\overrightarrow{PS}=' + vt(sub(S, P)) + '$。',
               p: { aa: aa, bb: bb, h: [h1, h2, h3, h4], v: 0, ans: { QS2: QS2 } } };
    if (v === 1)
      return { q: setup + '求 (1) ' + T('\\overline{PR}') + '　(2) ' + T('\\triangle PQR') + ' 的面積。',
               a: '(1) ' + T(sqrtTex(PR2)) + '　(2) ' + T(sqrtFracTex(n2(cr2), 4)),
               h: hb + '第 (2) 小題：$\\overrightarrow{PQ}=' + vt(sub(Q, P)) + '$、$\\overrightarrow{PR}=' + vt(sub(R, P)) + '$。',
               p: { aa: aa, bb: bb, h: [h1, h2, h3, h4], v: 1, ans: { PR2: PR2 } } };
    return { q: setup + '求 (1) ' + T('\\overline{QS}') + '　(2) 四面體 ' + T('PQRS') + ' 的體積。',
             a: '(1) ' + T(sqrtTex(QS2)) + '　(2) ' + T(Fr.tex(vol)),
             h: hb + '第 (2) 小題：$V=\\dfrac16|\\det(\\overrightarrow{PQ},\\overrightarrow{PR},\\overrightarrow{PS})|$，其中 $\\overrightarrow{PQ}=' + vt(sub(Q, P)) + '$、$\\overrightarrow{PR}=' + vt(sub(R, P)) + '$、$\\overrightarrow{PS}=' + vt(sub(S, P)) + '$。',
             p: { aa: aa, bb: bb, h: [h1, h2, h3, h4], v: 2, ans: { QS2: QS2, vol: fr2(vol) } } };
  };

  /* ══ L3-12　AP+BP 最小、P 在坐標平面上：把 A 鏡射過去，連線與平面的交點 ══ */
  L3.mirrorMinPlane = function (r) {
    r();
    var k = r.int(0, 2), v = r.int(0, 2), sg = r.sign(), tries = 0;
    var A = rp(r, -9, 9), B = rp(r, -9, 9);
    A[k] = sg * r.int(1, 9); B[k] = sg * r.int(1, 9);
    while (A[(k + 1) % 3] === B[(k + 1) % 3] && A[(k + 2) % 3] === B[(k + 2) % 3] && tries < 40) { B[(k + 2) % 3] = r.int(-9, 9); tries++; }
    var Am = A.slice(); Am[k] = -A[k];
    var den = A[k] + B[k], t = F(A[k], den), P = l3lerp(Am, B, t);
    var M2 = n2(sub(B, Am)), PL = ['yz', 'zx', 'xy'][k];
    var setup = T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，' + T('P') + ' 為 ' + T(PL) + ' 平面上的一點。當 ' + T('\\overline{AP}+\\overline{BP}') + ' 最小時，';
    var hb = '$A$、$B$ 的 $' + AXES[k] + '$ 坐標同號 ⟹ 兩點在 $' + PL + '$ 平面的同側，不能直接連 $\\overline{AB}$。'
           + '把 $A$ 對 $' + PL + '$ 平面鏡射成 $A^\\prime' + vt(Am) + '$（只有 $' + AXES[k] + '$ 變號），則對平面上任一點 $P$ 都有 $\\overline{AP}=\\overline{A^\\prime P}$ ⟹ '
           + '$\\overline{AP}+\\overline{BP}=\\overline{A^\\prime P}+\\overline{BP}\\ge\\overline{A^\\prime B}$，等號在 $P$ 落在線段 $\\overline{A^\\prime B}$ 上時。'
           + '所以寫 $P=A^\\prime+t\\,\\overrightarrow{A^\\prime B}$ 並令 $' + AXES[k] + '$ 分量為 $0$ 解 $t$。';
    if (v === 0)
      return { q: setup + '求 ' + T('P') + '。', a: T('P' + l3vf(P)), h: hb,
               p: { A: A, B: B, k: k, v: 0, ans: { t: fr2(t) } } };
    if (v === 1)
      return { q: setup + '求 (1) ' + T('\\overline{AP}+\\overline{BP}') + ' 的最小值　(2) 此時的 ' + T('P') + '。',
               a: '(1) ' + T(sqrtTex(M2)) + '　(2) ' + T('P' + l3vf(P)), h: hb,
               p: { A: A, B: B, k: k, v: 1, ans: { M2: M2 } } };
    return { q: setup + '求 (1) 此時的 ' + T('P') + '　(2) 此時的 ' + T('\\overline{AP}') + '。',
             a: '(1) ' + T('P' + l3vf(P)) + '　(2) ' + T(sqrtFracTex(A[k] * A[k] * M2, den * den)), h: hb,
             p: { A: A, B: B, k: k, v: 2, ans: { M2: M2 } } };
  };

  /* ══ L3-13　一個外積兩題用：面積＝半長、點到直線的距離＝長÷底 ══ */
  L3.crossAreaDist = function (r) {
    r();
    var Q = rp(r, -6, 6), u, w, cr, tries = 0;
    do { u = quad(r); w = rv(r, -6, 6); cr = cross(w, u); tries++; }
    while ((isZero(cr) || !l3isSq(n2(cr)) || dot(w, u) === 0 || dot(w, u) === n2(u)) && tries < 250);
    while (isZero(cr) || dot(w, u) === 0 || dot(w, u) === n2(u)) { u = quad(r); w = rv(r, -6, 6); cr = cross(w, u); }   /* 投影點不要剛好落在 Q 或 R 上（t=0、1） */
    var P = add(Q, w), R = add(Q, u), v = r.int(0, 2);
    var area = sqrtFracTex(n2(cr), 4), dP = sqrtFracTex(n2(cr), n2(u)), dQ = sqrtFracTex(n2(cr), n2(sub(u, w)));
    var t = F(dot(w, u), n2(u)), H = l3lerp(Q, R, t);
    var setup = T('P' + vt(P)) + '、' + T('Q' + vt(Q)) + '、' + T('R' + vt(R)) + '。';
    var hb = '一個外積兩題用：$\\overrightarrow{QP}=' + vt(w) + '$、$\\overrightarrow{QR}=' + vt(u) + '$ ⟹ $\\overrightarrow{QP}\\times\\overrightarrow{QR}=' + vt(cr) + '$。'
           + '$\\triangle PQR$ 的面積 $=\\dfrac12|\\overrightarrow{QP}\\times\\overrightarrow{QR}|$；'
           + '而「面積 $=\\dfrac12\\times$ 底 $\\times$ 高」⟹ 點到直線的距離 $=\\dfrac{|\\overrightarrow{QP}\\times\\overrightarrow{QR}|}{\\text{那條底邊的長}}$——分母換成哪一條底邊，就是哪一個頂點的距離。';
    if (v === 0)
      return { q: setup + '求 (1) ' + T('\\triangle PQR') + ' 的面積　(2) ' + T('P') + ' 到直線 ' + T('QR') + ' 的距離。',
               a: '(1) ' + T(area) + '　(2) ' + T(dP), h: hb,
               p: { P: P, Q: Q, R: R, v: 0, ans: { cr2: n2(cr) } } };
    if (v === 1)
      return { q: setup + '求 (1) ' + T('\\triangle PQR') + ' 的面積　(2) ' + T('Q') + ' 到直線 ' + T('PR') + ' 的距離。',
               a: '(1) ' + T(area) + '　(2) ' + T(dQ),
               h: hb + '本題的底邊是 $\\overline{PR}$，$\\overrightarrow{PR}=' + vt(sub(u, w)) + '$。',
               p: { P: P, Q: Q, R: R, v: 1, ans: { cr2: n2(cr) } } };
    return { q: setup + '求 (1) ' + T('\\triangle PQR') + ' 的面積　(2) ' + T('P') + ' 在直線 ' + T('QR') + ' 上的投影點 ' + T('H') + '。',
             a: '(1) ' + T(area) + '　(2) ' + T('H' + l3vf(H)),
             h: hb + '投影點另外算：$H=Q+t\\,\\overrightarrow{QR}$，$t=\\dfrac{\\overrightarrow{QP}\\cdot\\overrightarrow{QR}}{|\\overrightarrow{QR}|^2}=\\dfrac{' + dot(w, u) + '}{' + n2(u) + '}' + (gcd(dot(w, u), n2(u)) > 1 ? '=' + Fr.tex(t) : '') + '$。',
             p: { P: P, Q: Q, R: R, v: 2, ans: { cr2: n2(cr), t: fr2(t) } } };
  };

  /* ══ L3-14　|b| 固定求 a·b 的最大值：等號在同向 ⟹ b=(|b|/|a|)a ══ */
  L3.maxDotVec = function (r) {
    r();
    var a = quad(r), m = r.int(2, 15), v = r.int(0, 2);
    var L = Math.round(Math.sqrt(n2(a))), bv = [F(m * a[0], L), F(m * a[1], L), F(m * a[2], L)];
    var sq = function (x) { return (x < 0 ? '(' + x + ')' : String(x)) + '^2'; };
    var hb = '$|\\vec a|=\\sqrt{' + sq(a[0]) + '+' + sq(a[1]) + '+' + sq(a[2]) + '}$。$\\vec a\\cdot\\vec b=|\\vec a||\\vec b|\\cos\\theta$ 而 $-1\\le\\cos\\theta\\le1$ ⟹ '
           + '$-|\\vec a||\\vec b|\\le\\vec a\\cdot\\vec b\\le|\\vec a||\\vec b|$，最大值在 $\\vec b$ 與 $\\vec a$ 同向時取到，此時 $\\vec b=\\dfrac{|\\vec b|}{|\\vec a|}\\vec a=\\dfrac{' + m + '}{|\\vec a|}\\vec a$。'
           + '（這就是柯西不等式 $(x^2+y^2+z^2)(' + n2(a) + ')\\ge(' + term(a[0], 'x', true) + term(a[1], 'y', false) + term(a[2], 'z', false) + ')^2$ 的等號條件。）';
    if (v === 2)
      return { q: '設 ' + T('x,y,z') + ' 為實數且 ' + T('x^2+y^2+z^2=' + (m * m)) + '。求 (1) ' + T(term(a[0], 'x', true) + term(a[1], 'y', false) + term(a[2], 'z', false)) + ' 的最大值　(2) 此時的 ' + T('(x,y,z)') + '。',
               a: '(1) ' + T(String(L * m)) + '　(2) ' + T(l3vf(bv)), h: hb,
               p: { a: a, m: m, v: 2, ans: { mx: L * m } } };
    if (v === 1)
      return { q: '設 ' + T('\\vec a=' + vt(a)) + '、' + T('\\vec b=(x,y,z)') + ' 且 ' + T('|\\vec b|=' + m) + '。求 (1) ' + T('\\vec a\\cdot\\vec b') + ' 的最大值與最小值　(2) 取到最大值時的 ' + T('\\vec b') + '。',
               a: '(1) 最大值 ' + T(String(L * m)) + '、最小值 ' + T(String(-L * m)) + '　(2) ' + T('\\vec b=' + l3vf(bv)), h: hb,
               p: { a: a, m: m, v: 1, ans: { mx: L * m } } };
    return { q: '設 ' + T('\\vec a=' + vt(a)) + '、' + T('\\vec b=(x,y,z)') + ' 且 ' + T('|\\vec b|=' + m) + '。求 (1) ' + T('\\vec a\\cdot\\vec b') + ' 的最大值　(2) 此時的 ' + T('\\vec b') + '。',
             a: '(1) ' + T(String(L * m)) + '　(2) ' + T('\\vec b=' + l3vf(bv)), h: hb,
             p: { a: a, m: m, v: 0, ans: { mx: L * m } } };
  };

  /* ══ L3-15　數字很接近的行列式：先用「列減列」（行減行）把數字變小，再提公因數 ══ */
  L3.detCloseRows = function (r) {
    r();
    var v = r.int(0, 2), d, u, w, M, base, tries = 0, dt = 0;
    do {
      d = r.int(2, 6);
      var bw = r.int(10, 20), bu = r.int(8, 16);
      w = [bw + r.int(-2, 2), bw + r.int(-2, 2), bw + r.int(-2, 2)];
      u = [bu + r.int(-2, 2), bu + r.int(-2, 2), bu + r.int(-2, 2)];
      dt = d * det3([1, 1, 1], u, w);
      tries++;
    } while ((dt === 0 || Math.abs(dt) > 400) && tries < 300);
    var dd = [d, d, d];
    if (v === 2) { base = [add(add(w, dd), u), add(w, dd), w]; }        /* 第二列減第三列得常數列 */
    else { base = [add(add(w, u), dd), add(w, u), w]; }                 /* 第一列減第二列得常數列 */
    M = v === 1 ? l3tr(base) : base;
    var val = det3(M[0], M[1], M[2]);
    var red = v === 2 ? [u, dd, w] : [dd, u, w];
    var red1 = v === 2 ? [u, [1, 1, 1], w] : [[1, 1, 1], u, w];
    var hb, ln = v === 1 ? '行' : '列';
    if (v === 1)
      hb = '三個直行的數字很接近 ⟹ 先做「行減行」（行列式的值不變）：第一行減第二行整行都變成 $' + d + '$、第二行減第三行變成 ' + T(vt(u)) + ' 那一行 ⟹ '
         + '行列式 $=' + l3mat(l3tr(red)) + '$，再從第一行提出公因數 $' + d + '$ 得 $' + d + l3mat(l3tr(red1)) + '$，剩下的用全是 $1$ 的那一行展開。';
    else
      hb = '三個橫列的數字很接近 ⟹ 先做「列減列」（行列式的值不變）：' + (v === 2 ? '第二列減第三列得 $' + vt(dd) + '$、第一列減第二列得 $' + vt(u) + '$' : '第一列減第二列得 $' + vt(dd) + '$、第二列減第三列得 $' + vt(u) + '$')
         + ' ⟹ 行列式 $=' + l3mat(red) + '$，再從那一列提出公因數 $' + d + '$ 得 $' + d + l3mat(red1) + '$，剩下的用 $(1,1,1)$ 那一列展開。';
    if (v === 2)
      return { q: '設 ' + T('\\Delta=' + l3mat(M)) + '。求 (1) ' + T('\\Delta') + ' 的值　(2) 以 ' + T('\\Delta') + ' 的三個列向量為稜的平行六面體體積。',
               a: '(1) ' + T(String(val)) + '　(2) ' + T(String(Math.abs(val))),
               h: hb + '平行六面體的體積就是行列式的絕對值。',
               p: { M: M, d: d, v: 2, ans: { val: val } } };
    return { q: '計算行列式 ' + T(l3mat(M)) + '。', a: T(String(val)), h: hb,
             p: { M: M, d: d, v: v, ln: ln, ans: val } };
  };

  var META_L3 = [['polePythag', '直徑上的圓周角＋垂直桿：兩次畢氏'], ['antUnfold', '螞蟻爬表面：兩種展開取小'], ['cornerSection', '正立方體的牆角截面三角形'],
                 ['tetraEdgeDist', '三稜兩兩垂直：頂點到對稜的距離'], ['threePerpLine', '三垂線定理：三個直角三角形接力'], ['cubeProj', '正立方體頂點在直線上的投影點'],
                 ['twoDivSeg', '兩個分點再求距離'], ['cubeCenter', '三頂點還原正立方體的中心'], ['segPlaneHit', '線段交坐標平面的交點'],
                 ['axisDistFind', '到三軸的距離反求坐標'], ['pillarsRect', '底面矩形＋四根柱子'], ['mirrorMinPlane', '鏡射求 AP＋BP 的最小值'],
                 ['crossAreaDist', '一個外積：面積與點到直線距離'], ['maxDotVec', '|b| 固定求 a·b 的最大值'], ['detCloseRows', '數字接近的行列式：列減列']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'polePythag', 'L3-2': 'antUnfold', 'L3-3': 'cornerSection', 'L3-4': 'tetraEdgeDist', 'L3-5': 'threePerpLine',
                 'L3-6': 'cubeProj', 'L3-7': 'twoDivSeg', 'L3-8': 'cubeCenter', 'L3-9': 'segPlaneHit', 'L3-10': 'axisDistFind',
                 'L3-11': 'pillarsRect', 'L3-12': 'mirrorMinPlane', 'L3-13': 'crossAreaDist', 'L3-14': 'maxDotVec', 'L3-15': 'detCloseRows' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：兩點距離與中點（高一上 ch2）、平面向量的內積與夾角、垂直與平行的待定係數、二階行列式與三角形面積、分點公式（以上高二上 ch3）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  function l0sn(x) { return x < 0 ? '(' + x + ')' : String(x); }
  function l0pp(x, y) { return '(' + x + ')(' + y + ')'; }                       /* 乘積寫成括號並列：(3)(-2)，因數是 1 也不會印出 1\times */
  function l0kx(k, x) { return (k === 1 ? '' : k) + '(' + x + ')'; }
  function l0pt(P) { return '(' + P[0] + ',' + P[1] + ')'; }
  function l0ptF(x, y) { return (x.d === 1 && y.d === 1) ? '(' + x.n + ',' + y.n + ')' : '\\left(' + Fr.tex(x) + ',\\ ' + Fr.tex(y) + '\\right)'; }
  L0.dist2 = function (r) {
    r();
    var A = [r.int(-7, 7), r.int(-7, 7)], dx = r.nz(-8, 8), dy = r.nz(-8, 8), B = [A[0] + dx, A[1] + dy], d2 = dx * dx + dy * dy;
    var M = [F(A[0] + B[0], 2), F(A[1] + B[1], 2)];
    return { q: '平面上兩點 ' + T('A' + l0pt(A)) + '、' + T('B' + l0pt(B)) + '。求 ' + T('\\overline{AB}') + ' 的長與 ' + T('\\overline{AB}') + ' 的中點坐標。',
             a: T('\\overline{AB}=' + sqrtTex(d2)) + '、中點 ' + T(l0ptF(M[0], M[1])),
             h: '距離：$\\sqrt{' + l0sn(dx) + '^2+' + l0sn(dy) + '^2}=\\sqrt{' + d2 + '}$（兩個坐標差的平方和，開根號後要化簡）；中點：兩個坐標各自取平均。這一章只是多一個 $z$：$\\sqrt{(x_2-x_1)^2+(y_2-y_1)^2+(z_2-z_1)^2}$。',
             p: { A: A, B: B, ans: { d2: d2, M: [fr2(M[0]), fr2(M[1])] } } };
  };
  L0.dot2 = function (r) {
    r();
    var u = [r.nz(-6, 6), r.nz(-6, 6)], v = [r.nz(-6, 6), r.nz(-6, 6)];
    if (r() < 0.3) v = r.pick([[-u[1], u[0]], [u[1], -u[0]], [2 * u[1], -2 * u[0]]]);                 /* 三成機會恰好垂直 */
    var d = u[0] * v[0] + u[1] * v[1], kind = d > 0 ? '銳角' : d < 0 ? '鈍角' : '直角', par = u[0] * v[1] - u[1] * v[0] === 0;
    if (par) { v = [v[0] + 1 || 2, v[1]]; d = u[0] * v[0] + u[1] * v[1]; kind = d > 0 ? '銳角' : d < 0 ? '鈍角' : '直角'; }   /* 避開平行（夾角 0° 或 180°） */
    return { q: '設 ' + T('\\vec u=' + l0pt(u)) + '、' + T('\\vec v=' + l0pt(v)) + '。求 ' + T('\\vec u\\cdot\\vec v') + '，並判斷兩向量的夾角是銳角、直角還是鈍角。',
             a: T('\\vec u\\cdot\\vec v=' + d) + '，夾角是' + kind,
             h: '內積＝對應分量相乘再相加：$' + l0pp(u[0], v[0]) + '+' + l0pp(u[1], v[1]) + '$。內積為正 ⟹ 銳角、為 $0$ ⟹ 直角、為負 ⟹ 鈍角（因為 $\\vec u\\cdot\\vec v=|\\vec u||\\vec v|\\cos\\theta$）。空間向量只是多一項 $z$ 分量的乘積。',
             p: { u: u, v: v, ans: { dot: d, kind: kind } } };
  };
  L0.perpPar2 = function (r) {
    r();
    var a = r.nz(-6, 6), b = r.nz(-6, 6), c = r.nz(-8, 8);
    var tPar = F(b * c, a), tPerp = F(-a * c, b);                                  /* (a,b)∥(c,t)：at=bc；⊥：ac+bt=0 */
    return { q: '設 ' + T('\\vec u=(' + a + ',' + b + ')') + '、' + T('\\vec v=(' + c + ',t)') + '。(1) 若 ' + T('\\vec u\\parallel\\vec v') + '，求 ' + T('t') + '。(2) 若 ' + T('\\vec u\\perp\\vec v') + '，求 ' + T('t') + '。',
             a: '(1) ' + T('t=' + Fr.tex(tPar)) + '　(2) ' + T('t=' + Fr.tex(tPerp)),
             h: '平行 ⟹ 分量成比例：$' + term(a, 't', true) + '=' + l0pp(b, c) + '$；垂直 ⟹ 內積為 $0$：$' + l0pp(a, c) + term(b, 't', false) + '=0$。空間向量的平行要<b>三個</b>分量同時成比例，垂直還是「內積為 $0$」一條式子。',
             p: { u: [a, b], c: c, ans: { par: fr2(tPar), perp: fr2(tPerp) } } };
  };
  L0.det2area = function (r) {
    r();
    var A = [r.int(-6, 6), r.int(-6, 6)], u, v, D, t = 0;
    do { u = [r.nz(-7, 7), r.nz(-7, 7)]; v = [r.nz(-7, 7), r.nz(-7, 7)]; D = u[0] * v[1] - u[1] * v[0]; } while (D === 0 && t++ < 50);
    var B = [A[0] + u[0], A[1] + u[1]], C = [A[0] + v[0], A[1] + v[1]], K = F(Math.abs(D), 2);
    return { q: '平面上三點 ' + T('A' + l0pt(A)) + '、' + T('B' + l0pt(B)) + '、' + T('C' + l0pt(C)) + '。求 ' + T('\\triangle ABC') + ' 的面積。',
             a: T(Fr.tex(K)),
             h: '先求 $\\overrightarrow{AB}=' + l0pt(u) + '$、$\\overrightarrow{AC}=' + l0pt(v) + '$，面積 $=\\dfrac12\\left|\\begin{vmatrix}' + u[0] + '&' + u[1] + '\\\\' + v[0] + '&' + v[1] + '\\end{vmatrix}\\right|$（二階行列式＝交叉相乘相減，別忘了絕對值與 $\\dfrac12$）。這一章把它升級：面積變成外積的長度、三階行列式變成體積。',
             p: { A: A, B: B, C: C, ans: fr2(K) } };
  };
  L0.divPoint2 = function (r) {
    r();
    var A = [r.int(-8, 8), r.int(-8, 8)], B, m = r.int(1, 5), n = r.int(1, 5), g = gcd(m, n); m /= g; n /= g;
    do { B = [r.int(-8, 8), r.int(-8, 8)]; } while (B[0] === A[0] && B[1] === A[1]);
    if (m === n) n = m + 1;                                                       /* 1:1 就是中點，第一型已經考過 */
    var P = [F(n * A[0] + m * B[0], m + n), F(n * A[1] + m * B[1], m + n)];
    return { q: '平面上兩點 ' + T('A' + l0pt(A)) + '、' + T('B' + l0pt(B)) + '，點 ' + T('P') + ' 在線段 ' + T('\\overline{AB}') + ' 上且 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '。求 ' + T('P') + ' 的坐標。',
             a: T('P' + l0ptF(P[0], P[1])),
             h: '分點公式：$\\overrightarrow{OP}=\\dfrac{' + n + '\\,\\overrightarrow{OA}+' + m + '\\,\\overrightarrow{OB}}{' + (m + n) + '}$——<b>交叉乘</b>：靠近 $A$ 的那段 $' + m + '$ 乘在 $B$ 上。$x$ 坐標 $=\\dfrac{' + l0kx(n, A[0]) + '+' + l0kx(m, B[0]) + '}{' + (m + n) + '}$，$y$ 坐標同理；空間的分點公式一模一樣，只是多算一個 $z$。',
             p: { A: A, B: B, m: m, n: n, ans: [fr2(P[0]), fr2(P[1])] } };
  };
  var META_L0 = [['dist2', '兩點距離與中點'], ['dot2', '平面向量的內積與夾角'], ['perpPar2', '平行與垂直：待定係數'], ['det2area', '二階行列式與三角形面積'], ['divPoint2', '分點公式']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    dist2: { txt: '兩點距離與中點（高一上第二章 直線與圓）——空間的距離與中點只是多一個 z', link: '../g10a-ch02/practice.html#L1' },
    dot2: { txt: '平面向量的內積與夾角（高二上第三章 平面向量）——空間的內積、夾角、正射影是同一套', link: '../g11a-ch03/practice.html#L1' },
    perpPar2: { txt: '平行（分量成比例）與垂直（內積為 0）的待定係數（高二上第三章 平面向量）', link: '../g11a-ch03/practice.html#L1' },
    det2area: { txt: '二階行列式與三角形面積（高二上第三章 平面向量）——這一章升級成外積與三階行列式', link: '../g11a-ch03/practice.html#L1' },
    divPoint2: { txt: '分點公式（高二上第三章 平面向量）——空間的分點、重心、係數和判別法都從這裡來', link: '../g11a-ch03/practice.html#L1' }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  var CONTRAST = {
    'L1.octantDist': { f: function (p) { return p.ans.oct <= 4 ? 'up' : 'down'; }, why: '卦限先看 $z$ 的正負分上下：$z\\gt0$ 是第一到第四卦限、$z\\lt0$ 是第五到第八卦限，編號恰好差 $4$；再用 $(x,y)$ 的象限決定是哪一個。距離的算法（到軸「把那個坐標丟掉」、到坐標平面「就是缺的那個坐標的絕對值」）不受正負號影響。' },
    'L1.symProj': { f: function (p) { return p.i < 3 ? 'plane' : p.i < 6 ? 'axis' : 'origin'; }, why: '對<b>坐標平面</b>對稱：只有「名字裡沒出現」的那一個坐標變號（對 $xy$ 平面 ⟹ $z$ 變號）；對<b>坐標軸</b>對稱：軸名以外的兩個坐標變號（對 $x$ 軸 ⟹ $y,z$ 變號）；對<b>原點</b>：三個全部變號。變號的坐標個數依序是 $1,2,3$ 個。' },
    'L1.equidistAxis': { f: function (p) { return p.ax; }, why: '「在哪一個軸上」決定未知點長什麼樣子：$x$ 軸上設 $(t,0,0)$、$y$ 軸上設 $(0,t,0)$、$z$ 軸上設 $(0,0,t)$。列出「到兩點距離的平方相等」後，$t^2$ 會消掉，剩下 $t$ 的一次方程式——兩題的流程一樣，只是 $t$ 放的位置不同。' },
    'L1.divCoef': { f: function (p) { return p.ans.ext; }, why: '$\\overrightarrow{OP}=x\\,\\overrightarrow{OA}+y\\,\\overrightarrow{OB}$ 且 $x+y=1$ ⟹ $P$ 在直線 $AB$ 上。兩個係數<b>都為正</b> ⟹ $P$ 在線段 $\\overline{AB}$ 上（內分）；<b>有一個為負</b> ⟹ $P$ 在延長線上（外分），而且靠近係數為正、絕對值較大的那一端。' },
    'L1.sumLen': { f: function (p) { return p.degs.indexOf(120) >= 0; }, why: '$|\\vec a+\\vec b+\\vec c|^2$ 展開後有三個內積。夾角 $60°$ 的內積為正、$90°$ 為 $0$、$120°$ 為<b>負</b>——只要出現 $120°$，那一項就會把和的長度往下拉。同樣的三個長度，夾角換了，答案可以差很多。' },
    'L1.dotAngle3': { f: function (p) { return p.ans.dot > 0 ? 1 : p.ans.dot < 0 ? -1 : 0; }, why: '夾角是銳角、直角還是鈍角，<b>只看內積的正負</b>就知道（分母 $|\\vec a||\\vec b|$ 恆正）：內積為正 ⟹ $\\cos\\theta\\gt0$ ⟹ 銳角；為 $0$ ⟹ 垂直；為負 ⟹ 鈍角。$\\cos\\theta$ 的值要帶著正負號寫，不要自己取絕對值。' },
    'L1.proj3': { f: function (p) { return p.ans.neg; }, why: '$\\vec a$ 在 $\\vec b$ 上的正射影 $=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|^2}\\,\\vec b$。內積為正 ⟹ 係數為正，正射影與 $\\vec b$ <b>同向</b>；內積為負 ⟹ 係數為負，正射影與 $\\vec b$ <b>反向</b>（夾角是鈍角，影子落在 $\\vec b$ 的反向延長線上）。正射影的<b>長度</b>則一律取絕對值。' },
    'L1.dihedralBox': { f: function (p) { return p.which; }, why: '兩面角先找<b>稜</b>（兩平面的交線），再在兩個面上各找一條<b>垂直於稜</b>的線，它們的夾角就是兩面角。斜面 $ABGH$ 的稜是 $\\overline{AB}$，平面角是 $\\angle DAH$（$\\overline{AD}$、$\\overline{AH}$ 都垂直 $\\overline{AB}$），用到 $\\overline{AD}$ 與 $\\overline{AE}$；斜面 $ADGF$ 的稜是 $\\overline{AD}$，平面角換成 $\\angle BAF$，用到的邊長跟著換成 $\\overline{AB}$ 與 $\\overline{AE}$。' },
    'L1.detProps': { f: function (p) { return p.sw; }, why: '<b>對調</b>兩列（$\\vec a,\\vec b,\\vec c\\to\\vec c,\\vec b,\\vec a$）行列式<b>變號</b>；<b>輪換</b>（$\\vec a,\\vec b,\\vec c\\to\\vec b,\\vec c,\\vec a$）等於對調兩次，行列式<b>不變</b>。判斷方法：數一數要對調幾次才能換回原來的順序，奇數次變號、偶數次不變。' },
    'L2.lineFaceAngle': { f: function (p) { return p.which; }, why: '以 $A$ 為原點坐標化後，四條體對角線的方向向量只差分量的正負號：$\\overrightarrow{AG}=(a,b,c)$、$\\overrightarrow{BH}=(-a,b,c)$、$\\overrightarrow{DF}=(a,-b,c)$。換一條對角線，內積裡變號的那一項就跟著換（$-a^2$ 或 $-b^2$），長度則完全相同。' },
    'L2.cubeCoefDist': { f: function (p) { return p.which; }, why: '以 $A$ 為原點、三條稜為坐標軸，三個係數就是 $P$ 的坐標。到<b>哪一條稜</b>（坐標軸）的距離，就把<b>那個坐標丟掉</b>，剩下兩個坐標的平方和開根號；到哪一個面（坐標平面）的距離，就是名字裡缺的那個坐標。問的軸換了，被丟掉的坐標就跟著換。' },
    'L2.reflectPlane': { f: function (p) { return p.pl; }, why: '光線對坐標平面反射時，<b>只有垂直鏡面的那個分量變號</b>，平行鏡面的兩個分量不變：鏡面是 $xy$ 平面 ⟹ $z$ 分量變號；$yz$ 平面 ⟹ $x$ 分量變號；$zx$ 平面 ⟹ $y$ 分量變號。先寫出入射方向 $\\overrightarrow{PO}$，再依鏡面改一個正負號。' }
  };
  function contrastPair(tier, key, seedA, maxTry) {
    var c = CONTRAST[tier + '.' + key]; if (!c) return null;
    var A = wrapItem(tier, key, seedA), fA = c.f(A.p), keep = c.keep || [];
    for (var n = 1; n < (maxTry || 2000); n++) {
      var s = (seedA * 7919 + n * 104729) % 900000 + 1;                    /* 連號種子的 LCG 首值幾乎相同，要跳著取 */
      var B = wrapItem(tier, key, s);
      if (c.f(B.p) === fA) continue;
      var ok = true; keep.forEach(function (k) { if (JSON.stringify(B.p[k]) !== JSON.stringify(A.p[k])) ok = false; });
      if (!ok || B.q === A.q) continue;
      return { A: A, B: B, seedB: s, why: c.why };
    }
    return null;
  }
  function wrapItem(tier, key, seed) { return ({ L0: L0, L1: L1, L2: L2, L3: L3 })[tier][key](makeRng(seed)); }
  var META = { L0: META_L0, L1: META_L1, L2: META_L2, L3: META_L3 };

  function escMath(s) {
    return String(s).replace(/\$([^$]*)\$/g, function (m, inner) {
      return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ') + '$';
    });
  }
  function wrapAll(group, solMap, h1Map) {
    Object.keys(group).forEach(function (k) {
      var f = group[k];
      group[k] = function (r) {
        var o = f(r); o.q = escMath(o.q); o.a = escMath(o.a); o.h = escMath(o.h);
        if (solMap && solMap[k]) o.s = solMap[k](o.p, o).map(escMath);
        if (h1Map && h1Map[k]) o.h1 = escMath(h1Map[k]);
        return o;
      };
    });
  }
  wrapAll(L0); wrapAll(L1, L1_SOL, L1_H1); wrapAll(L2); wrapAll(L3);

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, dot: dot, cross: cross } };
}));
