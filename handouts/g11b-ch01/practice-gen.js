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

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* 2-1 卦限與各種距離 */
  L1.octantDist = function (r) {
    var P = rv(r, -9, 9), ax = r.int(0, 2), pl = r.int(0, 2);
    var toAx = n2(P) - P[ax] * P[ax], toPl = Math.abs(P[[2, 0, 1][pl]]);
    return { q: '設 ' + T('P' + vt(P)) + '。(1) ' + T('P') + ' 在第幾卦限？(2) 求 ' + T('\\overline{OP}') + '。(3) 求 ' + T('P') + ' 到 ' + T(AXES[ax]) + ' 軸的距離。(4) 求 ' + T('P') + ' 到 ' + T(PLANES[pl]) + ' 平面的距離。',
             a: '(1) 第' + CN[octant(P)] + '卦限　(2) ' + T(sqrtTex(n2(P))) + '　(3) ' + T(sqrtTex(toAx)) + '　(4) ' + T(String(toPl)),
             h: '卦限：先看 $z$ 正負分上下（$1$–$4$ 在上、$5$–$8$ 在下），再依 $(x,y)$ 的象限。到 $' + AXES[ax] + '$ 軸的距離「把 $' + AXES[ax] + '$ 丟掉」；到 $' + PLANES[pl] + '$ 平面的距離就是缺的那個坐標的絕對值。',
             p: { P: P, ax: ax, pl: pl, ans: { oct: octant(P), r2: n2(P), ax2: toAx, pl: toPl } } };
  };

  /* 2-2 對稱點與投影點 */
  L1.symProj = function (r) {
    var P = rv(r, -9, 9), tgts = ['$xy$ 平面', '$yz$ 平面', '$zx$ 平面', '$x$ 軸', '$y$ 軸', '$z$ 軸', '原點'];
    var i = r.int(0, 6), j = r.int(0, 5);
    function sym(P, k) { var Q = P.slice(); if (k === 0) Q[2] = -Q[2]; else if (k === 1) Q[0] = -Q[0]; else if (k === 2) Q[1] = -Q[1]; else if (k === 3) { Q[1] = -Q[1]; Q[2] = -Q[2]; } else if (k === 4) { Q[0] = -Q[0]; Q[2] = -Q[2]; } else if (k === 5) { Q[0] = -Q[0]; Q[1] = -Q[1]; } else Q = sc(-1, Q); return Q; }
    function proj(P, k) { var Q = P.slice(); if (k === 0) Q[2] = 0; else if (k === 1) Q[0] = 0; else if (k === 2) Q[1] = 0; else if (k === 3) { Q[1] = 0; Q[2] = 0; } else if (k === 4) { Q[0] = 0; Q[2] = 0; } else { Q[0] = 0; Q[1] = 0; } return Q; }
    var S = sym(P, i), Q = proj(P, j);
    return { q: '設 ' + T('P' + vt(P)) + '。(1) 求 ' + T('P') + ' 對' + (i === 6 ? '' : ' ') + tgts[i] + '的對稱點。(2) 求 ' + T('P') + ' 在 ' + tgts[j] + '上的投影點。(3) 求 (1) 的對稱點與 ' + T('P') + ' 的距離。',
             a: '(1) ' + T(vt(S)) + '　(2) ' + T(vt(Q)) + '　(3) ' + T(sqrtTex(n2(sub(S, P)))),
             h: '對平面對稱：只有「缺席」的那個坐標變號；對軸對稱：軸名以外的兩個坐標變號；對原點：全部變號。投影：把不在上面的坐標歸零。',
             p: { P: P, i: i, j: j, ans: { S: S, Q: Q, d2: n2(sub(S, P)) } } };
  };

  /* 2-3 分點與中點 */
  L1.midDiv = function (r) {
    var A = rv(r, -8, 8), B; do { B = rv(r, -8, 8); } while (isZero(sub(A, B)));
    var m = r.int(1, 4), n = r.int(1, 4); if (m === n) n += 1;
    var g0 = gcd(m, n); m /= g0; n /= g0;                          /* 2:4 → 1:2 */
    var P = [F(n * A[0] + m * B[0], m + n), F(n * A[1] + m * B[1], m + n), F(n * A[2] + m * B[2], m + n)];
    var M = [F(A[0] + B[0], 2), F(A[1] + B[1], 2), F(A[2] + B[2], 2)];
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '。(1) 求 ' + T('\\overline{AB}') + ' 與中點 ' + T('M') + '。(2) 求 ' + T('\\overline{AB}') + ' 上滿足 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + ' 的點 ' + T('P') + '。',
             a: '(1) ' + T('\\overline{AB}=' + sqrtTex(n2(sub(B, A)))) + '，' + T('M' + vtF(M)) + '　(2) ' + T('P' + vtF(P)),
             h: '內分點「交叉配」：$P=\\dfrac{' + term(n, 'A', true) + term(m, 'B', false) + '}{' + (m + n) + '}$——離 $A$ 近的權重給 $A$。',
             p: { A: A, B: B, m: m, n: n, ans: { d2: n2(sub(B, A)), M: M.map(fr2), P: P.map(fr2) } } };
  };

  /* 2-4 重心反求頂點 */
  L1.centroidC = function (r) {
    var A = rv(r, -7, 7), B = rv(r, -7, 7), C = rv(r, -7, 7), G = [F(A[0] + B[0] + C[0], 3), F(A[1] + B[1] + C[1], 3), F(A[2] + B[2] + C[2], 3)];
    var D = rv(r, -7, 7), G4 = [F(A[0] + B[0] + C[0] + D[0], 4), F(A[1] + B[1] + C[1] + D[1], 4), F(A[2] + B[2] + C[2] + D[2], 4)];
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，' + T('\\triangle ABC') + ' 的重心為 ' + T('G' + vtF(G)) + '。(1) 求 ' + T('C') + '。(2) 若 ' + T('D' + vt(D)) + '，求四面體 ' + T('ABCD') + ' 的重心（四頂點坐標的平均）。',
             a: '(1) ' + T('C' + vt(C)) + '　(2) ' + T(vtF(G4)),
             h: '$C=3G-A-B$，逐坐標算。四面體重心 $=\\dfrac{A+B+C+D}{4}$。',
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
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '。求 ' + T(AXES[ax]) + ' 軸上與 ' + T('A') + '、' + T('B') + ' 等距離的點 ' + T('P') + '，並求 ' + T('\\overline{PA}^2') + '。',
             a: T('P' + vtF(Pt)) + '，' + T('\\overline{PA}^2=' + Fr.tex(PA2)),
             h: '設 $P$ 的 $' + AXES[ax] + '$ 坐標為 $t$、其餘為 $0$；$\\overline{PA}^2=\\overline{PB}^2$ 展開後 $t^2$ 相消，剩下一次方程式。',
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
             h: '分量各自算；單位向量 $=\\dfrac{\\vec a}{|\\vec a|}$。',
             p: { a: a, b: b, k1: k1, k2: k2, ans: { c: c, na: na, nab: n2(add(a, b)) } } };
  };

  /* 3-2 平行：待定分量 */
  L1.parallel3 = function (r) {
    var b = rv(r, -5, 5), k = r.pick([2, 3, -2, -3, -1]), a = sc(k, b), i = r.int(0, 2), j = (i + 1) % 3;
    var kf = F(k);
    return { q: '若 ' + T('(' + [0, 1, 2].map(function (t) { return t === i ? 'm' : t === j ? 'n' : String(a[t]); }).join(',') + ')\\parallel' + vt(b)) + '，求 ' + T('m') + '、' + T('n') + ' 與 ' + T('m+n') + '。',
             a: T('m=' + a[i]) + '、' + T('n=' + a[j]) + '，' + T('m+n=' + (a[i] + a[j])),
             h: '平行 ⟹ 分量成比例：由已知的那個分量先求出倍數 $k=' + Fr.tex(kf, true) + '$，再乘回去。',
             p: { b: b, k: k, i: i, j: j, known: a[3 - i - j], ans: { m: a[i], n: a[j] } } };
  };

  /* 3-3 三點共線：反求坐標 */
  L1.collinear3 = function (r) {
    var A = rv(r, -5, 5), d = rv(r, -4, 4), k = r.pick([2, 3, -1, -2, F(1, 2)]);
    var B = add(A, d), kf = typeof k === 'number' ? F(k) : k;
    var C = [Fr.add(F(A[0]), Fr.mul(kf, F(d[0]))), Fr.add(F(A[1]), Fr.mul(kf, F(d[1]))), Fr.add(F(A[2]), Fr.mul(kf, F(d[2])))];
    if (C.some(function (x) { return x.d !== 1; })) { kf = F(2); C = [F(A[0] + 2 * d[0]), F(A[1] + 2 * d[1]), F(A[2] + 2 * d[2])]; }
    var Cn = C.map(function (x) { return x.n; }), hide = r.int(0, 2);
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C(' + [0, 1, 2].map(function (t) { return t === hide ? 'c' : String(Cn[t]); }).join(',') + ')') + ' 三點共線，求 ' + T('c') + '，並求 ' + T('\\overrightarrow{AC}=k\\,\\overrightarrow{AB}') + ' 中的 ' + T('k') + '。',
             a: T('c=' + Cn[hide]) + '，' + T('k=' + Fr.tex(kf)),
             h: '共線 ⟺ $\\overrightarrow{AC}\\parallel\\overrightarrow{AB}$；用已知的兩個分量先定 $k$，再算缺的那個。',
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
             h: '係數和 $=1$ ⟹ 在直線上；兩係數皆正 ⟹ 在線段內；$\\overline{AP}:\\overline{PB}=|y|:|x|$（$B$ 的係數對應 $\\overline{AP}$）。',
             p: { A: A, B: B, x: fr2(x), y: fr2(y), ans: { P: P.map(fr2), m: m, n: n, ext: ext } } };
  };

  /* 3-5 共平面：線性組合的係數 */
  L1.coplanarComb = function (r) {
    var u, v; do { u = rv(r, -4, 4); v = rv(r, -4, 4); } while (parallel(u, v));
    var p = r.nz(-3, 3), q = r.nz(-3, 3), w = add(sc(p, u), sc(q, v));
    return { q: '設 ' + T(vec('u') + '=' + vt(u)) + '、' + T(vec('v') + '=' + vt(v)) + '、' + T(vec('w') + '=' + vt(w)) + '。(1) 判斷三者是否共平面。(2) 若共平面，把 ' + T(vec('w')) + ' 寫成 ' + T('p\\,' + vec('u') + '+q\\,' + vec('v')) + '。',
             a: '(1) 共平面（' + T('\\det(\\vec u,\\vec v,\\vec w)=0') + '）　(2) ' + T('(p,q)=(' + p + ',' + q + ')'),
             h: '三個分量各一條方程式 $pu_i+qv_i=w_i$，兩個未知數：用兩條解、第三條驗算（驗得過就共平面）。',
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
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '、' + T('D(' + [0, 1, 2].map(function (i) { return i === hide ? 'k' : String(D[i]); }).join(',') + ')') + ' 四點共平面，求 ' + T('k') + '，並把 ' + T(ov('AD')) + ' 寫成 ' + T('s\\,' + ov('AB') + '+t\\,' + ov('AC')) + '。',
             a: T('k=' + D[hide]) + '，' + T('(s,t)=(' + s + ',' + t + ')'),
             h: '四點共平面 ⟺ $\\overrightarrow{AD}=s\\overrightarrow{AB}+t\\overrightarrow{AC}$：用不含 $k$ 的兩個分量解 $s,t$，再代回求 $k$（或用 $\\det=0$）。',
             p: { A: A, B: B, C: C, D: D, hide: hide, ans: { k: D[hide], s: s, t: t } } };
  };

  /* 3-7 三角不等式 */
  L1.triIneq3 = function (r) {
    var la = r.int(2, 9), lb = r.int(2, 9), lo = Math.abs(la - lb), hi = la + lb, m = r.int(lo, hi);
    var dotv = F(m * m - la * la - lb * lb, 2);
    return { q: '設 ' + T('|\\vec a|=' + la) + '、' + T('|\\vec b|=' + lb) + '。(1) 求 ' + T('|\\vec a+\\vec b|') + ' 的範圍。(2) 若又知 ' + T('|\\vec a+\\vec b|=' + m) + '，求 ' + T('\\vec a\\cdot\\vec b') + '。',
             a: '(1) ' + T(lo + '\\le|\\vec a+\\vec b|\\le' + hi) + '　(2) ' + T('\\vec a\\cdot\\vec b=' + Fr.tex(dotv)),
             h: '三角不等式 $\\big||\\vec a|-|\\vec b|\\big|\\le|\\vec a+\\vec b|\\le|\\vec a|+|\\vec b|$；(2) 平方展開 $|\\vec a+\\vec b|^2=|\\vec a|^2+2\\vec a\\cdot\\vec b+|\\vec b|^2$。',
             p: { la: la, lb: lb, m: m, ans: { lo: lo, hi: hi, dot: fr2(dotv) } } };
  };

  /* 3-8 三向量和的長度（夾角 60/90/120） */
  L1.sumLen = function (r) {
    var l = [r.int(1, 5), r.int(1, 5), r.int(1, 5)], degs = [r.pick([60, 90, 120]), r.pick([60, 90, 120]), r.pick([60, 90, 120])];
    var cs = { 60: F(1, 2), 90: F(0), 120: F(-1, 2) };
    var s2 = F(l[0] * l[0] + l[1] * l[1] + l[2] * l[2]);
    s2 = Fr.add(s2, Fr.mul(F(2 * l[0] * l[1]), cs[degs[0]])); s2 = Fr.add(s2, Fr.mul(F(2 * l[1] * l[2]), cs[degs[1]])); s2 = Fr.add(s2, Fr.mul(F(2 * l[2] * l[0]), cs[degs[2]]));
    return { q: '設 ' + T('|\\vec a|=' + l[0]) + '、' + T('|\\vec b|=' + l[1]) + '、' + T('|\\vec c|=' + l[2]) + '，且 ' + T('\\vec a,\\vec b') + ' 夾 ' + T(degs[0] + '^\\circ') + '、' + T('\\vec b,\\vec c') + ' 夾 ' + T(degs[1] + '^\\circ') + '、' + T('\\vec c,\\vec a') + ' 夾 ' + T(degs[2] + '^\\circ') + '。求 ' + T('|\\vec a+\\vec b+\\vec c|') + '。',
             a: T(sqrtTex(s2.n) + (s2.d === 1 ? '' : '\\ \\text{（即 }\\sqrt{' + Fr.tex(s2, true) + '}\\text{）}')),
             h: '求長度先平方：$|\\vec a+\\vec b+\\vec c|^2=\\sum|\\cdot|^2+2(\\vec a\\cdot\\vec b+\\vec b\\cdot\\vec c+\\vec c\\cdot\\vec a)$，內積用 $|\\vec a||\\vec b|\\cos\\theta$。',
             p: { l: l, degs: degs, ans: fr2(s2) } };
  };

  /* 4-1 內積與夾角 */
  L1.dotAngle3 = function (r) {
    var a = rv(r, -5, 5), b = rv(r, -5, 5), d = dot(a, b), na = n2(a), nb = n2(b);
    var cosT = d === 0 ? '0' : sqrtFracTex(d * d, na * nb, d < 0);
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '。(1) 求 ' + T('\\vec a\\cdot\\vec b') + '。(2) 求夾角的餘弦值，並判斷夾角是銳角、直角或鈍角。(3) 求 ' + T('|\\vec a+\\vec b|^2') + '。',
             a: '(1) ' + T(String(d)) + '　(2) ' + T('\\cos\\theta=' + cosT) + '，' + (d > 0 ? '銳角' : d < 0 ? '鈍角' : '直角') + '　(3) ' + T(String(na + nb + 2 * d)),
             h: '$\\cos\\theta=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec a||\\vec b|}$，正負由內積決定；$|\\vec a+\\vec b|^2=|\\vec a|^2+|\\vec b|^2+2\\vec a\\cdot\\vec b$。',
             p: { a: a, b: b, ans: { dot: d, cos2: [d * d, na * nb], nab: na + nb + 2 * d } } };
  };

  /* 4-2 垂直：待定係數 */
  L1.perpT = function (r) {
    var b = rv(r, -5, 5), a = [r.nz(-5, 5), r.nz(-5, 5), 0], i = r.int(0, 2); if (b[i] === 0) b[i] = 1;
    /* a[i] 未知 t：Σ a_j b_j + t b_i = 0 */
    var known = [0, 1, 2].filter(function (j) { return j !== i; }), s = 0;
    var av = rv(r, -5, 5); known.forEach(function (j) { s += av[j] * b[j]; });
    var t = F(-s, b[i]);
    return { q: '若 ' + T('(' + [0, 1, 2].map(function (j) { return j === i ? 't' : String(av[j]); }).join(',') + ')\\perp' + vt(b)) + '，求 ' + T('t') + '。',
             a: T('t=' + Fr.tex(t)),
             h: '垂直 ⟺ 內積為 $0$：一條一次方程式。',
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
             h: '正射影向量 $=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|^2}\\vec b$（分母是平方）；正射影長 $=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|}$（只除一次，可為負）。',
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
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '。(1) 求 ' + T('\\vec a\\times\\vec b') + '。(2) 求 ' + T('|\\vec a\\times\\vec b|') + '。(3) 驗證 ' + T('|\\vec a\\times\\vec b|^2+(\\vec a\\cdot\\vec b)^2=|\\vec a|^2|\\vec b|^2') + '。',
             a: '(1) ' + T(vt(c)) + '　(2) ' + T(sqrtTex(n2(c))) + '　(3) ' + T(n2(c) + '+' + (dot(a, b) * dot(a, b)) + '=' + (n2(a) * n2(b))) + ' ✓',
             h: '外積 $(a_2b_3-a_3b_2,\\ a_3b_1-a_1b_3,\\ a_1b_2-a_2b_1)$，中間那項是「反過來減」；算完用「與 $\\vec a$、$\\vec b$ 內積都是 $0$」檢查。',
             p: { a: a, b: b, ans: { c: c, nc: n2(c) } } };
  };

  /* 4-7 三點決定的三角形面積 */
  L1.area3 = function (r) {
    var A, B, C, cr; do { A = rv(r, -4, 4); B = rv(r, -4, 4); C = rv(r, -4, 4); cr = cross(sub(B, A), sub(C, A)); } while (isZero(cr));
    var n = n2(cr), s = simpSqrt(n), areaT = s.c % 2 === 0 ? sqrtTex(n / 4) : '\\dfrac{' + sqrtTex(n) + '}{2}';
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。(1) 求 ' + T(ov('AB') + '\\times' + ov('AC')) + '。(2) 求 ' + T('\\triangle ABC') + ' 的面積。',
             a: '(1) ' + T(vt(cr)) + '　(2) ' + T(areaT),
             h: '面積 $=\\dfrac12|\\overrightarrow{AB}\\times\\overrightarrow{AC}|$；平行四邊形就不除 $2$。',
             p: { A: A, B: B, C: C, ans: { cr: cr, n: n } } };
  };

  /* 4-8 長方體的兩面角 */
  L1.dihedralBox = function (r) {
    var a = r.int(2, 8), b = r.int(2, 8), c = r.int(2, 8), which = r.int(0, 1);
    /* which=0：底面 ABCD 與平面 ABGH（含稜 AB）：cos = b/√(b²+c²)；which=1：底面與平面 ADFG?（含稜 AD）：cos = a/√(a²+c²) */
    var cos2 = which === 0 ? [b * b, b * b + c * c] : [a * a, a * a + c * c];
    var plane = which === 0 ? 'ABGH' : 'ADFE'.replace('E', 'F').replace('F', 'F');   /* 平面 ADGF：含 AD 與 GF */
    plane = which === 0 ? 'ABGH' : 'ADGF';
    return { q: '長方體 ' + T('ABCD') + '-' + T('EFGH') + ' 中 ' + T('\\overline{AB}=' + a) + '、' + T('\\overline{AD}=' + b) + '、' + T('\\overline{AE}=' + c) + '（' + T('ABCD') + ' 為底面、' + T('\\overline{AE}') + ' 鉛直）。求底面 ' + T('ABCD') + ' 與平面 ' + T(plane) + ' 所夾兩面角的餘弦值。',
             a: T(sqrtFracTex(cos2[0], cos2[1])),
             h: '兩平面的法向量：底面取 $(0,0,1)$；平面 $' + plane + '$ 含 $\\overrightarrow{' + (which === 0 ? 'AB' : 'AD') + '}$ 與 $\\overrightarrow{' + (which === 0 ? 'AH' : 'AF') + '}$，用外積求法向量。也可以直接看平面角：稜是 $\\overline{' + (which === 0 ? 'AB' : 'AD') + '}$，平面角在 $\\overline{' + (which === 0 ? 'AD' : 'AB') + '}$ 與 $\\overline{' + (which === 0 ? 'AH' : 'AF') + '}$ 之間。',
             p: { a: a, b: b, c: c, which: which, ans: cos2 } };
  };

  /* 5-1 三階行列式 */
  L1.det3calc = function (r) {
    var M = [rv(r, -5, 5), rv(r, -5, 5), rv(r, -5, 5)], d = det3(M[0], M[1], M[2]);
    var tex = '\\begin{vmatrix}' + M.map(function (row) { return row.join('&'); }).join('\\\\') + '\\end{vmatrix}';
    return { q: '計算 ' + T(tex) + '。',
             a: T(String(d)),
             h: '沿第一列展開：$a_1(b_2c_3-b_3c_2)-a_2(b_1c_3-b_3c_1)+a_3(b_1c_2-b_2c_1)$；或用「對角線法」六項相加減。',
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
             h: '每一列都是線性的，相同兩列為 $0$：$\\det(p\\vec a+q\\vec b,\\ s\\vec a+t\\vec b,\\ \\vec c)=(pt-qs)\\det(\\vec a,\\vec b,\\vec c)$。對調兩列變號、輪換（$\\vec b,\\vec c,\\vec a$）不變。',
             p: { p: p, q: q, s: s, t: t, D: D, sw: sw, ans: { v1: k * D, v2: sw ? -D : D, v3: Math.abs(k * D) } } };
  };

  /* 5-3 平行六面體與四面體體積 */
  L1.volume3 = function (r) {
    var u, v, w, d; do { u = rv(r, -4, 4); v = rv(r, -4, 4); w = rv(r, -4, 4); d = det3(u, v, w); } while (d === 0);
    return { q: '設 ' + T(vec('u') + '=' + vt(u)) + '、' + T(vec('v') + '=' + vt(v)) + '、' + T(vec('w') + '=' + vt(w)) + '。(1) 求三重積 ' + T('\\vec u\\cdot(\\vec v\\times\\vec w)') + '。(2) 求以三者為邊的平行六面體體積。(3) 求以三者為邊的四面體體積。',
             a: '(1) ' + T(String(d)) + '　(2) ' + T(String(Math.abs(d))) + '　(3) ' + T(Fr.tex(F(Math.abs(d), 6))),
             h: '三重積 $=$ 三階行列式；平行六面體體積是絕對值，四面體再除以 $6$。',
             p: { u: u, v: v, w: w, ans: { d: d } } };
  };

  /* 5-4 牆角型：原點到平面的距離（體積法） */
  L1.ptPlaneAxes = function (r) {
    var a = r.int(1, 6), b = r.int(1, 6), c = r.int(1, 6), N = a * a * b * b + b * b * c * c + c * c * a * a;
    /* d = abc/√N */
    return { q: '設 ' + T('O') + ' 為原點、' + T('A(' + a + ',0,0)') + '、' + T('B(0,' + b + ',0)') + '、' + T('C(0,0,' + c + ')') + '。(1) 求四面體 ' + T('OABC') + ' 的體積。(2) 求 ' + T('\\triangle ABC') + ' 的面積。(3) 求 ' + T('O') + ' 到平面 ' + T('ABC') + ' 的距離。',
             a: '(1) ' + T(Fr.tex(F(a * b * c, 6))) + '　(2) ' + T(radTex(1, N, 2)) + '　(3) ' + T(sqrtFracTex(a * a * b * b * c * c, N)),
             h: '牆角型：$V=\\dfrac{abc}6$；$\\overrightarrow{AB}\\times\\overrightarrow{AC}=(bc,ca,ab)$ 給面積；$d=\\dfrac{3V}{S}$——不需要平面方程式。',
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
             h: '角平分線方向 $=$ 兩個<b>單位</b>向量的和：$\\dfrac{\\overrightarrow{OA}}{' + la + '}+\\dfrac{\\overrightarrow{OB}}{' + lb + '}$，乘 $' + la + '$ 得 $\\overrightarrow{OA}+\\dfrac{' + la + '}{' + lb + '}\\overrightarrow{OB}$。',
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
    var faces = [['BCGF', [1, F(1, 2), F(1, 2)]], ['DCGH', [F(1, 2), 1, F(1, 2)]], ['EFGH', [F(1, 2), F(1, 2), 1]], ['ABFE', [F(1, 2), 0, F(1, 2)]], ['ADHE', [0, F(1, 2), F(1, 2)]], ['ABCD', [F(1, 2), F(1, 2), 0]]];
    var f = r.pick(faces), co = f[1].map(function (v) { return typeof v === 'number' ? F(v) : v; });
    var extra = r.int(0, 1);   /* 再問一個：AG 或 EC 的分解 */
    var seg = extra === 0 ? ['AG', [F(1), F(1), F(1)]] : ['EC', [F(1), F(1), F(-1)]];
    return { q: T('ABCD') + '-' + T('EFGH') + ' 為平行六面體（' + T('ABCD') + ' 為底面，' + T('\\overline{AE}') + ' 為側稜），' + T('J') + ' 為面 ' + T(f[0]) + ' 的中心。(1) 若 ' + T(ov('AJ') + '=a\\,' + ov('AB') + '+b\\,' + ov('AD') + '+c\\,' + ov('AE')) + '，求 ' + T('(a,b,c)') + '。(2) 把 ' + T(ov(seg[0])) + ' 用 ' + T(ov('AB') + ',' + ov('AD') + ',' + ov('AE')) + ' 表示。',
             a: '(1) ' + T('(a,b,c)=' + vtF(co)) + '　(2) ' + T(ov(seg[0]) + '=' + ov('AB') + '+' + ov('AD') + (seg[1][2].n < 0 ? '-' : '+') + ov('AE')),
             h: '面心是該面對角線的中點：$\\overrightarrow{AJ}=\\dfrac{\\overrightarrow{AX}+\\overrightarrow{AY}}2$（$X,Y$ 為對角頂點），每個頂點都先寫成三稜的組合（例如 $\\overrightarrow{AG}=\\overrightarrow{AB}+\\overrightarrow{AD}+\\overrightarrow{AE}$）。',
             p: { face: f[0], extra: extra, ans: { co: co.map(fr2), seg: seg[1].map(fr2) } } };
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
    return { q: '設 ' + T('f(x)=' + tex) + '。(1) 求 ' + T('f(x)') + ' 的常數項。(2) 求 ' + T('f(x)') + ' 的各項係數和。(3) 求各偶次項係數和。(4) 求 ' + T('f(x)') + ' 的次數與領導係數。',
             a: '(1) ' + T(String(f0)) + '　(2) ' + T(String(f1)) + '　(3) ' + T(String((f1 + fm1) / 2)) + '　(4) ' + T((f.length - 1) + '\\text{ 次，領導係數 }' + f[f.length - 1]),
             h: '不要真的乘開：常數項 $=f(0)$、係數和 $=f(1)$、偶次和 $=\\dfrac{f(1)+f(-1)}2$，各代一個數字算行列式；次數與領導係數要看六支乘積中最高次的貢獻。',
             p: { E: E, ans: { f0: f0, f1: f1, even: (f1 + fm1) / 2, deg: f.length - 1, lead: f[f.length - 1], poly: f } } };
  };

  /* 2-9 四面體體積與點到平面距離 */
  L2.tetraDist = function (r) {
    var A, B, C, D, d, cr; do { A = rv(r, -3, 3); B = rv(r, -3, 3); C = rv(r, -3, 3); D = rv(r, -3, 3); cr = cross(sub(B, A), sub(C, A)); d = dot(cr, sub(D, A)); } while (d === 0 || isZero(cr));
    var V = F(Math.abs(d), 6), h2 = [d * d, n2(cr)];
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '、' + T('D' + vt(D)) + '。(1) 求四面體 ' + T('ABCD') + ' 的體積。(2) 求 ' + T('D') + ' 到平面 ' + T('ABC') + ' 的距離。',
             a: '(1) ' + T(Fr.tex(V)) + '　(2) ' + T(sqrtFracTex(h2[0], h2[1])),
             h: '$V=\\dfrac16|\\det(\\overrightarrow{AB},\\overrightarrow{AC},\\overrightarrow{AD})|$；$S=\\dfrac12|\\overrightarrow{AB}\\times\\overrightarrow{AC}|$；$h=\\dfrac{3V}{S}=\\dfrac{|\\det|}{|\\overrightarrow{AB}\\times\\overrightarrow{AC}|}$。',
             p: { A: A, B: B, C: C, D: D, ans: { V: fr2(V), h2: h2 } } };
  };

  /* 2-10 平行四邊形的第四個頂點 */
  L2.fourthVertex = function (r) {
    var A, B, C; do { A = rv(r, -5, 5); B = rv(r, -5, 5); C = rv(r, -5, 5); } while (parallel(sub(B, A), sub(C, A)) || isZero(sub(B, A)) || isZero(sub(C, A)));
    var D1 = sub(add(A, C), B), D2 = sub(add(A, B), C), D3 = sub(add(B, C), A);
    return { q: '空間中 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。求所有能與 ' + T('A,B,C') + ' 構成平行四邊形的第四個頂點 ' + T('D') + '。',
             a: T(vt(D1)) + '、' + T(vt(D2)) + '、' + T(vt(D3)),
             h: '「誰跟誰是對角」有三種配法：對角線互相平分 ⟹ $D=A+C-B$、$A+B-C$、$B+C-A$，三個都要寫。',
             p: { A: A, B: B, C: C, ans: [D1, D2, D3] } };
  };

  /* 2-11 正四面體的五個數字 */
  L2.regularTetra = function (r) {
    var a = r.pick([2, 3, 4, 6, 8, 12]), which = r.int(0, 3);
    var items = [
      ['體高', radTex(a, 6, 3), [a, 6, 3]],                 /* a√6/3 */
      ['體積', radTex(a * a * a, 2, 12), [a * a * a, 2, 12]],   /* a³√2/12 */
      ['外接球半徑（頂點到中心的距離）', radTex(a, 6, 4), [a, 6, 4]],
      ['內切球半徑（中心到面的距離）', radTex(a, 6, 12), [a, 6, 12]]
    ];
    var it = items[which];
    return { q: '正四面體的邊長為 ' + T(String(a)) + '。(1) 求' + it[0] + '。(2) 求相鄰兩面的兩面角的餘弦值。',
             a: '(1) ' + T(it[1]) + '　(2) ' + T('\\dfrac13'),
             h: '邊長 $a$ 的正四面體：底面高 $\\frac{\\sqrt3}{2}a$、重心到頂點 $\\frac{\\sqrt3}{3}a$、體高 $\\frac{\\sqrt6}{3}a$、體積 $\\frac{\\sqrt2}{12}a^3$；中心把體高分成 $3:1$（外接球半徑 $\\frac{\\sqrt6}4a$、內切球半徑 $\\frac{\\sqrt6}{12}a$）；兩面角 $\\cos\\theta=\\frac13$。',
             p: { a: a, which: which, ans: { num: it[2][0], rad: it[2][1], den: it[2][2] } } };
  };

  /* 2-12 點在直線上的投影 */
  L2.projLine3 = function (r) {
    var A = rv(r, -5, 5), C, B; do { C = rv(r, -5, 5); } while (isZero(sub(C, A))); B = rv(r, -5, 5);
    var AC = sub(C, A), t = F(dot(sub(B, A), AC), n2(AC));
    var H = [Fr.add(F(A[0]), Fr.mul(t, F(AC[0]))), Fr.add(F(A[1]), Fr.mul(t, F(AC[1]))), Fr.add(F(A[2]), Fr.mul(t, F(AC[2])))];
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。求 ' + T('B') + ' 在直線 ' + T('AC') + ' 上的投影點 ' + T('H') + '，並說明 ' + T('H') + ' 落在線段 ' + T('\\overline{AC}') + ' 的內部、外部或端點。',
             a: T('H' + vtF(H)) + '，' + (t.n < 0 ? '在 $A$ 的外側' : Fr.eq(t, F(0)) ? '就是 $A$' : t.n < t.d ? '在線段內部' : Fr.eq(t, F(1)) ? '就是 $C$' : '在 $C$ 的外側') + '（' + T('t=' + Fr.tex(t)) + '）',
             h: '$t=\\dfrac{\\overrightarrow{AB}\\cdot\\overrightarrow{AC}}{|\\overrightarrow{AC}|^2}$，投影點 $=A+t\\,\\overrightarrow{AC}$；$0\\le t\\le1$ 才在線段上。',
             p: { A: A, B: B, C: C, ans: { t: fr2(t), H: H.map(fr2) } } };
  };

  /* 2-13 點到直線的距離 */
  L2.ptLineDist = function (r) {
    var A = rv(r, -4, 4), B, P, cr; do { B = rv(r, -4, 4); P = rv(r, -4, 4); cr = cross(sub(P, A), sub(B, A)); } while (isZero(sub(B, A)) || isZero(cr));
    var d2 = [n2(cr), n2(sub(B, A))];
    return { q: '設 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('P' + vt(P)) + '。求 ' + T('P') + ' 到直線 ' + T('AB') + ' 的距離。',
             a: T(sqrtFracTex(d2[0], d2[1])),
             h: '$d=\\dfrac{|\\overrightarrow{AP}\\times\\overrightarrow{AB}|}{|\\overrightarrow{AB}|}$（三角形面積的兩種算法相等）；也可以先求投影點再算距離。',
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
    return { q: '三角錐 ' + T('O') + '-' + T('ABC') + ' 中，在 ' + T('\\overline{OA}') + '、' + T('\\overline{OB}') + '、' + T('\\overline{OC}') + ' 上各取 ' + T('P') + '、' + T('Q') + '、' + T('R') + '，使 ' + T('\\overline{OP}:\\overline{PA}=' + ratios[0][0] + ':' + ratios[0][1]) + '、' + T('\\overline{OQ}:\\overline{QB}=' + ratios[1][0] + ':' + ratios[1][1]) + '、' + T('\\overline{OR}:\\overline{RC}=' + ratios[2][0] + ':' + ratios[2][1]) + '。求 ' + T('V(O\\text{-}PQR):V(O\\text{-}ABC)') + '。',
             a: T(v.n + ':' + v.d),
             h: '三個方向的伸縮比相乘（行列式每一列都是線性的）：$\\dfrac{\\overline{OP}}{\\overline{OA}}\\cdot\\dfrac{\\overline{OQ}}{\\overline{OB}}\\cdot\\dfrac{\\overline{OR}}{\\overline{OC}}$；注意 $' + ratios[0][0] + ':' + ratios[0][1] + '$ 表示佔全長的 $\\frac{' + ratios[0][0] + '}{' + (ratios[0][0] + ratios[0][1]) + '}$。',
             p: { ratios: ratios, ans: fr2(v) } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['octantDist', '§2 卦限與距離'], ['symProj', '§2 對稱點與投影點'], ['midDiv', '§2 分點與中點'], ['centroidC', '§2 重心反求頂點'], ['equidistAxis', '§2 軸上等距點'], ['boxGeom', '§2 長方體體對角線'], ['minSum', '§2 坐標化解最小值'],
      ['vecOps3', '§3 向量基本運算'], ['parallel3', '§3 平行：待定分量'], ['collinear3', '§3 三點共線'], ['divCoef', '§3 係數和判別法'], ['coplanarComb', '§3 共平面與線性組合'], ['fourCoplanar', '§3 四點共平面'], ['triIneq3', '§3 三角不等式'], ['sumLen', '§3 三向量和的長度'],
      ['dotAngle3', '§4 內積與夾角'], ['perpT', '§4 垂直：待定係數'], ['unitPerp', '§4 同時垂直的單位向量'], ['proj3', '§4 正射影'], ['cauchy3', '§4 柯西不等式'], ['cross3', '§4 外積計算'], ['area3', '§4 三角形面積'], ['dihedralBox', '§4 長方體的兩面角'],
      ['det3calc', '§5 三階行列式'], ['detProps', '§5 行列式性質'], ['volume3', '§5 平行六面體與四面體體積'], ['ptPlaneAxes', '§5 牆角型：點到平面（體積法）']
    ],
    L2: [
      ['lineFaceAngle', '§2 兩體對角線的夾角'], ['cubeCoefDist', '§3 係數就是坐標'], ['bisectorT', '§4 角平分線方向'], ['extBisector', '§4 外角平分線交對邊'], ['weightedZero', '§3 加權和為零向量'],
      ['reflectPlane', '§2 鏡面反射'], ['paraCenter', '§3 平行六面體的面心'], ['detPoly', '§5 含 x 的行列式'], ['tetraDist', '§5 四面體體積與點到平面'], ['fourthVertex', '§3 平行四邊形第四頂點'],
      ['regularTetra', '§1 正四面體的五個數字'], ['projLine3', '§4 點在直線上的投影'], ['ptLineDist', '§4 點到直線的距離'], ['cauchyPoint', '§4 平面上的最近點'], ['skewAngleBox', '§1 歪斜線的夾角'], ['volumeRatio', '§5 三角錐體積比']
    ]
  };

  function escMath(s) {
    return String(s).replace(/\$([^$]*)\$/g, function (m, inner) {
      return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ') + '$';
    });
  }
  function wrapAll(group) {
    Object.keys(group).forEach(function (k) {
      var f = group[k];
      group[k] = function (r) { var o = f(r); o.q = escMath(o.q); o.a = escMath(o.a); o.h = escMath(o.h); return o; };
    });
  }
  wrapAll(L1); wrapAll(L2);

  return { makeRng: makeRng, L1: L1, L2: L2, META: META, _util: { gcd: gcd, F: F, Fr: Fr, dot: dot, cross: cross } };
}));
