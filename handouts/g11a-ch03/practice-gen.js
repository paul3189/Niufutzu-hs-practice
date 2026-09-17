/* ══════════════════════════════════════════════════════════════
   g11a-ch03 平面向量・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示                         p：參數與結構化答案（給 verify_gen11c.py 獨立重算）
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
    toNum: function (x) { return x.n / x.d; },
    tex: function (x, small) {
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function simpSqrt(n) { var c = 1, r = n; for (var k = 2; k * k <= r; k++) { while (r % (k * k) === 0) { r /= k * k; c *= k; } } return { c: c, r: r }; }
  function sqrtTex(n) { if (n === 0) return '0'; var s = simpSqrt(n); if (s.r === 1) return String(s.c); return (s.c === 1 ? '' : s.c) + '\\sqrt{' + s.r + '}'; }
  function rootTexF(f) {   /* √(n/d) 的最簡寫法：整數、c√r、\dfrac{c√r}{d} */
    if (f.d === 1) return sqrtTex(f.n);
    var s = simpSqrt(f.n * f.d), k = F(s.c, f.d);
    if (s.r === 1) return Fr.tex(k);
    var body = (k.n === 1 ? '' : k.n) + '\\sqrt{' + s.r + '}';
    return k.d === 1 ? body : '\\dfrac{' + body + '}{' + k.d + '}';
  }
  function T(s) { return '$' + s + '$'; }
  function term(coef, v, first) {
    if (coef === 0) return '';
    var sgn = coef < 0 ? '-' : (first ? '' : '+');
    var ab = Math.abs(coef);
    return sgn + (ab === 1 && v ? '' : ab) + v;
  }
  /* ── 向量工具（陣列 [x,y]）── */
  function vt(v) { return '(' + v[0] + ',' + v[1] + ')'; }
  function vtF(v) { return '\\left(' + Fr.tex(v[0]) + ',\\ ' + Fr.tex(v[1]) + '\\right)'; }
  function add(u, v) { return [u[0] + v[0], u[1] + v[1]]; }
  function sub(u, v) { return [u[0] - v[0], u[1] - v[1]]; }
  function sc(k, v) { return [k * v[0], k * v[1]]; }
  function dot(u, v) { return u[0] * v[0] + u[1] * v[1]; }
  function cross(u, v) { return u[0] * v[1] - u[1] * v[0]; }
  function n2(v) { return dot(v, v); }
  function ov(s) { return '\\overrightarrow{' + s + '}'; }
  function vec(s) { return '\\vec ' + s; }
  function comb(k, s, first) {   /* k·s 的 tex，如 2\vec a、-\vec b */
    if (k === 0) return '';
    var sgn = k < 0 ? '-' : (first ? '' : '+'), ab = Math.abs(k);
    return sgn + (ab === 1 ? '' : ab) + s;
  }
  function combF(k, s, first) {  /* 分數係數 */
    if (k.n === 0) return '';
    var sgn = k.n < 0 ? '-' : (first ? '' : '+'), ab = F(Math.abs(k.n), k.d);
    return sgn + (Fr.eq(ab, F(1)) ? '' : Fr.tex(ab, true)) + s;
  }
  function pt(x, y) { return '(' + x + ',' + y + ')'; }
  function fr2(f) { return [f.n, f.d]; }
  var COS = { 30: [Math.sqrt(3) / 2, '\\dfrac{\\sqrt3}2'], 45: [Math.SQRT1_2, '\\dfrac{\\sqrt2}2'], 60: [0.5, '\\dfrac12'], 90: [0, '0'], 120: [-0.5, '-\\dfrac12'], 135: [-Math.SQRT1_2, '-\\dfrac{\\sqrt2}2'], 150: [-Math.sqrt(3) / 2, '-\\dfrac{\\sqrt3}2'] };
  /* 內積用「係數 × 根號」表示：{c, r} 代表 c·√r（r=1 為整數） */
  function cosR(deg) { return { 30: [1, 3, 2], 45: [1, 2, 2], 60: [1, 1, 2], 90: [0, 1, 1], 120: [-1, 1, 2], 135: [-1, 2, 2], 150: [-1, 3, 2] }[deg]; } /* [sign*num, radicand, den] */
  function radTex(num, rad, den) {  /* num·√rad / den */
    if (num === 0) return '0';
    var g = gcd(num, den); num /= g; den /= g;
    var body = (Math.abs(num) === 1 ? '' : Math.abs(num)) + (rad === 1 ? (Math.abs(num) === 1 ? '1' : '') : '\\sqrt{' + rad + '}');
    if (rad === 1) body = String(Math.abs(num));
    var s = (num < 0 ? '-' : '') + (den === 1 ? body : '\\dfrac{' + body + '}{' + den + '}');
    return s;
  }

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* 1-1 坐標運算 */
  L1.vecOps = function (r) {
    var a = [r.nz(-6, 6), r.nz(-6, 6)], b = [r.nz(-6, 6), r.nz(-6, 6)], k1 = r.pick([2, 3, -2]), k2 = r.pick([1, -1, 2, -3]);
    var ans = add(sc(k1, a), sc(k2, b));
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '，求 ' + T(comb(k1, vec('a'), true) + comb(k2, vec('b'), false)) + ' 與它的長度。',
             a: T(vt(ans)) + '，長度 ' + T(sqrtTex(n2(ans))),
             h: '分量各自算；長度 $=\\sqrt{x^2+y^2}$，根號要化到最簡。',
             p: { a: a, b: b, k1: k1, k2: k2, ans: ans, len2: n2(ans) } };
  };

  /* 1-2 首尾相接化簡 */
  L1.chain = function (r) {
    var L = r.shuffle(['A', 'B', 'C', 'D', 'E']);
    /* 目標 AB+BC+CD-ED = AE？ 隨機產生一串合法首尾相接式 */
    var terms = [], cur = L[0], used = [L[0]];
    for (var i = 1; i < 5; i++) {
      var nxt = L[i], flip = r() < 0.4;
      terms.push(flip ? '-' + ov(nxt + cur) : '+' + ov(cur + nxt)); cur = nxt;
    }
    var expr = terms.join('').replace(/^\+/, '');
    return { q: '化簡 ' + T(expr) + '。',
             a: T(ov(L[0] + L[4])),
             h: '「減一個向量」＝加上它的反向量：$-' + ov('XY') + '=' + ov('YX') + '$；全部翻成同向後首尾相接。',
             p: { start: L[0], end: L[4], expr: expr, ans: L[0] + L[4] } };
  };

  /* 1-3 分點坐標（內分／外分） */
  L1.divPoint = function (r) {
    var A = [r.int(-6, 6), r.int(-6, 6)], B = [r.int(-6, 6), r.int(-6, 6)];
    while (A[0] === B[0] && A[1] === B[1]) B = [r.int(-6, 6), r.int(-6, 6)];
    var m = r.int(1, 4), n = r.int(1, 4); while (m === n) n = r.int(1, 4);
    var ext = r() < 0.4;
    var P = ext ? [F(n * A[0] - m * B[0], n - m), F(n * A[1] - m * B[1], n - m)] : [F(n * A[0] + m * B[0], m + n), F(n * A[1] + m * B[1], m + n)];
    return { q: '已知 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，點 ' + T('P') + (ext ? ' 在直線 $AB$ 上但不在線段 $AB$ 上' : ' 在線段 $AB$ 上') + '，且 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '，求 ' + T('P') + ' 的坐標。',
             a: T('P=' + vtF(P)),
             h: (ext ? '外分：$P=\\dfrac{n\\,A-m\\,B}{n-m}$（把「靠近誰」想清楚，或用 $\\overrightarrow{AP}=\\frac{m}{m-n}\\overrightarrow{AB}$ 的正負判斷）。' : '內分：$P=\\dfrac{n\\,A+m\\,B}{m+n}$——離 $A$ 近的權重給 $A$，也就是「交叉配」。'),
             p: { A: A, B: B, m: m, n: n, ext: ext, ans: [fr2(P[0]), fr2(P[1])] } };
  };

  /* 1-4 重心 */
  L1.centroid = function (r) {
    var A = [r.int(-5, 5), r.int(-5, 5)], B = [r.int(-5, 5), r.int(-5, 5)], G = [r.int(-3, 3), r.int(-3, 3)], C;
    while (true) { C = [3 * G[0] - A[0] - B[0], 3 * G[1] - A[1] - B[1]]; if (cross(sub(B, A), sub(C, A)) !== 0) break; B = [r.int(-5, 5), r.int(-5, 5)]; G = [r.int(-3, 3), r.int(-3, 3)]; }
    return { q: T('\\triangle ABC') + ' 的頂點 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，重心為 ' + T('G' + vt(G)) + '。求 (1) 頂點 ' + T('C') + '　(2) ' + T('\\triangle ABC') + ' 的面積。',
             a: '(1) ' + T('C' + vt(C)) + '　(2) ' + T(Fr.tex(F(Math.abs(cross(sub(B, A), sub(C, A))), 2))),
             h: '重心 $=$ 三頂點平均 ⟹ $C=3G-A-B$；面積 $=\\dfrac12|a_1b_2-a_2b_1|$（兩邊向量的行列式）。',
             p: { A: A, B: B, G: G, ans: { C: C, area2: Math.abs(cross(sub(B, A), sub(C, A))) } } };
  };

  /* 1-5 平行條件 */
  L1.parallelCond = function (r) {
    var b = [r.nz(-4, 4), r.nz(-4, 4)], k = r.pick([2, -2, 3, -3, 1.5, -0.5]);
    var a = [k * b[0], k * b[1]]; if (a[0] % 1 || a[1] % 1) { k = 2; a = [2 * b[0], 2 * b[1]]; }
    var which = r.pick([0, 1]); var shown = a.slice(); var ans = a[which];
    return { q: '設 ' + T(vec('a') + '=' + (which === 0 ? '(x,' + a[1] + ')' : '(' + a[0] + ',x)')) + '、' + T(vec('b') + '=' + vt(b)) + '，若 ' + T(vec('a') + '\\parallel' + vec('b')) + '，求 ' + T('x') + '。',
             a: T('x=' + ans),
             h: '平行 ⟺ 交叉相乘相等：$a_1b_2=a_2b_1$（行列式為 $0$）。',
             p: { b: b, which: which, known: a[1 - which], ans: ans } };
  };

  /* 1-6 三點共線 */
  L1.collinear = function (r) {
    var A = [r.int(-4, 4), r.int(-4, 4)], d = [r.nz(-3, 3), r.nz(-3, 3)], s = r.pick([2, 3, -1, -2]), t = r.pick([1, -1, 4, -3]);
    while (s === t) t = r.pick([1, -1, 4, -3]);
    var B = add(A, sc(s, d)), C = add(A, sc(t, d)), which = r.pick([0, 1]);
    var Cs = which === 0 ? '(x,' + C[1] + ')' : '(' + C[0] + ',x)';
    return { q: '已知 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + Cs) + ' 三點共線，求 ' + T('x') + '。',
             a: T('x=' + C[which]),
             h: '$\\overrightarrow{AB}\\parallel\\overrightarrow{AC}$ ⟹ 交叉相乘相等。',
             p: { A: A, B: B, C: C, which: which, ans: C[which] } };
  };

  /* 1-7 線性組合解係數 */
  L1.linComb = function (r) {
    var a = [r.nz(-3, 3), r.nz(-3, 3)], b = [r.nz(-3, 3), r.nz(-3, 3)];
    while (cross(a, b) === 0) b = [r.nz(-3, 3), r.nz(-3, 3)];
    var x = r.nz(-4, 4), y = r.nz(-4, 4), c = add(sc(x, a), sc(y, b));
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '、' + T(vec('c') + '=' + vt(c)) + '。若 ' + T(vec('c') + '=x' + vec('a') + '+y' + vec('b')) + '，求 ' + T('(x,y)') + '。',
             a: T('(x,y)=' + pt(x, y)),
             h: '分量各寫一條方程式，二元一次聯立；或用克拉瑪：$x=\\dfrac{\\det(\\vec c,\\vec b)}{\\det(\\vec a,\\vec b)}$。',
             p: { a: a, b: b, c: c, ans: [x, y] } };
  };

  /* 1-8 線段上的點：係數判準 */
  L1.segCoef = function (r) {
    var m = r.int(1, 5), n = r.int(1, 5); while (m === n) n = r.int(1, 5);
    var x = F(n, m + n), y = F(m, m + n);
    return { q: '點 ' + T('P') + ' 在線段 ' + T('AB') + ' 上且 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '。若 ' + T(ov('OP') + '=x' + ov('OA') + '+y' + ov('OB')) + '（' + T('O') + ' 為任意點），求 ' + T('(x,y)') + '。',
             a: T('(x,y)=\\left(' + Fr.tex(x) + ',\\ ' + Fr.tex(y) + '\\right)'),
             h: '$\\overrightarrow{OP}=\\overrightarrow{OA}+\\dfrac{m}{m+n}\\overrightarrow{AB}$，展開後「靠近 $A$ 的權重大」；兩係數和必為 $1$。',
             p: { m: m, n: n, ans: [fr2(x), fr2(y)] } };
  };

  /* 1-9 坐標內積與夾角 */
  L1.dotCoord = function (r) {
    var a, b, deg, base = r.pick([[1, 0], [1, 1], [2, 1], [1, 2], [3, 1], [1, 3]]);
    var opts = [[45, [1, 1]], [90, [0, 1]], [135, [-1, 1]], [60, null], [30, null]];
    deg = r.pick([45, 90, 135, 180, 0, 45, 90]);
    var k1 = r.pick([1, 2, 3]), k2 = r.pick([1, 2, 3, -1, -2]);
    a = sc(k1, base);
    var rotd = deg === 45 ? [base[0] - base[1], base[0] + base[1]] : deg === 90 ? [-base[1], base[0]] : deg === 135 ? [-base[0] - base[1], base[0] - base[1]] : deg === 180 ? [-base[0], -base[1]] : base;
    b = sc(Math.abs(k2), rotd);
    if (a[0] === b[0] && a[1] === b[1]) b = sc(2, b);
    var cosv = dot(a, b) / Math.sqrt(n2(a) * n2(b)), ang = Math.round(Math.acos(Math.max(-1, Math.min(1, cosv))) * 180 / Math.PI);
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '，求 ' + T(vec('a') + '\\cdot' + vec('b')) + ' 與兩向量的夾角 ' + T('\\theta') + '。',
             a: T(vec('a') + '\\cdot' + vec('b') + '=' + dot(a, b)) + '，' + T('\\theta=' + ang + '^\\circ'),
             h: '$\\cos\\theta=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec a||\\vec b|}$，先算內積與兩個長度再化簡。',
             p: { a: a, b: b, ans: { dot: dot(a, b), deg: ang } } };
  };

  /* 1-10 長度與夾角給定：求內積與 |a+b| */
  L1.dotLenAngle = function (r) {
    var la = r.int(1, 5), lb = r.int(1, 5), deg = r.pick([60, 120, 90, 60, 120]), k1 = r.pick([1, 2, 3]), k2 = r.pick([1, -1, 2, -2]);
    var d = la * lb * (deg === 60 ? 0.5 : deg === 120 ? -0.5 : 0);        /* 整數或 .5 */
    var dF = F(la * lb * (deg === 60 ? 1 : deg === 120 ? -1 : 0), deg === 90 ? 1 : 2);
    var len2 = Fr.add(Fr.add(F(k1 * k1 * la * la), F(k2 * k2 * lb * lb)), Fr.mul(F(2 * k1 * k2), dF));
    return { q: '設 ' + T('|' + vec('a') + '|=' + la) + '、' + T('|' + vec('b') + '|=' + lb) + '，且 ' + T(vec('a') + ',' + vec('b')) + ' 的夾角為 ' + T(deg + '^\\circ') + '。求 (1) ' + T(vec('a') + '\\cdot' + vec('b')) + '　(2) ' + T('\\left|' + comb(k1, vec('a'), true) + comb(k2, vec('b'), false) + '\\right|') + '。',
             a: '(1) ' + T(Fr.tex(dF)) + '　(2) ' + T(len2.d === 1 ? sqrtTex(len2.n) : '\\sqrt{' + Fr.tex(len2) + '}'),
             h: '長度先平方：$|k_1\\vec a+k_2\\vec b|^2=k_1^2|\\vec a|^2+2k_1k_2\\,\\vec a\\cdot\\vec b+k_2^2|\\vec b|^2$。',
             p: { la: la, lb: lb, deg: deg, k1: k1, k2: k2, ans: { dot: fr2(dF), len2: fr2(len2) } } };
  };

  /* 1-11 垂直條件 */
  L1.perpCond = function (r) {
    var b = [r.nz(-5, 5), r.nz(-5, 5)], k = r.nz(-3, 3), which = r.pick([0, 1]);
    var a = which === 0 ? [k * b[1], -k * b[0]] : [-k * b[1], k * b[0]];   /* a ⊥ b */
    var t = r.nz(-4, 4); a = add(a, [0, 0]);
    /* 題目：a=(x, a1) 或 (a0, x) 與 b 垂直 */
    return { q: '設 ' + T(vec('a') + '=' + (which === 0 ? '(x,' + a[1] + ')' : '(' + a[0] + ',x)')) + '、' + T(vec('b') + '=' + vt(b)) + '，若 ' + T(vec('a') + '\\perp' + vec('b')) + '，求 ' + T('x') + '。',
             a: T('x=' + a[which]),
             h: '垂直 ⟺ 內積為 $0$：$a_1b_1+a_2b_2=0$。',
             p: { b: b, which: which, known: a[1 - which], ans: a[which] } };
  };

  /* 1-12 正射影向量 */
  L1.projVec = function (r) {
    var b = r.pick([[1, 2], [2, 1], [1, 1], [3, 1], [1, 3], [2, -1], [-1, 2], [1, -1], [3, 4], [4, -3]]);
    var k = r.nz(-3, 3), w = [-b[1], b[0]], m = r.nz(-3, 3);
    var a = add(sc(k, b), sc(m, w));   /* a = k b + m w ⇒ 正射影 = k b */
    return { q: '求 ' + T(vec('a') + '=' + vt(a)) + ' 在 ' + T(vec('b') + '=' + vt(b)) + ' 上的正射影（向量）與正射影長。',
             a: '正射影 ' + T(vt(sc(k, b))) + '，長度 ' + T(sqrtTex(k * k * n2(b))),
             h: '正射影 $=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|^2}\\vec b$（分母是平方）；長度 $=\\dfrac{|\\vec a\\cdot\\vec b|}{|\\vec b|}$。',
             p: { a: a, b: b, ans: { proj: sc(k, b), len2: k * k * n2(b) } } };
  };

  /* 1-13 由內積反求夾角 */
  L1.angleFromDot = function (r) {
    var deg = r.pick([30, 45, 60, 90, 120, 135, 150]), c = cosR(deg), la = r.int(1, 4), lb = r.int(1, 4);
    /* a·b = la·lb·num·√rad/den */
    var num = la * lb * c[0], den = c[2], rad = c[1];
    return { q: '設 ' + T('|' + vec('a') + '|=' + la) + '、' + T('|' + vec('b') + '|=' + lb) + '，且 ' + T(vec('a') + '\\cdot' + vec('b') + '=' + radTex(num, rad, den)) + '，求兩向量的夾角。',
             a: T(deg + '^\\circ'),
             h: '$\\cos\\theta=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec a||\\vec b|}$，再查特殊角；負值就是鈍角。',
             p: { la: la, lb: lb, dotNum: num, dotRad: rad, dotDen: den, ans: deg } };
  };

  /* 1-14 三角形面積（行列式） */
  L1.areaDet = function (r) {
    var A = [r.int(-5, 5), r.int(-5, 5)], B = [r.int(-5, 5), r.int(-5, 5)], C = [r.int(-5, 5), r.int(-5, 5)];
    while (cross(sub(B, A), sub(C, A)) === 0) { B = [r.int(-5, 5), r.int(-5, 5)]; C = [r.int(-5, 5), r.int(-5, 5)]; }
    var d = Math.abs(cross(sub(B, A), sub(C, A)));
    return { q: '求以 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + ' 為頂點的三角形面積。',
             a: T(Fr.tex(F(d, 2))),
             h: '$\\overrightarrow{AB}=(a_1,a_2)$、$\\overrightarrow{AC}=(b_1,b_2)$，面積 $=\\dfrac12|a_1b_2-a_2b_1|$。',
             p: { A: A, B: B, C: C, ans: [d, 2] } };
  };

  /* 1-15 平行四邊形面積與係數伸縮 */
  L1.paraArea = function (r) {
    var a = [r.nz(-4, 4), r.nz(-4, 4)], b = [r.nz(-4, 4), r.nz(-4, 4)];
    while (cross(a, b) === 0) b = [r.nz(-4, 4), r.nz(-4, 4)];
    var p = r.pick([1, 2, 3, -1]), q = r.pick([1, -1, 2, -2]), s = r.pick([1, -1, 2]), t = r.pick([1, 2, 3, -2]);
    while (p * t - q * s === 0) t = r.pick([1, 2, 3, -2, 4]);
    var u = add(sc(p, a), sc(q, b)), v = add(sc(s, a), sc(t, b));
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '。求 (1) ' + T(vec('a') + ',' + vec('b')) + ' 所張平行四邊形的面積　(2) ' + T(comb(p, vec('a'), true) + comb(q, vec('b'), false)) + ' 與 ' + T(comb(s, vec('a'), true) + comb(t, vec('b'), false)) + ' 所張平行四邊形的面積。',
             a: '(1) ' + T(String(Math.abs(cross(a, b)))) + '　(2) ' + T(String(Math.abs(cross(u, v)))),
             h: '面積 $=|a_1b_2-a_2b_1|$；(2) 直接算，或用伸縮率 $\\left|\\begin{smallmatrix}p&q\\\\s&t\\end{smallmatrix}\\right|$ 乘上 (1)。',
             p: { a: a, b: b, p: p, q: q, s: s, t: t, ans: [Math.abs(cross(a, b)), Math.abs(cross(u, v))] } };
  };

  /* 1-16 三邊長求內積 */
  L1.triDot = function (r) {
    var c = r.int(3, 9), b = r.int(3, 9), a = r.int(Math.abs(b - c) + 1, b + c - 1);  /* AB=c, AC=b, BC=a */
    var d = F(b * b + c * c - a * a, 2);
    var M = r() < 0.5;
    return { q: T('\\triangle ABC') + ' 中 ' + T('\\overline{AB}=' + c) + '、' + T('\\overline{BC}=' + a) + '、' + T('\\overline{CA}=' + b) + (M ? '，' + T('M') + ' 為 ' + T('\\overline{CA}') + ' 的中點，求 ' + T(ov('AB') + '\\cdot' + ov('AM')) : '，求 ' + T(ov('AB') + '\\cdot' + ov('AC'))) + '。',
             a: T(Fr.tex(M ? Fr.div(d, F(2)) : d)),
             h: '$\\overrightarrow{AB}\\cdot\\overrightarrow{AC}=\\dfrac{|AB|^2+|AC|^2-|BC|^2}{2}$（餘弦定理的變形）；$\\overrightarrow{AM}=\\frac12\\overrightarrow{AC}$。',
             p: { c: c, b: b, a: a, M: M, ans: fr2(M ? Fr.div(d, F(2)) : d) } };
  };

  /* 1-17 柯西：x²+y²=r² 上 px+qy 的最大值 */
  L1.cauchyCircle = function (r) {
    var p = r.nz(-5, 5), q = r.nz(-5, 5), R2 = r.pick([1, 4, 9, 16, 25, 2, 5, 10]);
    var M2 = (p * p + q * q) * R2;
    return { q: '設實數 ' + T('x,y') + ' 滿足 ' + T('x^{2}+y^{2}=' + R2) + '，求 ' + T(term(p, 'x', true) + term(q, 'y', false)) + ' 的最大值。',
             a: T(sqrtTex(M2)),
             h: '柯西：$(px+qy)^2\\le(p^2+q^2)(x^2+y^2)$；或看成 $(p,q)\\cdot(x,y)\\le|(p,q)|\\,|(x,y)|$。',
             p: { p: p, q: q, R2: R2, ans: M2 } };
  };

  /* 1-18 砝碼：aPA+bPB+cPC=0 ⇒ 面積比 */
  L1.weightArea = function (r) {
    var a = r.int(1, 5), b = r.int(1, 5), c = r.int(1, 5);
    return { q: T('P') + ' 在 ' + T('\\triangle ABC') + ' 內部且 ' + T(comb(a, ov('PA'), true) + comb(b, ov('PB'), false) + comb(c, ov('PC'), false) + '=\\vec0') + '，求 ' + T('\\triangle PBC:\\triangle PCA:\\triangle PAB') + '，以及 ' + T('\\dfrac{\\triangle PBC}{\\triangle ABC}') + '。',
             a: T(a / gcd(gcd(a, b), c) + ':' + b / gcd(gcd(a, b), c) + ':' + c / gcd(gcd(a, b), c)) + '，' + T(Fr.tex(F(a, a + b + c))),
             h: '把 $P$ 看成三個砝碼 $a,b,c$ 的平衡點：對面三角形的面積比 $=a:b:c$。',
             p: { a: a, b: b, c: c, ans: [a, b, c, fr2(F(a, a + b + c))] } };
  };

  /* 1-19 AP=xAB+yAC 的位置判讀 */
  L1.coefRegion = function (r) {
    var xs = [F(1, 3), F(1, 2), F(2, 3), F(1, 4), F(3, 4), F(-1, 2), F(5, 4), F(2, 5), F(3, 5)];
    var x = r.pick(xs), y = r.pick(xs);
    var sum = Fr.add(x, y), inside = x.n > 0 && y.n > 0 && sum.n < sum.d;
    var onBC = x.n > 0 && y.n > 0 && sum.n === sum.d;
    var region = inside ? '三角形內部' : (onBC ? '邊 $BC$ 上' : ((x.n > 0 && y.n > 0) ? '∠BAC 的張角內、但在邊 $BC$ 的外側' : '∠BAC 的張角外'));
    return { q: T('\\triangle ABC') + ' 中，' + T(ov('AP') + '=' + combF(x, ov('AB'), true) + combF(y, ov('AC'), false)) + '。問 ' + T('P') + ' 在三角形的哪裡？並求 ' + T('\\dfrac{\\triangle PBC}{\\triangle ABC}') + '（' + T('P') + ' 在內部時）。',
             a: region + (inside ? '，' + T('\\dfrac{\\triangle PBC}{\\triangle ABC}=' + Fr.tex(Fr.sub(F(1), sum))) : ''),
             h: '內部 ⟺ $x\\gt0$、$y\\gt0$ 且 $x+y\\lt1$；$\\triangle PBC:\\triangle PCA:\\triangle PAB=(1-x-y):x:y$。',
             p: { x: fr2(x), y: fr2(y), ans: { inside: inside, onBC: onBC, ratio: inside ? fr2(Fr.sub(F(1), sum)) : null } } };
  };

  /* 1-20 距離：|ta+b| 的最小值 */
  L1.minLen = function (r) {
    var a = r.pick([[1, 2], [2, 1], [3, 1], [1, 3], [2, -1], [1, -2], [3, 4], [4, 3]]), k = r.nz(-3, 3), m = r.nz(-4, 4), w = [-a[1], a[0]];
    var b = add(sc(k, a), sc(m, w));
    var min2 = m * m * n2(a);   /* 最小長度平方 = |m w|^2 */
    return { q: '設 ' + T('t') + ' 為實數，' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '，求 ' + T('|t' + vec('a') + '+' + vec('b') + '|') + ' 的最小值。',
             a: T(sqrtTex(min2)) + '（' + T('t=' + (-k)) + ' 時）',
             h: '平方後是 $t$ 的二次式，配方；或看成「$\\vec b$ 的終點到直線（方向 $\\vec a$）的距離」$=\\dfrac{|\\vec a\\times\\vec b|}{|\\vec a|}$。',
             p: { a: a, b: b, ans: { min2: min2, t: -k } } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 2-1 平行四邊形內兩線交點（分點 × 共線） */
  L2.paraIntersect = function (r) {
    /* ABCD 平行四邊形，E 在 DC 上 DE = e·DC，F 在 AB 上 AF = f·AB，BE ∩ CF = P；AP = x AB + y AD */
    var e = F(r.int(1, 3), r.int(2, 5)), f = F(r.int(1, 4), r.int(2, 5));
    if (e.n >= e.d) e = F(1, 3); if (f.n >= f.d) f = F(3, 5);
    /* E = D + e AB = (e, 1)，B = (1,0)，C = (1,1)，F = (f,0)（以 AB, AD 為基底） */
    /* BE: B + t(E-B) = (1 + t(e-1), t)；CF: C + s(F-C) = (1 + s(f-1), 1 - s) ⇒ t = 1-s；1 + (1-s)(e-1) = 1 + s(f-1) ⇒ (1-s)(e-1) = s(f-1) ⇒ s = (e-1)/(e-1+f-1) */
    var e1 = Fr.sub(e, F(1)), f1 = Fr.sub(f, F(1));
    var s = Fr.div(e1, Fr.add(e1, f1)), t = Fr.sub(F(1), s);
    var x = Fr.add(F(1), Fr.mul(t, e1)), y = t;
    /* EP:PB = t : (1-t)  （P = B + t(E−B) ⇒ BP = t·BE） */
    var BP = t, PE = Fr.sub(F(1), t);
    return { q: '平行四邊形 ' + T('ABCD') + ' 中，' + T(ov('DE') + '=' + Fr.tex(e) + ov('DC')) + '、' + T(ov('AF') + '=' + Fr.tex(f) + ov('AB')) + '，' + T('\\overline{BE}') + ' 與 ' + T('\\overline{CF}') + ' 交於 ' + T('P') + '。<br>(1) 求 ' + T('\\overline{BP}:\\overline{PE}') + '　(2) 若 ' + T(ov('AP') + '=x' + ov('AB') + '+y' + ov('AD')) + '，求 ' + T('(x,y)') + '。',
             a: '(1) ' + T(Fr.div(BP, PE).n + ':' + Fr.div(BP, PE).d) + '　(2) ' + T('(x,y)=\\left(' + Fr.tex(x) + ',\\ ' + Fr.tex(y) + '\\right)'),
             h: '以 $\\overrightarrow{AB},\\overrightarrow{AD}$ 為基底把 $E,F,B,C$ 都寫成係數；$P$ 同時在 $BE$、$CF$ 上，用「係數和為 1」設兩個參數再比對。',
             p: { e: fr2(e), f: fr2(f), ans: { BP: fr2(BP), PE: fr2(PE), x: fr2(x), y: fr2(y) } } };
  };

  /* 2-2 係數 ⟹ 三個小三角形面積 */
  L2.coefArea = function (r) {
    var d = r.pick([6, 8, 10, 12, 15, 20]), xn = r.int(1, d - 2), yn = r.int(1, d - 1 - xn);
    var x = F(xn, d), y = F(yn, d), z = F(d - xn - yn, d), S = d * r.int(2, 8);
    return { q: T('P') + ' 在 ' + T('\\triangle ABC') + ' 內且 ' + T(ov('AP') + '=' + combF(x, ov('AB'), true) + combF(y, ov('AC'), false)) + '，' + T('\\triangle ABC') + ' 的面積為 ' + T(String(S)) + '。求 ' + T('\\triangle PBC') + '、' + T('\\triangle PCA') + '、' + T('\\triangle PAB') + ' 的面積。',
             a: T(String(S * z.n / z.d)) + '、' + T(String(S * x.n / x.d)) + '、' + T(String(S * y.n / y.d)),
             h: '$\\triangle PBC:\\triangle PCA:\\triangle PAB=(1-x-y):x:y$——係數就是「到對邊的距離比」。',
             p: { x: fr2(x), y: fr2(y), S: S, ans: [S * z.n / z.d, S * x.n / x.d, S * y.n / y.d] } };
  };

  /* 2-3 過定點的直線截兩邊：1/x+1/y 恆等式與 x+y 最小 */
  L2.lineThroughPoint = function (r) {
    var m = r.int(1, 4), n = r.int(1, 4);  /* D 在 BC 上 BD:DC = m:n ⇒ AD = n/(m+n) AB + m/(m+n) AC */
    var p = F(n, m + n), q = F(m, m + n);   /* AD = p AB + q AC = (p/x) AE + (q/y) AF ⇒ p/x + q/y = 1 */
    /* x + y 最小：x+y = (x+y)(p/x+q/y) = p + q + p y/x + q x/y ≥ p+q+2√(pq) */
    var pq = Fr.mul(p, q), sq = simpSqrt(pq.n * pq.d);  /* √(pq) = √(pq.n·pq.d)/pq.d */
    var minTex = Fr.tex(Fr.add(p, q)) + '+' + (sq.r === 1 ? Fr.tex(F(2 * sq.c, pq.d)) : Fr.tex(F(2 * sq.c, pq.d)) + '\\sqrt{' + sq.r + '}');
    if (sq.r === 1) minTex = Fr.tex(Fr.add(Fr.add(p, q), F(2 * sq.c, pq.d)));
    return { q: T('\\triangle ABC') + ' 中，' + T('D') + ' 在 ' + T('\\overline{BC}') + ' 上且 ' + T('\\overline{BD}:\\overline{DC}=' + m + ':' + n) + '。過 ' + T('D') + ' 的直線交直線 ' + T('AB') + '、' + T('AC') + ' 於 ' + T('E,F') + '，' + T(ov('AE') + '=x' + ov('AB')) + '、' + T(ov('AF') + '=y' + ov('AC')) + '（' + T('x,y\\gt0') + '）。<br>(1) 求 ' + T('\\dfrac{p}{x}+\\dfrac{q}{y}=1') + ' 中的 ' + T('(p,q)') + '　(2) 求 ' + T('x+y') + ' 的最小值。',
             a: '(1) ' + T('(p,q)=\\left(' + Fr.tex(p) + ',\\ ' + Fr.tex(q) + '\\right)') + '　(2) ' + T(minTex),
             h: '$\\overrightarrow{AD}=\\frac{n}{m+n}\\overrightarrow{AB}+\\frac{m}{m+n}\\overrightarrow{AC}=\\frac{p}{x}\\overrightarrow{AE}+\\frac{q}{y}\\overrightarrow{AF}$，$E,D,F$ 共線 ⟹ 係數和 $1$；(2) 用 $(x+y)\\left(\\frac px+\\frac qy\\right)$ 配算幾。',
             p: { m: m, n: n, ans: { p: fr2(p), q: fr2(q), min: [Fr.add(p, q).n, Fr.add(p, q).d, 2 * sq.c, pq.d, sq.r] } } };
  };

  /* 2-4 向量區域的面積 */
  L2.regionArea = function (r) {
    var u = [r.nz(-3, 3), r.nz(-3, 3)], v = [r.nz(-3, 3), r.nz(-3, 3)];
    while (cross(u, v) === 0) v = [r.nz(-3, 3), r.nz(-3, 3)];
    var x1 = r.int(-2, 1), x2 = x1 + r.int(1, 3), y1 = r.int(-2, 1), y2 = y1 + r.int(1, 3);
    var A = (x2 - x1) * (y2 - y1) * Math.abs(cross(u, v));
    return { q: '設 ' + T(vec('u') + '=' + vt(u)) + '、' + T(vec('v') + '=' + vt(v)) + '。若 ' + T(ov('OP') + '=x' + vec('u') + '+y' + vec('v')) + '，其中 ' + T(x1 + '\\le x\\le ' + x2) + '、' + T(y1 + '\\le y\\le ' + y2) + '，求 ' + T('P') + ' 所形成區域的面積。',
             a: T(String(A)),
             h: '區域是平行四邊形：面積 $=(x$ 的長度$)\\times(y$ 的長度$)\\times|\\vec u\\times\\vec v|$，其中 $|\\vec u\\times\\vec v|=|u_1v_2-u_2v_1|$。',
             p: { u: u, v: v, x1: x1, x2: x2, y1: y1, y2: y2, ans: A } };
  };

  /* 2-5 |u|=k|v|=|au+bv| ⟹ cosθ */
  L2.cosFromLen = function (r) {
    var k = r.int(2, 3), a = r.pick([1, 2, 3]), b = r.pick([1, -1, 2, -2, 3, -3]);
    /* |v|=1, |u|=k: |au+bv|^2 = a²k² + b² + 2ab u·v = k² ⇒ u·v = (k²-a²k²-b²)/(2ab); cos = u·v/k */
    var uv = F(k * k - a * a * k * k - b * b, 2 * a * b), cos = Fr.div(uv, F(k));
    if (Math.abs(Fr.toNum(cos)) > 1) { a = 1; b = 1; uv = F(k * k - k * k - 1, 2); cos = Fr.div(uv, F(k)); }
    return { q: '設 ' + T(vec('u') + ',' + vec('v')) + ' 為非零向量，且 ' + T('|' + vec('u') + '|=' + k + '|' + vec('v') + '|=\\left|' + comb(a, vec('u'), true) + comb(b, vec('v'), false) + '\\right|') + '，' + T('\\theta') + ' 為兩向量的夾角，求 ' + T('\\cos\\theta') + '。',
             a: T('\\cos\\theta=' + Fr.tex(cos)),
             h: '設 $|\\vec v|=t$、$|\\vec u|=' + k + 't$，把 $|' + comb(a, '\\vec u', true) + comb(b, '\\vec v', false) + '|^2$ 展開，$t^2$ 全部約掉，解出 $\\vec u\\cdot\\vec v$。',
             p: { k: k, a: a, b: b, ans: fr2(cos) } };
  };

  /* 2-6 由 |au−bv| 求正射影長 */
  L2.projLen = function (r) {
    var lu = r.int(1, 4), lv = r.int(1, 4), a = r.pick([1, 2, 3]), b = r.pick([1, 2, 3]), deg = r.pick([60, 120, 90]);
    var uv = F(lu * lv * (deg === 60 ? 1 : deg === 120 ? -1 : 0), deg === 90 ? 1 : 2);
    var L2v = Fr.add(F(a * a * lu * lu + b * b * lv * lv), Fr.mul(F(-2 * a * b), uv));   /* |au-bv|^2 */
    var projl = Fr.div(uv, F(lv));  /* u 在 v 上的正射影長（可為負，取絕對值） */
    return { q: '設非零向量 ' + T(vec('u') + ',' + vec('v')) + ' 滿足 ' + T('|' + vec('u') + '|=' + lu) + '、' + T('|' + vec('v') + '|=' + lv) + '、' + T('\\left|' + comb(a, vec('u'), true) + comb(-b, vec('v'), false) + '\\right|=' + rootTexF(L2v)) + '，求 ' + T(vec('u')) + ' 在 ' + T(vec('v')) + ' 上的正射影長。',
             a: T(Fr.tex(F(Math.abs(projl.n), projl.d))),
             h: '先把已知長度平方展開解出 $\\vec u\\cdot\\vec v$；正射影長 $=\\dfrac{|\\vec u\\cdot\\vec v|}{|\\vec v|}$（「長度」只除一次）。',
             p: { lu: lu, lv: lv, a: a, b: b, L2: fr2(L2v), ans: fr2(F(Math.abs(projl.n), projl.d)) } };
  };

  /* 2-7 柯西：ax²+by²=c 上 px+qy 的最大值與達成點 */
  L2.cauchyEllipse = function (r) {
    var A = r.pick([1, 4, 9]), B = r.pick([1, 4, 9, 16]); while (A === B) B = r.pick([4, 9, 16, 25]);
    var sa = Math.round(Math.sqrt(A)), sb = Math.round(Math.sqrt(B));
    /* 取 x = sb·m/g?... 直接設達成點 (x0,y0) 使 A x0² + B y0² = C，且 (p,q) ∥ (A x0, B y0) */
    var x0 = r.nz(-3, 3), y0 = r.nz(-3, 3), C = A * x0 * x0 + B * y0 * y0;
    var g = gcd(A * x0, B * y0), p = A * x0 / g, q = B * y0 / g, M = p * x0 + q * y0;
    return { q: '實數 ' + T('x,y') + ' 滿足 ' + T((A === 1 ? '' : A) + 'x^{2}+' + (B === 1 ? '' : B) + 'y^{2}=' + C) + '。求 ' + T(term(p, 'x', true) + term(q, 'y', false)) + ' 的最大值，以及達到最大值時的 ' + T('(x,y)') + '。',
             a: '最大值 ' + T(String(M)) + '，' + T('(x,y)=' + pt(x0, y0)),
             h: '柯西：$(px+qy)^2\\le\\left(' + (A === 1 ? 'p^2' : '\\dfrac{p^2}{' + A + '}') + '+' + (B === 1 ? 'q^2' : '\\dfrac{q^2}{' + B + '}') + '\\right)(' + (A === 1 ? '' : A) + 'x^2+' + (B === 1 ? '' : B) + 'y^2)$，等號在 $(' + (A === 1 ? '' : A) + 'x,' + (B === 1 ? '' : B) + 'y)\\parallel(p,q)$。',
             p: { A: A, B: B, C: C, p: p, q: q, ans: { M: M, x: x0, y: y0 } } };
  };

  /* 2-8 行列式伸縮率反推 */
  L2.detScale = function (r) {
    var p = r.pick([1, 2, 3, -1, -2]), q = r.pick([1, -1, 2, 3]), s = r.pick([1, -1, 2, -2]), t = r.pick([1, 2, 3, -1, -3]);
    while (p * t - q * s === 0) t = r.pick([1, 2, 3, -1, -3, 4]);
    var k = Math.abs(p * t - q * s), S0 = r.int(2, 9), S1 = k * S0, rev = r() < 0.5;
    var comboTex = T(comb(p, vec('a'), true) + comb(q, vec('b'), false)) + ' 與 ' + T(comb(s, vec('a'), true) + comb(t, vec('b'), false));
    return rev ? { q: '已知 ' + comboTex + ' 所張平行四邊形的面積為 ' + T(String(S1)) + '，求 ' + T(vec('a') + ',' + vec('b')) + ' 所張平行四邊形的面積。',
                   a: T(String(S0)), h: '係數行列式 $\\left|\\begin{smallmatrix}' + p + '&' + q + '\\\\' + s + '&' + t + '\\end{smallmatrix}\\right|$ 的絕對值 $' + k + '$ 就是面積的伸縮率。',
                   p: { p: p, q: q, s: s, t: t, given: S1, rev: true, ans: S0 } }
               : { q: '已知 ' + T(vec('a') + ',' + vec('b')) + ' 所張平行四邊形的面積為 ' + T(String(S0)) + '，求 ' + comboTex + ' 所張平行四邊形的面積。',
                   a: T(String(S1)), h: '$\\det(p\\vec a+q\\vec b,\\ s\\vec a+t\\vec b)=(pt-qs)\\det(\\vec a,\\vec b)$，面積乘 $|pt-qs|$。',
                   p: { p: p, q: q, s: s, t: t, given: S0, rev: false, ans: S1 } };
  };

  /* 2-9 圓上動點的內積最大值 */
  L2.circleDot = function (r) {
    var h = r.int(-4, 4), k = r.int(-4, 4), R = r.int(1, 4), q = r.pick([[3, 4], [4, -3], [-3, 4], [5, 12], [-5, 12], [6, 8], [1, 0], [0, -1], [8, -6]]);
    var M = q[0] * h + q[1] * k + R * Math.round(Math.sqrt(n2(q)));
    return { q: '設 ' + T('P(a,b)') + ' 為圓 ' + T((h ? '(x' + (h > 0 ? '-' + h : '+' + (-h)) + ')^{2}' : 'x^{2}') + '+' + (k ? '(y' + (k > 0 ? '-' + k : '+' + (-k)) + ')^{2}' : 'y^{2}') + '=' + R * R) + ' 上的點，' + T('O') + ' 為原點、' + T('Q' + vt(q)) + '，求 ' + T(ov('OP') + '\\cdot' + ov('OQ')) + ' 的最大值。',
             a: T(String(M)),
             h: '$\\overrightarrow{OP}\\cdot\\overrightarrow{OQ}=\\overrightarrow{OM}\\cdot\\overrightarrow{OQ}+\\overrightarrow{MP}\\cdot\\overrightarrow{OQ}$（$M$ 為圓心），後者最大 $=R\\,|\\overrightarrow{OQ}|$（$\\overrightarrow{MP}$ 與 $\\overrightarrow{OQ}$ 同向時）。',
             p: { h: h, k: k, R: R, q: q, ans: M } };
  };

  /* 2-10 內積在拋物線上的最小值 */
  L2.dotParabola = function (r) {
    /* A, B 固定，C=(x, x²/k)；AB·AC = d1(x-a1) + d2(x²/k - a2)，二次式 */
    var kden = r.pick([1, 2, 4]), d = [r.nz(-4, 4), r.pick([1, 2, 4, 8])], A = [r.int(-3, 3), r.int(-3, 3)], B = add(A, d);
    /* f(x) = d1 (x - A0) + d2 (x²/kden - A1) ⇒ 頂點 x = -d1 kden/(2 d2) */
    var xv = F(-d[0] * kden, 2 * d[1]);
    var fmin = Fr.add(Fr.mul(F(d[0]), Fr.sub(xv, F(A[0]))), Fr.mul(F(d[1]), Fr.sub(Fr.div(Fr.mul(xv, xv), F(kden)), F(A[1]))));
    return { q: T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，' + T('C') + ' 在拋物線 ' + T('y=' + (kden === 1 ? 'x^{2}' : '\\dfrac{x^{2}}{' + kden + '}')) + ' 上變動。求 ' + T(ov('AB') + '\\cdot' + ov('AC')) + ' 的最小值，以及此時 ' + T('C') + ' 的 ' + T('x') + ' 坐標。',
             a: '最小值 ' + T(Fr.tex(fmin)) + '，' + T('x=' + Fr.tex(xv)),
             h: '設 $C\\left(x,\\dfrac{x^2}{' + kden + '}\\right)$，內積是 $x$ 的二次式，配方。',
             p: { A: A, B: B, kden: kden, ans: { min: fr2(fmin), x: fr2(xv) } } };
  };

  /* 2-11 外心→垂心：OH = OA+OB+OC */
  L2.orthocenter = function (r) {
    var R2 = r.pick([25, 25, 50, 65, 85, 100, 130]);
    var pts = [];
    for (var x = -12; x <= 12; x++) for (var y = -12; y <= 12; y++) if (x * x + y * y === R2) pts.push([x, y]);
    var P = r.shuffle(pts).slice(0, 3);
    while (Math.abs(cross(sub(P[1], P[0]), sub(P[2], P[0]))) === 0) P = r.shuffle(pts).slice(0, 3);
    var H = add(add(P[0], P[1]), P[2]), G = [F(H[0], 3), F(H[1], 3)];
    return { q: T('O(0,0)') + ' 為 ' + T('\\triangle ABC') + ' 的外心，' + T('A' + vt(P[0])) + '、' + T('B' + vt(P[1])) + '、' + T('C' + vt(P[2])) + '。求 (1) 重心 ' + T('G') + '　(2) 垂心 ' + T('H') + '。',
             a: '(1) ' + T('G' + vtF(G)) + '　(2) ' + T('H' + vt(H)),
             h: '外心在原點時 $\\overrightarrow{OH}=\\overrightarrow{OA}+\\overrightarrow{OB}+\\overrightarrow{OC}$（可用 $\\overrightarrow{AH}\\cdot\\overrightarrow{BC}=0$ 驗證），且 $\\overrightarrow{OH}=3\\overrightarrow{OG}$。',
             p: { A: P[0], B: P[1], C: P[2], ans: { G: [fr2(G[0]), fr2(G[1])], H: H } } };
  };

  /* 2-12 三向量和的長度範圍 */
  L2.sumRange = function (r) {
    var L = r.shuffle([r.int(1, 6), r.int(1, 6), r.int(1, 8)]);
    var mx = L.reduce(function (s, v) { return s + v; }, 0), big = Math.max.apply(null, L), rest = mx - big;
    var mn = big <= rest ? 0 : big - rest;
    return { q: '平面向量 ' + T(vec('a') + ',' + vec('b') + ',' + vec('c')) + ' 滿足 ' + T('|' + vec('a') + '|=' + L[0]) + '、' + T('|' + vec('b') + '|=' + L[1]) + '、' + T('|' + vec('c') + '|=' + L[2]) + '。設 ' + T('s=|' + vec('a') + '+' + vec('b') + '+' + vec('c') + '|') + '，求 ' + T('s') + ' 的範圍。',
             a: T(mn + '\\le s\\le ' + mx),
             h: '上界：三支同向。下界：最長的那支能否被另外兩支「抵銷」——三個長度圍得成三角形（含退化）就能到 $0$，否則下界是「最長減其餘兩支之和」。',
             p: { L: L, ans: [mn, mx] } };
  };

  /* 2-13 平行／垂直／最短三連問 */
  L2.tripleT = function (r) {
    var b = r.pick([[1, -1], [1, 1], [1, 2], [2, 1], [2, -1], [1, -2]]), c = r.pick([[5, -3], [3, 4], [4, -1], [2, 5], [-3, 5], [1, -4]]);
    while (cross(b, c) === 0) c = [r.nz(-5, 5), r.nz(-5, 5)];
    var t1 = r.nz(-6, 6), t2 = r.nz(-6, 6), lam = r.nz(-3, 3), mu = r.nz(-3, 3);
    /* a + t1 b ∥ c： a = lam c - t1 b；也要 a + t2 b ⊥ c：(lam c - t1 b + t2 b)·c = 0 ⇒ lam|c|² + (t2-t1)(b·c) = 0 ⇒ 不一定整數。改為只保證 t1，t2 由公式算（可能分數） */
    var a = sub(sc(lam, c), sc(t1, b));
    var t2F = Fr.div(F(-dot(a, c)), F(dot(b, c) || 1)); if (dot(b, c) === 0) t2F = null;
    var tminF = Fr.div(F(-dot(a, b)), F(n2(b)));
    var w = add(a, [Fr.toNum(tminF) * b[0], Fr.toNum(tminF) * b[1]]);
    var min2 = Fr.sub(F(n2(a)), Fr.div(F(dot(a, b) * dot(a, b)), F(n2(b))));
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '、' + T(vec('c') + '=' + vt(c)) + '。求 (1) ' + T('(' + vec('a') + '+t' + vec('b') + ')\\parallel' + vec('c')) + ' 的 ' + T('t') + (t2F ? '　(2) ' + T('(' + vec('a') + '+t' + vec('b') + ')\\perp' + vec('c')) + ' 的 ' + T('t') : '') + '　(' + (t2F ? 3 : 2) + ') ' + T('|' + vec('a') + '+t' + vec('b') + '|') + ' 最小時的 ' + T('t') + ' 與最小值。',
             a: '(1) ' + T('t=' + t1) + (t2F ? '　(2) ' + T('t=' + Fr.tex(t2F)) : '') + '　(' + (t2F ? 3 : 2) + ') ' + T('t=' + Fr.tex(tminF)) + '，最小值 ' + T(rootTexF(min2)),
             h: '平行：交叉相乘相等；垂直：內積為 $0$；最短：對 $t$ 配方，最小值也等於 $\\vec a$ 到直線（方向 $\\vec b$）的距離。',
             p: { a: a, b: b, c: c, ans: { t1: t1, t2: t2F ? fr2(t2F) : null, tmin: fr2(tminF), min2: fr2(min2) } } };
  };

  /* 2-14 角平分線的向量分解 */
  L2.bisector = function (r) {
    var c = r.int(3, 9), b = r.int(3, 9), a = r.int(Math.abs(b - c) + 1, b + c - 1);   /* AB=c, AC=b, BC=a */
    var x = F(b, b + c), y = F(c, b + c);   /* AD = b/(b+c) AB + c/(b+c) AC */
    return { q: T('\\triangle ABC') + ' 中 ' + T('\\overline{AB}=' + c) + '、' + T('\\overline{AC}=' + b) + '、' + T('\\overline{BC}=' + a) + '，' + T('\\angle BAC') + ' 的平分線交 ' + T('\\overline{BC}') + ' 於 ' + T('D') + '。若 ' + T(ov('AD') + '=x' + ov('AB') + '+y' + ov('AC')) + '，求 ' + T('(x,y)') + ' 與 ' + T('\\overline{BD}') + '。',
             a: T('(x,y)=\\left(' + Fr.tex(x) + ',\\ ' + Fr.tex(y) + '\\right)') + '，' + T('\\overline{BD}=' + Fr.tex(F(a * c, b + c))),
             h: '角平分線定理：$\\overline{BD}:\\overline{DC}=\\overline{AB}:\\overline{AC}=' + c + ':' + b + '$，再用分點公式（交叉配）。',
             p: { c: c, b: b, a: a, ans: { x: fr2(x), y: fr2(y), BD: fr2(F(a * c, b + c)) } } };
  };

  /* 2-15 折線行走：轉角 → 坐標 → 距離 */
  L2.walk = function (r) {
    var d1 = r.int(2, 9), d2 = r.int(2, 9), turn = r.pick([60, 120, 90]), d3 = r.pick([2, 3, 4]), turn2 = r.pick([90, 60, 120]);
    /* 方向角依序 0, turn, turn+turn2；坐標為 (Σ d cos, Σ d sin)，用精確：cos60=1/2, sin60=√3/2 */
    var ang1 = turn, ang2 = turn + turn2;
    function cs(a) { a = ((a % 360) + 360) % 360; var tab = { 0: [1, 0, 0, 0], 60: [1, 0, 0, 1], 90: [0, 0, 1, 0], 120: [-1, 0, 0, 1], 150: [0, -1, 1, 0], 180: [-1, 0, 0, 0], 210: [0, -1, -1, 0], 240: [-1, 0, 0, -1] }; return tab[a]; }
    /* cs 回傳 [cos 的有理分子(以 /2 計時), cos 的 √3 分子, sin 的有理分子, sin 的 √3 分子]，全部以 1/2 為單位 */
    function comp(deg) { var t = cs(deg); var half = (deg % 90 !== 0); return { cq: half ? F(t[0], 2) : F(t[0]), cr: half ? F(t[1], 2) : F(t[1]), sq: half ? F(t[2], 2) : F(t[2]), sr: half ? F(t[3], 2) : F(t[3]) }; }
    var c0 = comp(0), c1 = comp(ang1), c2 = comp(ang2);
    /* x = d1 c0.c + d2 c1.c + d3 c2.c  （有理部分 + √3 部分）*/
    var xq = Fr.add(Fr.add(Fr.mul(F(d1), c0.cq), Fr.mul(F(d2), c1.cq)), Fr.mul(F(d3), c2.cq)), xr = Fr.add(Fr.add(Fr.mul(F(d1), c0.cr), Fr.mul(F(d2), c1.cr)), Fr.mul(F(d3), c2.cr));
    var yq = Fr.add(Fr.add(Fr.mul(F(d1), c0.sq), Fr.mul(F(d2), c1.sq)), Fr.mul(F(d3), c2.sq)), yr = Fr.add(Fr.add(Fr.mul(F(d1), c0.sr), Fr.mul(F(d2), c1.sr)), Fr.mul(F(d3), c2.sr));
    /* |OC|² = (xq + xr√3)² + (yq + yr√3)² = (xq²+3xr²+yq²+3yr²) + 2√3 (xq xr + yq yr) */
    var Q = Fr.add(Fr.add(Fr.mul(xq, xq), Fr.mul(F(3), Fr.mul(xr, xr))), Fr.add(Fr.mul(yq, yq), Fr.mul(F(3), Fr.mul(yr, yr))));
    var Rt = Fr.mul(F(2), Fr.add(Fr.mul(xq, xr), Fr.mul(yq, yr)));
    var len2Tex = Fr.tex(Q) + (Rt.n === 0 ? '' : (Rt.n > 0 ? '+' : '-') + (Fr.eq(F(Math.abs(Rt.n), Rt.d), F(1)) ? '' : Fr.tex(F(Math.abs(Rt.n), Rt.d))) + '\\sqrt3');
    var ansTex = Rt.n === 0 ? rootTexF(Q) : '\\sqrt{' + len2Tex + '}';
    if (Rt.n !== 0 && Q.d === 1 && Rt.d === 1) {   /* Q+R√3=(p+q√3)² ⟺ p²、3q² 是 z²−Qz+3R²/4=0 的兩根 */
      var disc = Q.n * Q.n - 3 * Rt.n * Rt.n, sd = Math.round(Math.sqrt(Math.max(disc, 0)));
      if (disc >= 0 && sd * sd === disc && (Q.n + sd) % 2 === 0) {
        [(Q.n + sd) / 2, (Q.n - sd) / 2].forEach(function (p2) {
          var pp = Math.round(Math.sqrt(p2)), q2 = (Q.n - p2) / 3, qq = Math.round(Math.sqrt(Math.max(q2, 0)));
          if (p2 > 0 && pp * pp === p2 && q2 > 0 && qq * qq === q2 && 2 * pp * qq === Math.abs(Rt.n)) {
            var rt = (qq === 1 ? '' : qq) + '\\sqrt3';
            ansTex = Rt.n > 0 ? pp + '+' + rt : (p2 > 3 * q2 ? pp + '-' + rt : rt + '-' + pp);
          }
        });
      }
    }
    return { q: '小綠從 ' + T('O') + ' 出發直行 ' + T(String(d1)) + ' 公尺到 ' + T('A') + '，左轉 ' + T(turn + '^\\circ') + ' 直行 ' + T(String(d2)) + ' 公尺到 ' + T('B') + '，再左轉 ' + T(turn2 + '^\\circ') + ' 直行 ' + T(String(d3)) + ' 公尺到 ' + T('C') + '。求 ' + T('\\overline{OC}') + '。',
             a: T(ansTex) + ' 公尺',
             h: '$\\overrightarrow{OC}=\\overrightarrow{OA}+\\overrightarrow{AB}+\\overrightarrow{BC}$；設出發方向為 $x$ 軸正向，三段的方向角依序是 $0^\\circ$、$' + ang1 + '^\\circ$、$' + ang2 + '^\\circ$，各自寫成 $(d\\cos\\theta,d\\sin\\theta)$ 相加。',
             p: { d1: d1, d2: d2, d3: d3, turn: turn, turn2: turn2, ans: { Q: fr2(Q), R: fr2(Rt) } } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['vecOps', '§1 坐標運算與長度'], ['chain', '§1 首尾相接化簡'], ['divPoint', '§1 分點坐標'], ['centroid', '§1 重心與面積'],
      ['parallelCond', '§2 平行條件'], ['collinear', '§2 三點共線'], ['linComb', '§2 線性組合解係數'], ['segCoef', '§2 線段上的點：係數判準'], ['coefRegion', '§2 係數與位置'], ['weightArea', '§2 砝碼：面積比'],
      ['dotCoord', '§3 坐標內積與夾角'], ['dotLenAngle', '§3 長度夾角求內積'], ['perpCond', '§3 垂直條件'], ['projVec', '§3 正射影'], ['angleFromDot', '§3 由內積求夾角'],
      ['areaDet', '§3 三角形面積'], ['paraArea', '§3 平行四邊形面積'], ['triDot', '§3 三邊長求內積'], ['cauchyCircle', '§3 柯西不等式'], ['minLen', '§3 |ta+b| 的最小值']
    ],
    L2: [
      ['paraIntersect', '§2 平行四邊形內的交點'], ['coefArea', '§2 係數與三個小三角形'], ['lineThroughPoint', '§2 過定點直線的截距恆等式'], ['regionArea', '§2 向量區域的面積'],
      ['cosFromLen', '§3 由長度關係求 cosθ'], ['projLen', '§3 由長度求正射影長'], ['cauchyEllipse', '§3 柯西：橢圓型'], ['detScale', '§3 行列式伸縮率'], ['circleDot', '§3 圓上動點的內積'],
      ['dotParabola', '§3 拋物線上的內積最小'], ['orthocenter', '§3 外心→重心與垂心'], ['sumRange', '§3 三向量和的範圍'], ['tripleT', '§3 平行／垂直／最短三連問'], ['bisector', '§2 角平分線分解'], ['walk', '§1 折線行走']
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
