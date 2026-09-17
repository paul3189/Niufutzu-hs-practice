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

  /* ────────── 提示專用：把本題的數字代進式子 ────────── */
  function hpz(n) { return n < 0 ? '(' + n + ')' : String(n); }                  /* 負數代入時加括號 */
  function hdot(u, v) { return hpz(u[0]) + '\\times ' + hpz(v[0]) + '+' + hpz(u[1]) + '\\times ' + hpz(v[1]); }
  function hsq(v) { return '\\sqrt{' + (v[0] * v[0]) + '+' + (v[1] * v[1]) + '}'; }   /* |(3,-4)| 的代入式 */
  function hsum(a) { var s = String(a[0]); for (var i = 1; i < a.length; i++) s += '+' + hpz(a[i]); return s; }
  function hlin(c, k) { return String(c) + term(k, 't', false); }                 /* 3-2t */
  function antipodal(u, v) { return u[0] === -v[0] && u[1] === -v[1]; }           /* 圓上互為對徑點 ⟹ 直角三角形 */
  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* 1-1 坐標運算 */
  L1.vecOps = function (r) {
    var a = [r.nz(-6, 6), r.nz(-6, 6)], b = [r.nz(-6, 6), r.nz(-6, 6)], k1 = r.pick([2, 3, -2]), k2 = r.pick([1, -1, 2, -3]);
    var ans = add(sc(k1, a), sc(k2, b));
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '，求 ' + T(comb(k1, vec('a'), true) + comb(k2, vec('b'), false)) + ' 與它的長度。',
             a: T(vt(ans)) + '，長度 ' + T(sqrtTex(n2(ans))),
             h: '先把係數乘進分量：' + T(comb(k1, vec('a'), true) + '=\\left(' + k1 + '\\times ' + hpz(a[0]) + ',\\ ' + k1 + '\\times ' + hpz(a[1]) + '\\right)') + '，' + T(comb(k2, vec('b'), true)) + ' 同樣做，再把兩組對應分量相加；長度 $=\\sqrt{x^{2}+y^{2}}$，根號要化到最簡。',
             p: { a: a, b: b, k1: k1, k2: k2, ans: ans, len2: n2(ans) } };
  };

  /* 1-2 首尾相接化簡 */
  L1.chain = function (r) {
    var L = r.shuffle(['A', 'B', 'C', 'D', 'E']);
    /* 目標 AB+BC+CD-ED = AE？ 隨機產生一串合法首尾相接式 */
    var terms = [], cur = L[0], flips = [];
    for (var i = 1; i < 5; i++) {
      var nxt = L[i], flip = r() < 0.4;
      if (flip) flips.push(nxt + cur);
      terms.push(flip ? '-' + ov(nxt + cur) : '+' + ov(cur + nxt)); cur = nxt;
    }
    var expr = terms.join('').replace(/^\+/, '');
    return { q: '化簡 ' + T(expr) + '。',
             a: T(ov(L[0] + L[4])),
             h: '「減一個向量」＝加上它的反向量：$-' + ov('XY') + '=' + ov('YX') + '$。' +
                (flips.length ? '本題有 ' + T(String(flips.length)) + ' 項要翻，例如 ' + T('-' + ov(flips[0]) + '=' + ov(flips[0].charAt(1) + flips[0].charAt(0))) + '；' : '本題四項都是正號，不必翻；') +
                '翻完後從 ' + T(L[0]) + ' 出發首尾相接，中間的字母會一路消掉。',
             p: { start: L[0], end: L[4], expr: expr, ans: L[0] + L[4] } };
  };

  /* 1-3 分點坐標（內分／外分） */
  L1.divPoint = function (r) {
    var A = [r.int(-6, 6), r.int(-6, 6)], B = [r.int(-6, 6), r.int(-6, 6)];
    while (A[0] === B[0] && A[1] === B[1]) B = [r.int(-6, 6), r.int(-6, 6)];
    var m = r.int(1, 5), n = r.int(1, 5);
    while (m === n || gcd(m, n) !== 1) { m = r.int(1, 5); n = r.int(1, 5); }   /* 題幹的比一律最簡 */
    var ext = r() < 0.4, d = n - m;
    var P = ext ? [F(n * A[0] - m * B[0], n - m), F(n * A[1] - m * B[1], n - m)] : [F(n * A[0] + m * B[0], m + n), F(n * A[1] + m * B[1], m + n)];
    var frac = function (top, bot) { return bot === 1 ? top : '\\dfrac{' + top + '}{' + bot + '}'; };   /* 分母為 1 不寫分數 */
    var fx = ext ? (d > 0 ? frac(comb(n, 'A', true) + comb(-m, 'B', false), d) : frac(comb(m, 'B', true) + comb(-n, 'A', false), -d))
                 : frac(comb(n, 'A', true) + comb(m, 'B', false), m + n);
    return { q: '已知 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，點 ' + T('P') + (ext ? ' 在直線 $AB$ 上但不在線段 $AB$ 上' : ' 在線段 $AB$ 上') + '，且 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '，求 ' + T('P') + ' 的坐標。',
             a: T('P=' + vtF(P)),
             h: (ext ? '外分：本題 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '，套 ' + T('P=' + fx) + '（分母是「兩個權重相減」）；' : '內分：本題 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '，套 ' + T('P=' + fx) + '——離 $A$ 近的權重給 $A$，也就是「交叉配」；') + '把 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + ' 的坐標分量各自代進去算。',
             p: { A: A, B: B, m: m, n: n, ext: ext, ans: [fr2(P[0]), fr2(P[1])] } };
  };

  /* 1-4 重心 */
  L1.centroid = function (r) {
    var A = [r.int(-5, 5), r.int(-5, 5)], B = [r.int(-5, 5), r.int(-5, 5)], G = [r.int(-3, 3), r.int(-3, 3)], C;
    while (true) { C = [3 * G[0] - A[0] - B[0], 3 * G[1] - A[1] - B[1]]; if (cross(sub(B, A), sub(C, A)) !== 0) break; B = [r.int(-5, 5), r.int(-5, 5)]; G = [r.int(-3, 3), r.int(-3, 3)]; }
    return { q: T('\\triangle ABC') + ' 的頂點 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，重心為 ' + T('G' + vt(G)) + '。求 (1) 頂點 ' + T('C') + '　(2) ' + T('\\triangle ABC') + ' 的面積。',
             a: '(1) ' + T('C' + vt(C)) + '　(2) ' + T(Fr.tex(F(Math.abs(cross(sub(B, A), sub(C, A))), 2))),
             h: '重心 $=$ 三頂點的平均 ⟹ $C=3G-A-B$，本題是 ' + T('C=3' + vt(G) + '-' + vt(A) + '-' + vt(B)) + '（兩個分量各自算）；面積 $=\\dfrac12\\left|\\det\\left(' + ov('AB') + ',' + ov('AC') + '\\right)\\right|=\\dfrac12|a_1b_2-a_2b_1|$，先把兩個邊向量算出來。',
             p: { A: A, B: B, G: G, ans: { C: C, area2: Math.abs(cross(sub(B, A), sub(C, A))) } } };
  };

  /* 1-5 平行條件 */
  L1.parallelCond = function (r) {
    var b = [r.nz(-4, 4), r.nz(-4, 4)], k = r.pick([2, -2, 3, -3, 1.5, -0.5]);
    var a = [k * b[0], k * b[1]]; if (a[0] % 1 || a[1] % 1) { k = 2; a = [2 * b[0], 2 * b[1]]; }
    var which = r.pick([0, 1]); var ans = a[which];
    var eq = which === 0 ? term(b[1], 'x', true) + term(-a[1] * b[0], '', false)
                         : term(a[0] * b[1], '', true) + term(-b[0], 'x', false);
    return { q: '設 ' + T(vec('a') + '=' + (which === 0 ? '(x,' + a[1] + ')' : '(' + a[0] + ',x)')) + '、' + T(vec('b') + '=' + vt(b)) + '，若 ' + T(vec('a') + '\\parallel' + vec('b')) + '，求 ' + T('x') + '。',
             a: T('x=' + ans),
             h: '平行 ⟺ 交叉相乘相等（行列式為 $0$）：$a_1b_2-a_2b_1=0$。把本題的 ' + T(vec('b') + '=' + vt(b)) + ' 代進去得 ' + T(eq + '=0') + '，解這個一次方程式。',
             p: { b: b, which: which, known: a[1 - which], ans: ans } };
  };

  /* 1-6 三點共線 */
  L1.collinear = function (r) {
    var A = [r.int(-4, 4), r.int(-4, 4)], d = [r.nz(-3, 3), r.nz(-3, 3)], s = r.pick([2, 3, -1, -2]), t = r.pick([1, -1, 4, -3]);
    while (s === t) t = r.pick([1, -1, 4, -3]);
    var B = add(A, sc(s, d)), C = add(A, sc(t, d)), which = r.pick([0, 1]);
    var Cs = which === 0 ? '(x,' + C[1] + ')' : '(' + C[0] + ',x)';
    var ux = function (v) { return 'x' + (v > 0 ? '-' + v : (v < 0 ? '+' + (-v) : '')); };
    var acx = which === 0 ? ux(A[0]) : String(C[0] - A[0]), acy = which === 1 ? ux(A[1]) : String(C[1] - A[1]);
    return { q: '已知 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + Cs) + ' 三點共線，求 ' + T('x') + '。',
             a: T('x=' + C[which]),
             h: '$' + ov('AB') + '\\parallel' + ov('AC') + '$ ⟹ 交叉相乘相等。本題 ' + T(ov('AB') + '=' + vt(sub(B, A))) + '、' + T(ov('AC') + '=\\left(' + acx + ',\\ ' + acy + '\\right)') + '，兩組分量交叉相乘列一次方程式。',
             p: { A: A, B: B, C: C, which: which, ans: C[which] } };
  };

  /* 1-7 線性組合解係數 */
  L1.linComb = function (r) {
    var a = [r.nz(-3, 3), r.nz(-3, 3)], b = [r.nz(-3, 3), r.nz(-3, 3)];
    while (cross(a, b) === 0) b = [r.nz(-3, 3), r.nz(-3, 3)];
    var x = r.nz(-4, 4), y = r.nz(-4, 4), c = add(sc(x, a), sc(y, b));
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '、' + T(vec('c') + '=' + vt(c)) + '。若 ' + T(vec('c') + '=x' + vec('a') + '+y' + vec('b')) + '，求 ' + T('(x,y)') + '。',
             a: T('(x,y)=' + pt(x, y)),
             h: '分量各寫一條方程式：本題是 ' + T(term(a[0], 'x', true) + term(b[0], 'y', false) + '=' + c[0]) + ' 與 ' + T(term(a[1], 'x', true) + term(b[1], 'y', false) + '=' + c[1]) + '，二元一次聯立；或用克拉瑪 $x=\\dfrac{\\det(\\vec c,\\vec b)}{\\det(\\vec a,\\vec b)}$。',
             p: { a: a, b: b, c: c, ans: [x, y] } };
  };

  /* 1-8 線段上的點：係數判準 */
  L1.segCoef = function (r) {
    var m = r.int(1, 7), n = r.int(1, 7);
    while (m === n || gcd(m, n) !== 1) { m = r.int(1, 7); n = r.int(1, 7); }   /* 題幹的比一律最簡 */
    var ext = r() < 0.5;
    /* 內分 AP:PB=m:n ⟹ AP=(m/(m+n))AB；外分 ⟹ AP=(m/(m-n))AB（m>n 在 B 外、m<n 在 A 外） */
    var x = ext ? F(-n, m - n) : F(n, m + n), y = ext ? F(m, m - n) : F(m, m + n);
    var where = ext ? (m > n ? '在 ' + T('\\overline{AB}') + ' 的延長線上（' + T('B') + ' 在 ' + T('A') + ' 與 ' + T('P') + ' 之間）'
                             : '在 ' + T('\\overline{BA}') + ' 的延長線上（' + T('A') + ' 在 ' + T('B') + ' 與 ' + T('P') + ' 之間）')
                    : '在線段 ' + T('\\overline{AB}') + ' 上';
    return { q: '點 ' + T('P') + ' ' + where + '，且 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '。若 ' + T(ov('OP') + '=x' + ov('OA') + '+y' + ov('OB')) + '（' + T('O') + ' 為任意點），求 ' + T('(x,y)') + '。',
             a: T('(x,y)=\\left(' + Fr.tex(x) + ',\\ ' + Fr.tex(y) + '\\right)'),
             h: (ext ? '外分：' + T('P') + ' 在線段外，' + T(ov('AP') + '=\\dfrac{' + m + '}{' + m + '-' + n + '}' + ov('AB')) + '（係數 ' + (m > n ? '$\\gt 1$' : '$\\lt 0$') + '）'
                     : '內分：' + T(ov('AP') + '=\\dfrac{' + m + '}{' + (m + n) + '}' + ov('AB'))) +
                '；再用 ' + T(ov('OP') + '=' + ov('OA') + '+' + ov('AP')) + ' 與 ' + T(ov('AB') + '=' + ov('OB') + '-' + ov('OA')) + ' 展開合併同類項，兩係數和必為 $1$。',
             p: { m: m, n: n, ext: ext, ans: [fr2(x), fr2(y)] } };
  };

  /* 1-9 坐標內積與夾角 */
  L1.dotCoord = function (r) {
    var a, b, deg, base = r.pick([[1, 0], [1, 1], [2, 1], [1, 2], [3, 1], [1, 3]]);
    /* 0°／180°（退化）壓到 2/24 */
    deg = r.pick([45, 90, 135, 45, 90, 135, 45, 90, 135, 45, 90, 135, 45, 90, 135, 45, 90, 135, 45, 90, 135, 45, 0, 180]);
    var k1 = r.pick([1, 2, 3]), k2 = r.pick([1, 2, 3, -1, -2]);
    a = sc(k1, base);
    var rotd = deg === 45 ? [base[0] - base[1], base[0] + base[1]] : deg === 90 ? [-base[1], base[0]] : deg === 135 ? [-base[0] - base[1], base[0] - base[1]] : deg === 180 ? [-base[0], -base[1]] : base;
    b = sc(Math.abs(k2), rotd);
    if (a[0] === b[0] && a[1] === b[1]) b = sc(2, b);
    var cosv = dot(a, b) / Math.sqrt(n2(a) * n2(b)), ang = Math.round(Math.acos(Math.max(-1, Math.min(1, cosv))) * 180 / Math.PI);
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '，求 ' + T(vec('a') + '\\cdot' + vec('b')) + ' 與兩向量的夾角 ' + T('\\theta') + '。',
             a: T(vec('a') + '\\cdot' + vec('b') + '=' + dot(a, b)) + '，' + T('\\theta=' + ang + '^\\circ'),
             h: '先算內積：' + T(vec('a') + '\\cdot' + vec('b') + '=' + hdot(a, b)) + '；再算 ' + T('|' + vec('a') + '|=' + hsq(a)) + '、' + T('|' + vec('b') + '|=' + hsq(b)) + '，代進 $\\cos\\theta=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec a||\\vec b|}$ 化簡後查特殊角。',
             p: { a: a, b: b, ans: { dot: dot(a, b), deg: ang } } };
  };

  /* 1-10 長度與夾角給定：求內積與 |a+b| */
  L1.dotLenAngle = function (r) {
    var la = r.int(1, 5), lb = r.int(1, 5), deg = r.pick([60, 120, 90, 60, 120]), k1 = r.pick([1, 2, 3]), k2 = r.pick([1, -1, 2, -2]);
    var d = la * lb * (deg === 60 ? 0.5 : deg === 120 ? -0.5 : 0);        /* 整數或 .5 */
    var dF = F(la * lb * (deg === 60 ? 1 : deg === 120 ? -1 : 0), deg === 90 ? 1 : 2);
    var len2 = Fr.add(Fr.add(F(k1 * k1 * la * la), F(k2 * k2 * lb * lb)), Fr.mul(F(2 * k1 * k2), dF));
    var cosT = deg === 60 ? '\\dfrac12' : (deg === 120 ? '\\left(-\\dfrac12\\right)' : '0');
    return { q: '設 ' + T('|' + vec('a') + '|=' + la) + '、' + T('|' + vec('b') + '|=' + lb) + '，且 ' + T(vec('a') + ',' + vec('b')) + ' 的夾角為 ' + T(deg + '^\\circ') + '。求 (1) ' + T(vec('a') + '\\cdot' + vec('b')) + '　(2) ' + T('\\left|' + comb(k1, vec('a'), true) + comb(k2, vec('b'), false) + '\\right|') + '。',
             a: '(1) ' + T(Fr.tex(dF)) + '　(2) ' + T(len2.d === 1 ? sqrtTex(len2.n) : '\\sqrt{' + Fr.tex(len2) + '}'),
             h: '(1) ' + T(vec('a') + '\\cdot' + vec('b') + '=|' + vec('a') + '||' + vec('b') + '|\\cos\\theta=' + la + '\\times ' + lb + '\\times ' + cosT) + '；(2) 長度先平方：' + T('\\left|' + comb(k1, vec('a'), true) + comb(k2, vec('b'), false) + '\\right|^{2}=' + comb(k1 * k1, '|' + vec('a') + '|^{2}', true) + comb(2 * k1 * k2, '\\,' + vec('a') + '\\cdot' + vec('b'), false) + comb(k2 * k2, '|' + vec('b') + '|^{2}', false)) + '，把 ' + T('|' + vec('a') + '|=' + la) + '、' + T('|' + vec('b') + '|=' + lb) + ' 與 (1) 的內積代進去，最後別忘了開根號。',
             p: { la: la, lb: lb, deg: deg, k1: k1, k2: k2, ans: { dot: fr2(dF), len2: fr2(len2) } } };
  };

  /* 1-11 垂直條件 */
  L1.perpCond = function (r) {
    var b = [r.nz(-5, 5), r.nz(-5, 5)], k = r.nz(-3, 3), which = r.pick([0, 1]);
    var a = which === 0 ? [k * b[1], -k * b[0]] : [-k * b[1], k * b[0]];   /* a ⊥ b */
    var t = r.nz(-4, 4); a = add(a, [0, 0]);
    var eq = which === 0 ? term(b[0], 'x', true) + term(a[1] * b[1], '', false)
                         : term(a[0] * b[0], '', true) + term(b[1], 'x', false);
    /* 題目：a=(x, a1) 或 (a0, x) 與 b 垂直 */
    return { q: '設 ' + T(vec('a') + '=' + (which === 0 ? '(x,' + a[1] + ')' : '(' + a[0] + ',x)')) + '、' + T(vec('b') + '=' + vt(b)) + '，若 ' + T(vec('a') + '\\perp' + vec('b')) + '，求 ' + T('x') + '。',
             a: T('x=' + a[which]),
             h: '垂直 ⟺ 內積為 $0$：$a_1b_1+a_2b_2=0$。把本題的 ' + T(vec('b') + '=' + vt(b)) + ' 代進去得 ' + T(eq + '=0') + '，解這個一次方程式。',
             p: { b: b, which: which, known: a[1 - which], ans: a[which] } };
  };

  /* 1-12 正射影向量 */
  L1.projVec = function (r) {
    var b = r.pick([[1, 2], [2, 1], [1, 1], [3, 1], [1, 3], [2, -1], [-1, 2], [1, -1], [3, 4], [4, -3]]);
    var k = r.nz(-3, 3), w = [-b[1], b[0]], m = r.nz(-3, 3);
    var a = add(sc(k, b), sc(m, w));   /* a = k b + m w ⇒ 正射影 = k b */
    return { q: '求 ' + T(vec('a') + '=' + vt(a)) + ' 在 ' + T(vec('b') + '=' + vt(b)) + ' 上的正射影（向量）與正射影長。',
             a: '正射影 ' + T(vt(sc(k, b))) + '，長度 ' + T(sqrtTex(k * k * n2(b))),
             h: '正射影 $=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|^{2}}\\vec b$（分母是平方）。本題 ' + T(vec('a') + '\\cdot' + vec('b') + '=' + hdot(a, b)) + '、' + T('|' + vec('b') + '|^{2}=' + (b[0] * b[0]) + '+' + (b[1] * b[1])) + '，先算出前面那個係數再乘回 ' + T(vec('b')) + '；正射影長 $=\\dfrac{|\\vec a\\cdot\\vec b|}{|\\vec b|}$。',
             p: { a: a, b: b, ans: { proj: sc(k, b), len2: k * k * n2(b) } } };
  };

  /* 1-13 由內積反求夾角 */
  L1.angleFromDot = function (r) {
    var deg = r.pick([30, 45, 60, 90, 120, 135, 150]), c = cosR(deg), la = r.int(1, 4), lb = r.int(1, 4);
    /* a·b = la·lb·num·√rad/den */
    var num = la * lb * c[0], den = c[2], rad = c[1];
    return { q: '設 ' + T('|' + vec('a') + '|=' + la) + '、' + T('|' + vec('b') + '|=' + lb) + '，且 ' + T(vec('a') + '\\cdot' + vec('b') + '=' + radTex(num, rad, den)) + '，求兩向量的夾角。',
             a: T(deg + '^\\circ'),
             h: '由 $\\vec a\\cdot\\vec b=|\\vec a||\\vec b|\\cos\\theta$ 得 ' + T('\\cos\\theta=\\left(' + radTex(num, rad, den) + '\\right)\\div\\left(' + la + '\\times ' + lb + '\\right)') + '，算出來再查特殊角表；負值就是鈍角。',
             p: { la: la, lb: lb, dotNum: num, dotRad: rad, dotDen: den, ans: deg } };
  };

  /* 1-14 三角形面積（行列式） */
  L1.areaDet = function (r) {
    var A = [r.int(-5, 5), r.int(-5, 5)], B = [r.int(-5, 5), r.int(-5, 5)], C = [r.int(-5, 5), r.int(-5, 5)];
    while (cross(sub(B, A), sub(C, A)) === 0) { B = [r.int(-5, 5), r.int(-5, 5)]; C = [r.int(-5, 5), r.int(-5, 5)]; }
    var d = Math.abs(cross(sub(B, A), sub(C, A)));
    return { q: '求以 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + ' 為頂點的三角形面積。',
             a: T(Fr.tex(F(d, 2))),
             h: '先求兩個邊向量：本題 ' + T(ov('AB') + '=' + vt(sub(B, A))) + '、' + T(ov('AC') + '=' + vt(sub(C, A))) + '；面積 $=\\dfrac12|a_1b_2-a_2b_1|$，把這兩組坐標交叉相乘再相減。',
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
             h: '(1) 面積 $=|a_1b_2-a_2b_1|$，本題是 ' + T('\\left|' + a[0] + '\\times ' + hpz(b[1]) + '-' + hpz(a[1]) + '\\times ' + hpz(b[0]) + '\\right|') + '；(2) 把兩個新向量的坐標算出來再用同一條公式，或用伸縮率 ' + T('\\left|\\begin{smallmatrix}' + p + '&' + q + '\\\\' + s + '&' + t + '\\end{smallmatrix}\\right|') + ' 乘上 (1) 的答案。',
             p: { a: a, b: b, p: p, q: q, s: s, t: t, ans: [Math.abs(cross(a, b)), Math.abs(cross(u, v))] } };
  };

  /* 1-16 三邊長求內積 */
  L1.triDot = function (r) {
    var c = r.int(3, 9), b = r.int(3, 9), a = r.int(Math.abs(b - c) + 1, b + c - 1);  /* AB=c, AC=b, BC=a */
    var d = F(b * b + c * c - a * a, 2);
    var M = r() < 0.5;
    return { q: T('\\triangle ABC') + ' 中 ' + T('\\overline{AB}=' + c) + '、' + T('\\overline{BC}=' + a) + '、' + T('\\overline{CA}=' + b) + (M ? '，' + T('M') + ' 為 ' + T('\\overline{CA}') + ' 的中點，求 ' + T(ov('AB') + '\\cdot' + ov('AM')) : '，求 ' + T(ov('AB') + '\\cdot' + ov('AC'))) + '。',
             a: T(Fr.tex(M ? Fr.div(d, F(2)) : d)),
             h: '餘弦定理的變形：' + T(ov('AB') + '\\cdot' + ov('AC') + '=\\dfrac{\\overline{AB}^{2}+\\overline{AC}^{2}-\\overline{BC}^{2}}{2}=\\dfrac{' + c + '^{2}+' + b + '^{2}-' + a + '^{2}}{2}') + (M ? '；本題問的是 ' + T(ov('AB') + '\\cdot' + ov('AM')) + '，由 ' + T(ov('AM') + '=\\dfrac12' + ov('AC')) + ' 把上面的結果再減半。' : '。'),
             p: { c: c, b: b, a: a, M: M, ans: fr2(M ? Fr.div(d, F(2)) : d) } };
  };

  /* 1-17 柯西：x²+y²=r² 上 px+qy 的最大值 */
  L1.cauchyCircle = function (r) {
    var p = r.nz(-5, 5), q = r.nz(-5, 5), R2 = r.pick([1, 4, 9, 16, 25, 2, 5, 10]);
    var M2 = (p * p + q * q) * R2;
    return { q: '設實數 ' + T('x,y') + ' 滿足 ' + T('x^{2}+y^{2}=' + R2) + '，求 ' + T(term(p, 'x', true) + term(q, 'y', false)) + ' 的最大值。',
             a: T(sqrtTex(M2)),
             h: '柯西：$(px+qy)^{2}\\le(p^{2}+q^{2})(x^{2}+y^{2})$。本題代進去是 ' + T('\\left(' + term(p, 'x', true) + term(q, 'y', false) + '\\right)^{2}\\le\\left(' + (p * p) + '+' + (q * q) + '\\right)\\times ' + R2) + '，開根號取正號就是最大值。',
             p: { p: p, q: q, R2: R2, ans: M2 } };
  };

  /* 1-18 砝碼：aPA+bPB+cPC=0 ⇒ 面積比 */
  L1.weightArea = function (r) {
    var a = r.int(1, 5), b = r.int(1, 5), c = r.int(1, 5);
    return { q: T('P') + ' 在 ' + T('\\triangle ABC') + ' 內部且 ' + T(comb(a, ov('PA'), true) + comb(b, ov('PB'), false) + comb(c, ov('PC'), false) + '=\\vec0') + '，求 ' + T('\\triangle PBC:\\triangle PCA:\\triangle PAB') + '，以及 ' + T('\\dfrac{\\triangle PBC}{\\triangle ABC}') + '。',
             a: T(a / gcd(gcd(a, b), c) + ':' + b / gcd(gcd(a, b), c) + ':' + c / gcd(gcd(a, b), c)) + '，' + T(Fr.tex(F(a, a + b + c))),
             h: '把 ' + T('P') + ' 看成三個砝碼 ' + T(String(a)) + '、' + T(String(b)) + '、' + T(String(c)) + ' 的平衡點：某個頂點的砝碼越重，它對面那個小三角形就越大——三個面積比就是這三個係數（記得約成最簡整數比）。第二問的分母是三個係數的和 ' + T(a + '+' + b + '+' + c) + '。',
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
             h: '判準：在內部 ⟺ $x\\gt 0$、$y\\gt 0$ 且 $x+y\\lt 1$。本題 ' + T('x=' + Fr.tex(x)) + '、' + T('y=' + Fr.tex(y)) + '，先算 ' + T('x+y=' + Fr.tex(x) + (y.n < 0 ? '' : '+') + Fr.tex(y)) + ' 再對照判準；面積比 $\\triangle PBC:\\triangle PCA:\\triangle PAB=(1-x-y):x:y$。',
             p: { x: fr2(x), y: fr2(y), ans: { inside: inside, onBC: onBC, ratio: inside ? fr2(Fr.sub(F(1), sum)) : null } } };
  };

  /* 1-20 距離：|ta+b| 的最小值 */
  L1.minLen = function (r) {
    var a = r.pick([[1, 2], [2, 1], [3, 1], [1, 3], [2, -1], [1, -2], [3, 4], [4, 3]]), k = r.nz(-3, 3), m = r.nz(-4, 4), w = [-a[1], a[0]];
    var b = add(sc(k, a), sc(m, w));
    var min2 = m * m * n2(a);   /* 最小長度平方 = |m w|^2 */
    return { q: '設 ' + T('t') + ' 為實數，' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '，求 ' + T('|t' + vec('a') + '+' + vec('b') + '|') + ' 的最小值。',
             a: T(sqrtTex(min2)) + '（' + T('t=' + (-k)) + ' 時）',
             h: '先平方：$|t\\vec a+\\vec b|^{2}=t^{2}|\\vec a|^{2}+2t\\,\\vec a\\cdot\\vec b+|\\vec b|^{2}$，本題是 ' + T(term(n2(a), 't^{2}', true) + term(2 * dot(a, b), 't', false) + term(n2(b), '', false)) + '，對 $t$ 配方取最小，最後記得開根號；也可看成「$\\vec b$ 的終點到方向為 $\\vec a$ 的直線的距離」$=\\dfrac{\\left|\\det(\\vec a,\\vec b)\\right|}{|\\vec a|}$。',
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
             h: '以 ' + T(ov('AB') + ',' + ov('AD')) + ' 為基底，本題 ' + T(ov('AE') + '=' + Fr.tex(e) + ov('AB') + '+' + ov('AD')) + '、' + T(ov('AF') + '=' + Fr.tex(f) + ov('AB')) + '、' + T(ov('AC') + '=' + ov('AB') + '+' + ov('AD')) + '。設 ' + T(ov('BP') + '=t' + ov('BE')) + ' 把 ' + T(ov('AP')) + ' 寫成 ' + T('t') + ' 的式子，再用「' + T('P') + ' 也在 ' + T('\\overline{CF}') + ' 上（對 ' + T('C,F') + ' 的係數和為 $1$）」解出 ' + T('t') + '。',
             p: { e: fr2(e), f: fr2(f), ans: { BP: fr2(BP), PE: fr2(PE), x: fr2(x), y: fr2(y) } } };
  };

  /* 2-2 係數 ⟹ 三個小三角形面積 */
  L2.coefArea = function (r) {
    var d = r.pick([6, 8, 10, 12, 15, 20]), xn = r.int(1, d - 2), yn = r.int(1, d - 1 - xn);
    var x = F(xn, d), y = F(yn, d), z = F(d - xn - yn, d), S = d * r.int(2, 8);
    return { q: T('P') + ' 在 ' + T('\\triangle ABC') + ' 內且 ' + T(ov('AP') + '=' + combF(x, ov('AB'), true) + combF(y, ov('AC'), false)) + '，' + T('\\triangle ABC') + ' 的面積為 ' + T(String(S)) + '。求 ' + T('\\triangle PBC') + '、' + T('\\triangle PCA') + '、' + T('\\triangle PAB') + ' 的面積。',
             a: T(String(S * z.n / z.d)) + '、' + T(String(S * x.n / x.d)) + '、' + T(String(S * y.n / y.d)),
             h: '係數就是「到對邊的距離比」：$\\triangle PBC:\\triangle PCA:\\triangle PAB=(1-x-y):x:y$。本題 ' + T('x=' + Fr.tex(x)) + '、' + T('y=' + Fr.tex(y)) + '，先算 ' + T('1-x-y=1-' + Fr.tex(x) + '-' + Fr.tex(y)) + '，再把三個比例各乘上總面積 ' + T(String(S)) + '。',
             p: { x: fr2(x), y: fr2(y), S: S, ans: [S * z.n / z.d, S * x.n / x.d, S * y.n / y.d] } };
  };

  /* 2-3 過定點的直線截兩邊：1/x+1/y 恆等式與 x+y 最小 */
  L2.lineThroughPoint = function (r) {
    var m = r.int(1, 10), n = r.int(1, 10);  /* D 在 BC 上 BD:DC = m:n ⇒ AD = n/(m+n) AB + m/(m+n) AC */
    while (gcd(m, n) !== 1) { m = r.int(1, 10); n = r.int(1, 10); }              /* 題幹的比一律最簡 */
    var p = F(n, m + n), q = F(m, m + n);   /* AD = p AB + q AC = (p/x) AE + (q/y) AF ⇒ p/x + q/y = 1 */
    /* x + y 最小：x+y = (x+y)(p/x+q/y) = p + q + p y/x + q x/y ≥ p+q+2√(pq) */
    var pq = Fr.mul(p, q), sq = simpSqrt(pq.n * pq.d);  /* √(pq) = √(pq.n·pq.d)/pq.d */
    var minTex = Fr.tex(Fr.add(p, q)) + '+' + (sq.r === 1 ? Fr.tex(F(2 * sq.c, pq.d)) : Fr.tex(F(2 * sq.c, pq.d)) + '\\sqrt{' + sq.r + '}');
    if (sq.r === 1) minTex = Fr.tex(Fr.add(Fr.add(p, q), F(2 * sq.c, pq.d)));
    return { q: T('\\triangle ABC') + ' 中，' + T('D') + ' 在 ' + T('\\overline{BC}') + ' 上且 ' + T('\\overline{BD}:\\overline{DC}=' + m + ':' + n) + '。過 ' + T('D') + ' 的直線交直線 ' + T('AB') + '、' + T('AC') + ' 於 ' + T('E,F') + '，' + T(ov('AE') + '=x' + ov('AB')) + '、' + T(ov('AF') + '=y' + ov('AC')) + '（' + T('x,y\\gt0') + '）。<br>(1) 求 ' + T('\\dfrac{p}{x}+\\dfrac{q}{y}=1') + ' 中的 ' + T('(p,q)') + '　(2) 求 ' + T('x+y') + ' 的最小值。',
             a: '(1) ' + T('(p,q)=\\left(' + Fr.tex(p) + ',\\ ' + Fr.tex(q) + '\\right)') + '　(2) ' + T(minTex),
             h: '(1) 先把 ' + T(ov('AD')) + ' 寫成 ' + T(ov('AB') + ',' + ov('AC')) + ' 的組合：本題 ' + T(ov('AD') + '=' + ov('AB') + '+\\dfrac{' + m + '}{' + (m + n) + '}' + ov('BC')) + '，再把 ' + T(ov('BC') + '=' + ov('AC') + '-' + ov('AB')) + ' 代進去展開；接著用 ' + T(ov('AB') + '=\\dfrac1x' + ov('AE')) + '、' + T(ov('AC') + '=\\dfrac1y' + ov('AF')) + ' 換掉，' + T('E,D,F') + ' 共線 ⟹ 兩係數和為 $1$。(2) $x+y=(x+y)\\left(\\dfrac px+\\dfrac qy\\right)=p+q+\\dfrac{py}{x}+\\dfrac{qx}{y}\\ge p+q+2\\sqrt{pq}$，而本題 $p+q=1$。',
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
             h: '區域是一個平行四邊形：面積 $=(x$ 的長度$)\\times(y$ 的長度$)\\times\\left|\\det(\\vec u,\\vec v)\\right|$。本題 ' + T('x') + ' 的長度是 ' + T(x2 + '-' + hpz(x1)) + '、' + T('y') + ' 的長度是 ' + T(y2 + '-' + hpz(y1)) + '，而 ' + T('\\left|\\det(\\vec u,\\vec v)\\right|=\\left|' + u[0] + '\\times ' + hpz(v[1]) + '-' + hpz(u[1]) + '\\times ' + hpz(v[0]) + '\\right|') + '。',
             p: { u: u, v: v, x1: x1, x2: x2, y1: y1, y2: y2, ans: A } };
  };

  /* 2-5 |u|=k|v|=|au+bv| ⟹ cosθ */
  L2.cosFromLen = function (r) {
    /* |u| = k|v| = |a u + b v|：令 |v|=t、|u|=kt，展開得 cosθ = (k²(1-a²)-b²)/(2abk)。
       b 只從「|cosθ|<1」的真解集裡挑（a=1 ⟹ |b|<2k；a=2 ⟹ k<|b|<3k；a=3 ⟹ 2k<|b|<4k），
       所以不再需要 fallback，也不會出現 cosθ=±1 的退化題。 */
    var a = r.pick([1, 2, 3]), k = r.pick(a === 1 ? [1, 2, 3, 4] : [2, 3, 4]), cand = [], i, cs;
    for (i = -20; i <= 20; i++) {                    /* |cosθ|<1 且 a、b 互質（不出 |2u+2v| 這種可約寫法） */
      if (i === 0 || gcd(a, Math.abs(i)) !== 1) continue;
      cs = F(k * k * (1 - a * a) - i * i, 2 * a * i * k);
      if (Math.abs(cs.n) < Math.abs(cs.d)) cand.push(i);
    }
    var b = r.pick(cand), cos = F(k * k * (1 - a * a) - b * b, 2 * a * b * k);
    var kt = (k === 1 ? 't' : k + 't');
    return { q: '設 ' + T(vec('u') + ',' + vec('v')) + ' 為非零向量，且 ' + T('|' + vec('u') + '|=' + (k === 1 ? '' : k) + '|' + vec('v') + '|=\\left|' + comb(a, vec('u'), true) + comb(b, vec('v'), false) + '\\right|') + '，' + T('\\theta') + ' 為兩向量的夾角，求 ' + T('\\cos\\theta') + '。',
             a: T('\\cos\\theta=' + Fr.tex(cos)),
             h: '設 ' + T('|' + vec('v') + '|=t') + '、' + T('|' + vec('u') + '|=' + kt) + '，把 ' + T('\\left|' + comb(a, vec('u'), true) + comb(b, vec('v'), false) + '\\right|^{2}') + ' 展開：' + T(comb(a * a, '|' + vec('u') + '|^{2}', true) + comb(2 * a * b, '\\,' + vec('u') + '\\cdot' + vec('v'), false) + comb(b * b, '|' + vec('v') + '|^{2}', false) + '=|' + vec('u') + '|^{2}') + '，$t^{2}$ 全部約掉後解出 ' + T(vec('u') + '\\cdot' + vec('v')) + '，再用 $\\cos\\theta=\\dfrac{\\vec u\\cdot\\vec v}{|\\vec u||\\vec v|}$。',
             p: { k: k, a: a, b: b, ans: fr2(cos) } };
  };

  /* 2-6 由 |au−bv| 求正射影長 */
  L2.projLen = function (r) {
    var lu = r.int(1, 4), lv = r.int(1, 4), a = r.pick([1, 2, 3]), b = r.pick([1, 2, 3]);
    var deg = r.pick([60, 120, 60, 120, 60, 120, 60, 120, 60, 120, 60, 90]);   /* 90°（答案 0）降到 1/12 */
    var uv = F(lu * lv * (deg === 60 ? 1 : deg === 120 ? -1 : 0), deg === 90 ? 1 : 2);
    var L2v = Fr.add(F(a * a * lu * lu + b * b * lv * lv), Fr.mul(F(-2 * a * b), uv));   /* |au-bv|^2 */
    var projl = Fr.div(uv, F(lv));  /* u 在 v 上的正射影長（可為負，取絕對值） */
    return { q: '設非零向量 ' + T(vec('u') + ',' + vec('v')) + ' 滿足 ' + T('|' + vec('u') + '|=' + lu) + '、' + T('|' + vec('v') + '|=' + lv) + '、' + T('\\left|' + comb(a, vec('u'), true) + comb(-b, vec('v'), false) + '\\right|=' + rootTexF(L2v)) + '，求 ' + T(vec('u')) + ' 在 ' + T(vec('v')) + ' 上的正射影長。',
             a: T(Fr.tex(F(Math.abs(projl.n), projl.d))),
             h: '把已知長度平方展開：' + T('\\left|' + comb(a, vec('u'), true) + comb(-b, vec('v'), false) + '\\right|^{2}=' + comb(a * a, '|' + vec('u') + '|^{2}', true) + comb(-2 * a * b, '\\,' + vec('u') + '\\cdot' + vec('v'), false) + comb(b * b, '|' + vec('v') + '|^{2}', false)) + '，代入 ' + T('|' + vec('u') + '|=' + lu) + '、' + T('|' + vec('v') + '|=' + lv) + ' 解出 ' + T(vec('u') + '\\cdot' + vec('v')) + '；正射影長 $=\\dfrac{|\\vec u\\cdot\\vec v|}{|\\vec v|}$（「長度」只除一次）。',
             p: { lu: lu, lv: lv, a: a, b: b, L2: fr2(L2v), ans: fr2(F(Math.abs(projl.n), projl.d)) } };
  };

  /* 2-7 柯西：ax²+by²=c 上 px+qy 的最大值與達成點 */
  L2.cauchyEllipse = function (r) {
    var A = r.pick([1, 4, 9]), B = r.pick([1, 4, 9, 16]); while (A === B) B = r.pick([4, 9, 16, 25]);
    var sa = Math.round(Math.sqrt(A)), sb = Math.round(Math.sqrt(B));
    /* 取 x = sb·m/g?... 直接設達成點 (x0,y0) 使 A x0² + B y0² = C，且 (p,q) ∥ (A x0, B y0) */
    var x0 = r.nz(-3, 3), y0 = r.nz(-3, 3), C = A * x0 * x0 + B * y0 * y0;
    var g = gcd(A * x0, B * y0), p = A * x0 / g, q = B * y0 / g, M = p * x0 + q * y0;
    var ca = (A === 1 ? 'p^{2}' : '\\dfrac{p^{2}}{' + A + '}'), cb = (B === 1 ? 'q^{2}' : '\\dfrac{q^{2}}{' + B + '}');
    var na = (A === 1 ? String(p * p) : '\\dfrac{' + (p * p) + '}{' + A + '}'), nb = (B === 1 ? String(q * q) : '\\dfrac{' + (q * q) + '}{' + B + '}');
    return { q: '實數 ' + T('x,y') + ' 滿足 ' + T((A === 1 ? '' : A) + 'x^{2}+' + (B === 1 ? '' : B) + 'y^{2}=' + C) + '。求 ' + T(term(p, 'x', true) + term(q, 'y', false)) + ' 的最大值，以及達到最大值時的 ' + T('(x,y)') + '。',
             a: '最大值 ' + T(String(M)) + '，' + T('(x,y)=' + pt(x0, y0)),
             h: '柯西：$(px+qy)^{2}\\le\\left(' + ca + '+' + cb + '\\right)(' + (A === 1 ? '' : A) + 'x^{2}+' + (B === 1 ? '' : B) + 'y^{2})$。本題代進去是 ' + T('\\left(' + term(p, 'x', true) + term(q, 'y', false) + '\\right)^{2}\\le\\left(' + na + '+' + nb + '\\right)\\times ' + C) + '，等號在 $(' + (A === 1 ? '' : A) + 'x,' + (B === 1 ? '' : B) + 'y)\\parallel(' + p + ',' + q + ')$ 時成立。',
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
             h: '把 ' + T(ov('OP')) + ' 拆成 ' + T(ov('OM') + '+' + ov('MP')) + '（' + T('M') + ' 為圓心）：' + T(ov('OP') + '\\cdot' + ov('OQ') + '=' + ov('OM') + '\\cdot' + ov('OQ') + '+' + ov('MP') + '\\cdot' + ov('OQ')) + '。本題圓心是 ' + T('M' + vt([h, k])) + '、半徑 ' + T(String(R)) + '，所以前一項是定值 ' + T(hdot([h, k], q)) + '；後一項最大為 ' + T(R + '\\times ' + hsq(q)) + '（' + T(ov('MP')) + ' 與 ' + T(ov('OQ')) + ' 同向時）。',
             p: { h: h, k: k, R: R, q: q, ans: M } };
  };

  /* 2-10 內積在拋物線上的最小值 */
  L2.dotParabola = function (r) {
    /* A, B 固定，C=(x, x²/k)；AB·AC = d1(x-a1) + d2(x²/k - a2)，二次式 */
    var kden = r.pick([1, 2, 4]), d = [r.nz(-4, 4), r.pick([1, 2, 4, 8])], A = [r.int(-3, 3), r.int(-3, 3)], B = add(A, d);
    /* f(x) = d1 (x - A0) + d2 (x²/kden - A1) ⇒ 頂點 x = -d1 kden/(2 d2) */
    var xv = F(-d[0] * kden, 2 * d[1]);
    var fmin = Fr.add(Fr.mul(F(d[0]), Fr.sub(xv, F(A[0]))), Fr.mul(F(d[1]), Fr.sub(Fr.div(Fr.mul(xv, xv), F(kden)), F(A[1]))));
    var yT = (kden === 1 ? 'x^{2}' : '\\dfrac{x^{2}}{' + kden + '}');
    var off = function (v) { return v > 0 ? '-' + v : (v < 0 ? '+' + (-v) : ''); };
    return { q: T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，' + T('C') + ' 在拋物線 ' + T('y=' + yT) + ' 上變動。求 ' + T(ov('AB') + '\\cdot' + ov('AC')) + ' 的最小值，以及此時 ' + T('C') + ' 的 ' + T('x') + ' 坐標。',
             a: '最小值 ' + T(Fr.tex(fmin)) + '，' + T('x=' + Fr.tex(xv)),
             h: '設 $C\\left(x,' + yT + '\\right)$，則本題 ' + T(ov('AB') + '=' + vt(d)) + '、' + T(ov('AC') + '=\\left(x' + off(A[0]) + ',\\ ' + yT + off(A[1]) + '\\right)') + '；兩者內積展開後是 ' + T('x') + ' 的二次式，配方即得最小值與對應的 ' + T('x') + '。',
             p: { A: A, B: B, kden: kden, ans: { min: fr2(fmin), x: fr2(xv) } } };
  };

  /* 2-11 外心→垂心：OH = OA+OB+OC */
  L2.orthocenter = function (r) {
    var R2 = r.pick([25, 25, 50, 65, 85, 100, 130]);
    var pts = [];
    for (var x = -12; x <= 12; x++) for (var y = -12; y <= 12; y++) if (x * x + y * y === R2) pts.push([x, y]);
    var P = r.shuffle(pts).slice(0, 3);
    /* 外心在原點時，兩點互為對徑點 ⟺ 直角三角形（垂心會落在頂點上）⟹ 重抽 */
    while (Math.abs(cross(sub(P[1], P[0]), sub(P[2], P[0]))) === 0 || antipodal(P[0], P[1]) || antipodal(P[1], P[2]) || antipodal(P[0], P[2])) P = r.shuffle(pts).slice(0, 3);
    var H = add(add(P[0], P[1]), P[2]), G = [F(H[0], 3), F(H[1], 3)];
    return { q: T('O(0,0)') + ' 為 ' + T('\\triangle ABC') + ' 的外心，' + T('A' + vt(P[0])) + '、' + T('B' + vt(P[1])) + '、' + T('C' + vt(P[2])) + '。求 (1) 重心 ' + T('G') + '　(2) 垂心 ' + T('H') + '。',
             a: '(1) ' + T('G' + vtF(G)) + '　(2) ' + T('H' + vt(H)),
             h: '外心在原點時 ' + T(ov('OH') + '=' + ov('OA') + '+' + ov('OB') + '+' + ov('OC')) + '，而重心 ' + T(ov('OG') + '=\\dfrac13\\left(' + ov('OA') + '+' + ov('OB') + '+' + ov('OC') + '\\right)') + '。本題把三個坐標相加：' + T('x') + ' 是 ' + T(hsum([P[0][0], P[1][0], P[2][0]])) + '、' + T('y') + ' 是 ' + T(hsum([P[0][1], P[1][1], P[2][1]])) + '；算完可用 ' + T(ov('AH') + '\\cdot' + ov('BC') + '=0') + ' 檢驗。',
             p: { A: P[0], B: P[1], C: P[2], ans: { G: [fr2(G[0]), fr2(G[1])], H: H } } };
  };

  /* 2-12 三向量和的長度範圍 */
  L2.sumRange = function (r) {
    var L = r.shuffle([r.int(1, 6), r.int(1, 6), r.int(1, 8)]);
    var mx = L.reduce(function (s, v) { return s + v; }, 0), big = Math.max.apply(null, L), rest = mx - big;
    var mn = big <= rest ? 0 : big - rest;
    var others = L.slice(); others.splice(others.indexOf(big), 1);
    return { q: '平面向量 ' + T(vec('a') + ',' + vec('b') + ',' + vec('c')) + ' 滿足 ' + T('|' + vec('a') + '|=' + L[0]) + '、' + T('|' + vec('b') + '|=' + L[1]) + '、' + T('|' + vec('c') + '|=' + L[2]) + '。設 ' + T('s=|' + vec('a') + '+' + vec('b') + '+' + vec('c') + '|') + '，求 ' + T('s') + ' 的範圍。',
             a: T(mn + '\\le s\\le ' + mx),
             h: '上界：三支同向時最大，' + T('s\\le ' + L[0] + '+' + L[1] + '+' + L[2]) + '。下界：本題最長的一支是 ' + T(String(big)) + '，另外兩支是 ' + T(String(others[0])) + ' 與 ' + T(String(others[1])) + '——最長的那支能不能被另外兩支「抵銷」？三個長度圍得成三角形（含退化）就能到 $0$，否則下界是「最長減其餘兩支之和」。',
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
             h: '本題 ' + T(vec('a') + '+t' + vec('b') + '=\\left(' + hlin(a[0], b[0]) + ',\\ ' + hlin(a[1], b[1]) + '\\right)') + '。(1) 平行 ' + T(vec('c')) + ' ⟺ 與 ' + T(vec('c')) + ' 交叉相乘相等（行列式為 $0$）' + (t2F ? '；(2) 垂直 ⟺ 與 ' + T(vec('c')) + ' 的內積為 $0$' : '') + '；(' + (t2F ? 3 : 2) + ') ' + T('\\left|' + vec('a') + '+t' + vec('b') + '\\right|^{2}=' + term(n2(b), 't^{2}', true) + term(2 * dot(a, b), 't', false) + term(n2(a), '', false)) + '，對 $t$ 配方，最小值記得開根號。',
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
             h: T(ov('OC') + '=' + ov('OA') + '+' + ov('AB') + '+' + ov('BC')) + '；設出發方向為 $x$ 軸正向，三段的方向角依序是 $0^\\circ$、$' + ang1 + '^\\circ$、$' + ang2 + '^\\circ$，各段寫成 $(d\\cos\\theta,\\ d\\sin\\theta)$：本題是 ' + T(d1 + '\\left(\\cos 0^\\circ,\\ \\sin 0^\\circ\\right)') + '、' + T(d2 + '\\left(\\cos ' + ang1 + '^\\circ,\\ \\sin ' + ang1 + '^\\circ\\right)') + '、' + T(d3 + '\\left(\\cos ' + ang2 + '^\\circ,\\ \\sin ' + ang2 + '^\\circ\\right)') + ' 三個相加，最後 $\\overline{OC}=\\sqrt{x^{2}+y^{2}}$。',
             p: { d1: d1, d2: d2, d3: d3, turn: turn, turn2: turn2, ans: { Q: fr2(Q), R: fr2(Rt) } } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p 重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     用法：用 splice 腳本插在 META（var META_L1／var META = {）之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     ══════════════════════════════════════════════════════════ */
  function fF(t) { return F(t[0], t[1]); }                       /* p 裡的 [n,d] 還原成分數 */
  function sgT(n) { return n < 0 ? '-' + (-n) : '+' + n; }        /* 相加時的正負號 */
  function parT(s) { return '\\left(' + s + '\\right)'; }
  function combD(k, s, first) {   /* 同 combF，但用 \dfrac（步驟裡與答案的寫法一致） */
    if (k.n === 0) return '';
    var ab = F(Math.abs(k.n), k.d);
    return (k.n < 0 ? '-' : (first ? '' : '+')) + (Fr.eq(ab, F(1)) ? '' : Fr.tex(ab)) + s;
  }
  function COSD(deg) {                                            /* 0°～180° 特殊角的 cos（本章只會用到這幾個） */
    return { 0: '1', 30: '\\dfrac{\\sqrt3}{2}', 45: '\\dfrac{\\sqrt2}{2}', 60: '\\dfrac12', 90: '0',
             120: '-\\dfrac12', 135: '-\\dfrac{\\sqrt2}{2}', 150: '-\\dfrac{\\sqrt3}{2}', 180: '-1' }[deg];
  }

  var L1_H1 = {
    vecOps: '這是「向量的坐標運算」：係數先各自乘進兩個分量，再把對應分量相加；長度最後才用畢氏算。',
    chain: '這是「首尾相接的化簡」：先把每個減號的項翻成反向量，翻完之後每一項的終點都會是下一項的起點。',
    divPoint: '這是「分點坐標」：先判斷是內分還是外分，再套分點公式——權重是「交叉配」的，$x$、$y$ 兩個坐標各算一次。',
    centroid: '這是「重心與面積」：重心是三頂點的平均，先反解出第三個頂點；面積再用兩個邊向量的行列式。',
    parallelCond: '這是「平行條件」：平行就是行列式為 $0$，也就是交叉相乘相等，代進去會得到一個一次方程式。',
    collinear: '這是「三點共線」：共線就是兩個邊向量平行，先把兩個邊向量寫出來（其中一個帶未知數）再交叉相乘。',
    linComb: '這是「線性組合解係數」：把向量等式拆成兩個分量方程式，變成二元一次聯立。',
    segCoef: '這是「線段上的點：係數判準」：先用比例把 $\\overrightarrow{AP}$ 寫成 $\\overrightarrow{AB}$ 的倍數，再換成以 $O$ 為起點的向量。',
    coefRegion: '這是「係數與位置」：只看兩個係數的正負與它們的和跟 $1$ 的大小，就能判斷點落在哪一區。',
    weightArea: '這是「砝碼與面積比」：把等式看成三個頂點各掛一個砝碼而 $P$ 是平衡點，面積比就是砝碼比。',
    dotCoord: '這是「坐標內積與夾角」：先算內積，再算兩個長度，最後才代夾角公式並查特殊角。',
    dotLenAngle: '這是「長度與夾角求內積」：先用 $|\\vec a||\\vec b|\\cos\\theta$ 算內積；長度不要直接算，先平方展開。',
    perpCond: '這是「垂直條件」：垂直就是內積為 $0$，把兩個分量乘起來相加等於 $0$。',
    projVec: '這是「正射影」：先算內積與 $|\\vec b|^{2}$，兩者相除就是要乘回 $\\vec b$ 的係數。',
    angleFromDot: '這是「由內積反求夾角」：把內積、兩個長度代進 $\\cos\\theta$ 的公式，算出來再查特殊角表。',
    areaDet: '這是「三角形面積」：先取同一個頂點出發的兩個邊向量，再用行列式的一半。',
    paraArea: '這是「平行四邊形面積」：面積就是兩個向量的行列式絕對值；換成線性組合時面積會乘上係數行列式。',
    triDot: '這是「三邊長求內積」：把第三邊寫成兩個向量的差再平方，就能把內積用三個邊長表示出來。',
    cauchyCircle: '這是「柯西不等式」：把要求最大值的式子看成兩個向量的內積，再用柯西壓住它。',
    minLen: '這是「$|t\\vec a+\\vec b|$ 的最小值」：先平方變成 $t$ 的二次式再配方，最後別忘了開根號。'
  };

  var L1_SOL = {};

  /* 1-1 坐標運算與長度 */
  L1_SOL.vecOps = function (p, o) {
    var u = sc(p.k1, p.a), v = sc(p.k2, p.b), ans = p.ans;
    return ['先把係數乘進分量：$' + comb(p.k1, vec('a'), true) + '=' + parT(p.k1 + '\\times ' + hpz(p.a[0]) + ',\\ ' + p.k1 + '\\times ' + hpz(p.a[1])) + '=' + vt(u) + '$、$' + comb(p.k2, vec('b'), true) + '=' + vt(v) + '$。',
      '再把兩組對應分量相加：$' + parT(u[0] + sgT(v[0]) + ',\\ ' + u[1] + sgT(v[1])) + '=' + vt(ans) + '$。',
      '長度用畢氏：$\\sqrt{' + (ans[0] * ans[0]) + '+' + (ans[1] * ans[1]) + '}=' + sqrtTex(p.len2) + '$。答案：' + o.a + '。'];
  };

  /* 1-2 首尾相接化簡 */
  L1_SOL.chain = function (p, o) {
    var tm = p.expr.match(/[+-]?\\overrightarrow\{[A-Z]{2}\}/g), flip = [], ch = [];
    for (var i = 0; i < tm.length; i++) {
      var lb = tm[i].slice(-3, -1), rev = lb.charAt(1) + lb.charAt(0);
      if (tm[i].charAt(0) === '-') { flip.push('$-' + ov(lb) + '=' + ov(rev) + '$'); lb = rev; }
      ch.push(lb);
    }
    var joined = [];
    for (i = 0; i < ch.length; i++) joined.push(ov(ch[i]));
    return ['「減一個向量」就是「加上它的反向量」：$-' + ov('XY') + '=' + ov('YX') + '$。' + (flip.length ? '本題要翻的是 ' + flip.join('、') + '。' : '本題四項都是正號，不必翻。'),
      '翻完之後整串變成 $' + joined.join('+') + '$——每一項的終點正好是下一項的起點，可以首尾相接。',
      '相接時中間的字母全部消掉，只剩最前面的起點 $' + p.start + '$ 與最後面的終點 $' + p.end + '$，得 ' + o.a + '。'];
  };

  /* 1-3 分點坐標 */
  L1_SOL.divPoint = function (p, o) {
    var A = p.A, Bq = p.B, m = p.m, n = p.n, ca, cb, den;
    if (!p.ext) { ca = n; cb = m; den = m + n; }
    else if (n - m > 0) { ca = n; cb = -m; den = n - m; }
    else { ca = -n; cb = m; den = m - n; }
    var num = [ca * A[0] + cb * Bq[0], ca * A[1] + cb * Bq[1]];
    var frac = function (top, bot) { return bot === 1 ? String(top) : '\\dfrac{' + top + '}{' + bot + '}'; };
    var sb = function (i) {
      return frac(hpz(ca) + '\\times ' + hpz(A[i]) + '+' + hpz(cb) + '\\times ' + hpz(Bq[i]), den) + '=' + frac(num[i], den) + (den === 1 ? '' : '=' + Fr.tex(F(num[i], den)));
    };
    return [(p.ext ? '$P$ 在直線 $AB$ 上但不在線段上，是外分點：$\\overline{AP}:\\overline{PB}=' + m + ':' + n + '$ ⟹ $P=' + frac(comb(ca, 'A', true) + comb(cb, 'B', false), den) + '$（外分是相減，分母也跟著相減）。'
                : '$P$ 在線段 $AB$ 上，是內分點：$\\overline{AP}:\\overline{PB}=' + m + ':' + n + '$ ⟹ $P=' + frac(comb(ca, 'A', true) + comb(cb, 'B', false), den) + '$——離 $A$ 近的權重反而給 $A$，這就是「交叉配」。'),
      '$x$ 坐標：$' + sb(0) + '$。',
      '$y$ 坐標：$' + sb(1) + '$。答案：' + o.a + '。'];
  };

  /* 1-4 重心與面積 */
  L1_SOL.centroid = function (p, o) {
    var A = p.A, Bq = p.B, G = p.G, C = p.ans.C, u = sub(Bq, A), v = sub(C, A), d = cross(u, v);
    return ['重心是三頂點的平均：$G=\\dfrac{A+B+C}{3}$，兩邊乘 $3$ 再移項就得到 $C=3G-A-B$。',
      '代入本題：$C=3' + vt(G) + '-' + vt(A) + '-' + vt(Bq) + '=' + vt(C) + '$（兩個分量各算一次）。',
      '面積用兩個邊向量的行列式：$' + ov('AB') + '=' + vt(u) + '$、$' + ov('AC') + '=' + vt(v) + '$，面積 $=\\dfrac12\\left|' + u[0] + '\\times ' + hpz(v[1]) + '-' + hpz(u[1]) + '\\times ' + hpz(v[0]) + '\\right|=\\dfrac12\\times ' + Math.abs(d) + '=' + Fr.tex(F(Math.abs(d), 2)) + '$。答案：' + o.a + '。'];
  };

  /* 1-5 平行條件 */
  L1_SOL.parallelCond = function (p, o) {
    var b = p.b, kn = p.known, w = p.which;
    var av = w === 0 ? '(x,' + kn + ')' : '(' + kn + ',x)';
    var lhs = w === 0 ? 'x\\times ' + hpz(b[1]) + '-' + hpz(kn) + '\\times ' + hpz(b[0])
                      : hpz(kn) + '\\times ' + hpz(b[1]) + '-x\\times ' + hpz(b[0]);
    var cx = w === 0 ? b[1] : -b[0], cc = w === 0 ? -kn * b[0] : kn * b[1];
    return ['兩個向量平行 ⟺ 它們的行列式為 $0$，也就是交叉相乘相等：$a_1b_2-a_2b_1=0$。',
      '本題 $' + vec('a') + '=' + av + '$、$' + vec('b') + '=' + vt(b) + '$，代進去得 $' + lhs + '=0$，即 $' + term(cx, 'x', true) + term(cc, '', false) + '=0$。',
      '解這個一次方程式：$x=' + Fr.tex(F(-cc, cx)) + '$。答案：' + o.a + '。'];
  };

  /* 1-6 三點共線 */
  L1_SOL.collinear = function (p, o) {
    var A = p.A, Bq = p.B, C = p.C, w = p.which, u = sub(Bq, A);
    var ux = function (v) { return 'x' + (v > 0 ? '-' + v : (v < 0 ? '+' + (-v) : '')); };
    var v1 = w === 0 ? parT(ux(A[0])) : hpz(C[0] - A[0]), v2 = w === 1 ? parT(ux(A[1])) : hpz(C[1] - A[1]);
    return ['三點共線就是「同一個起點拉出去的兩個向量平行」：$' + ov('AB') + '\\parallel' + ov('AC') + '$。',
      '本題 $' + ov('AB') + '=' + vt(u) + '$、$' + ov('AC') + '=\\left(' + (w === 0 ? ux(A[0]) : String(C[0] - A[0])) + ',\\ ' + (w === 1 ? ux(A[1]) : String(C[1] - A[1])) + '\\right)$，平行 ⟹ 交叉相乘相等：$' + hpz(u[0]) + '\\times ' + v2 + '=' + hpz(u[1]) + '\\times ' + v1 + '$。',
      '把括號展開解一次方程式，得 ' + o.a + '。'];
  };

  /* 1-7 線性組合解係數 */
  L1_SOL.linComb = function (p, o) {
    var a = p.a, b = p.b, c = p.c, d0 = cross(a, b), d1 = cross(c, b), d2 = cross(a, c);
    return ['向量相等就是兩個分量各自相等，所以 $' + vec('c') + '=x' + vec('a') + '+y' + vec('b') + '$ 可以拆成兩條方程式。',
      '本題是 $' + term(a[0], 'x', true) + term(b[0], 'y', false) + '=' + c[0] + '$ 與 $' + term(a[1], 'x', true) + term(b[1], 'y', false) + '=' + c[1] + '$。',
      '用消去法或克拉瑪：$x=\\dfrac{\\det(\\vec c,\\vec b)}{\\det(\\vec a,\\vec b)}=\\dfrac{' + d1 + '}{' + d0 + '}=' + p.ans[0] + '$、$y=\\dfrac{\\det(\\vec a,\\vec c)}{\\det(\\vec a,\\vec b)}=\\dfrac{' + d2 + '}{' + d0 + '}=' + p.ans[1] + '$。答案：' + o.a + '。'];
  };

  /* 1-8 線段上的點：係數判準 */
  L1_SOL.segCoef = function (p, o) {
    var m = p.m, n = p.n, x = fF(p.ans[0]), y = fF(p.ans[1]);
    var yT = y.n < 0 ? parT(Fr.tex(y)) : Fr.tex(y);
    var s1 = p.ext ? '$P$ 在線段外，但 $' + ov('AP') + '$ 仍與 $' + ov('AB') + '$ 在同一條直線上：由 $\\overline{AP}:\\overline{PB}=' + m + ':' + n + '$ 得 $' + ov('AP') + '=\\dfrac{' + m + '}{' + m + '-' + n + '}' + ov('AB') + '=' + combD(y, ov('AB'), true) + '$（係數' + (m > n ? '大於 $1$' : '為負') + '，這正是「在延長線上」的意思）。'
                   : '先把 $' + ov('AP') + '$ 寫成 $' + ov('AB') + '$ 的倍數：$\\overline{AP}:\\overline{PB}=' + m + ':' + n + '$ ⟹ $' + ov('AP') + '=\\dfrac{' + m + '}{' + (m + n) + '}' + ov('AB') + '$。';
    return [s1,
      '換成以 $O$ 為起點：$' + ov('OP') + '=' + ov('OA') + '+' + ov('AP') + '=' + ov('OA') + combD(y, '\\left(' + ov('OB') + '-' + ov('OA') + '\\right)', false) + '$。',
      '合併同類項：$' + ov('OP') + '=\\left(1-' + yT + '\\right)' + ov('OA') + combD(y, ov('OB'), false) + '=' + combD(x, ov('OA'), true) + combD(y, ov('OB'), false) + '$，所以 $x=' + Fr.tex(x) + '$、$y=' + Fr.tex(y) + '$（兩者相加為 $1$）。答案：' + o.a + '。'];
  };

  /* 1-9 係數與位置 */
  L1_SOL.coefRegion = function (p, o) {
    var x = fF(p.x), y = fF(p.y), s = Fr.add(x, y);
    return ['判準只看兩件事：兩個係數是不是都大於 $0$，以及它們的和跟 $1$ 比大小——和小於 $1$ 在三角形內部、等於 $1$ 在 $\\overline{BC}$ 上、大於 $1$ 在 $\\overline{BC}$ 外側（仍在張角內）；只要有一個係數不是正的，就落在張角外。',
      '本題 $x=' + Fr.tex(x) + '$、$y=' + Fr.tex(y) + '$，$x+y=' + Fr.tex(x) + (y.n < 0 ? '' : '+') + Fr.tex(y) + '=' + Fr.tex(s) + '$。',
      (p.ans.inside ? '兩個係數都是正的而且和小於 $1$，所以 $P$ 在三角形內部；面積比 $\\triangle PBC:\\triangle PCA:\\triangle PAB=(1-x-y):x:y$，因此 $\\dfrac{\\triangle PBC}{\\triangle ABC}=1-' + Fr.tex(s) + '=' + Fr.tex(Fr.sub(F(1), s)) + '$。'
                     : '對照上面的判準就能定位（和等於 $1$ 在邊上、大於 $1$ 在外側、有非正係數則在張角外），本題不在內部時不必算面積比。') + '答案：' + o.a + '。'];
  };

  /* 1-10 砝碼：面積比 */
  L1_SOL.weightArea = function (p, o) {
    var a = p.a, b = p.b, c = p.c, g = gcd(gcd(a, b), c);
    return ['$' + comb(a, ov('PA'), true) + comb(b, ov('PB'), false) + comb(c, ov('PC'), false) + '=\\vec0$ 可以看成：$A$、$B$、$C$ 三點各掛上 $' + a + '$、$' + b + '$、$' + c + '$ 的砝碼，而 $P$ 正好是平衡點。',
      '平衡點的性質：某個頂點的砝碼越重，$P$ 就越靠近它，它對面的小三角形也就越大——所以 $\\triangle PBC:\\triangle PCA:\\triangle PAB=' + a + ':' + b + ':' + c + '$，約成最簡整數比是 $' + (a / g) + ':' + (b / g) + ':' + (c / g) + '$。',
      '三塊小三角形合起來就是整個 $\\triangle ABC$，所以 $\\dfrac{\\triangle PBC}{\\triangle ABC}=\\dfrac{' + a + '}{' + a + '+' + b + '+' + c + '}=' + Fr.tex(F(a, a + b + c)) + '$。答案：' + o.a + '。'];
  };

  /* 1-11 坐標內積與夾角 */
  L1_SOL.dotCoord = function (p, o) {
    var a = p.a, b = p.b, d = p.ans.dot, deg = p.ans.deg;
    return ['坐標內積就是「對應分量相乘再相加」：$' + vec('a') + '\\cdot' + vec('b') + '=' + hdot(a, b) + '=' + d + '$。',
      '兩個長度：$|' + vec('a') + '|=' + hsq(a) + '=' + sqrtTex(n2(a)) + '$、$|' + vec('b') + '|=' + hsq(b) + '=' + sqrtTex(n2(b)) + '$。',
      '代進夾角公式：$\\cos\\theta=\\dfrac{' + d + '}{' + sqrtTex(n2(a)) + '\\times ' + sqrtTex(n2(b)) + '}=' + COSD(deg) + '$，查特殊角得 $\\theta=' + deg + '^\\circ$。答案：' + o.a + '。'];
  };

  /* 1-12 長度夾角求內積 */
  L1_SOL.dotLenAngle = function (p, o) {
    var la = p.la, lb = p.lb, k1 = p.k1, k2 = p.k2, dF = fF(p.ans.dot), L2v = fF(p.ans.len2);
    return ['(1) 內積的定義式：$' + vec('a') + '\\cdot' + vec('b') + '=|' + vec('a') + '||' + vec('b') + '|\\cos\\theta=' + la + '\\times ' + lb + '\\times ' + parT(COSD(p.deg)) + '=' + Fr.tex(dF) + '$。',
      '(2) 長度不要直接算，先平方展開：$\\left|' + comb(k1, vec('a'), true) + comb(k2, vec('b'), false) + '\\right|^{2}=' + comb(k1 * k1, '|' + vec('a') + '|^{2}', true) + comb(2 * k1 * k2, '\\,' + vec('a') + '\\cdot' + vec('b'), false) + comb(k2 * k2, '|' + vec('b') + '|^{2}', false) + '$。',
      '把 $|' + vec('a') + '|=' + la + '$、$|' + vec('b') + '|=' + lb + '$ 與 (1) 的內積代進去：$=' + (k1 * k1) + '\\times ' + (la * la) + sgT(2 * k1 * k2) + '\\times ' + parT(Fr.tex(dF)) + '+' + (k2 * k2) + '\\times ' + (lb * lb) + '=' + Fr.tex(L2v) + '$，開根號得 $' + (L2v.d === 1 ? sqrtTex(L2v.n) : '\\sqrt{' + Fr.tex(L2v) + '}') + '$。答案：' + o.a + '。'];
  };

  /* 1-13 垂直條件 */
  L1_SOL.perpCond = function (p, o) {
    var b = p.b, kn = p.known, w = p.which;
    var av = w === 0 ? '(x,' + kn + ')' : '(' + kn + ',x)';
    var lhs = w === 0 ? 'x\\times ' + hpz(b[0]) + '+' + hpz(kn) + '\\times ' + hpz(b[1])
                      : hpz(kn) + '\\times ' + hpz(b[0]) + '+x\\times ' + hpz(b[1]);
    var cx = w === 0 ? b[0] : b[1], cc = w === 0 ? kn * b[1] : kn * b[0];
    return ['兩個向量垂直 ⟺ 內積為 $0$：$a_1b_1+a_2b_2=0$。',
      '本題 $' + vec('a') + '=' + av + '$、$' + vec('b') + '=' + vt(b) + '$，代進去得 $' + lhs + '=0$，即 $' + term(cx, 'x', true) + term(cc, '', false) + '=0$。',
      '解這個一次方程式：$x=' + Fr.tex(F(-cc, cx)) + '$。答案：' + o.a + '。'];
  };

  /* 1-14 正射影 */
  L1_SOL.projVec = function (p, o) {
    var a = p.a, b = p.b, d = dot(a, b), nb = n2(b), pr = p.ans.proj;
    return ['正射影向量的公式是 $\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|^{2}}\\vec b$——分母是 $|\\vec b|$ 的平方，不是 $|\\vec b|$。',
      '本題 $' + vec('a') + '\\cdot' + vec('b') + '=' + hdot(a, b) + '=' + d + '$、$|' + vec('b') + '|^{2}=' + (b[0] * b[0]) + '+' + (b[1] * b[1]) + '=' + nb + '$，所以正射影 $=\\dfrac{' + d + '}{' + nb + '}' + vt(b) + '=' + vt(pr) + '$。',
      '正射影長就是這個向量的長度：$\\sqrt{' + (pr[0] * pr[0]) + '+' + (pr[1] * pr[1]) + '}=' + sqrtTex(p.ans.len2) + '$（也等於 $\\dfrac{|\\vec a\\cdot\\vec b|}{|\\vec b|}$）。答案：' + o.a + '。'];
  };

  /* 1-15 由內積求夾角 */
  L1_SOL.angleFromDot = function (p, o) {
    var dtex = radTex(p.dotNum, p.dotRad, p.dotDen), c = cosR(p.ans);
    return ['夾角公式反過來用：$\\cos\\theta=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec a||\\vec b|}$。',
      '代入本題：$\\cos\\theta=' + parT(dtex) + '\\div' + parT(p.la + '\\times ' + p.lb) + '=' + radTex(c[0], c[1], c[2]) + '$。',
      '查特殊角表（' + (c[0] < 0 ? '負值 ⟹ 鈍角' : (c[0] === 0 ? '$0$ ⟹ 直角' : '正值 ⟹ 銳角')) + '）：對應的夾角是 ' + o.a + '。'];
  };

  /* 1-16 三角形面積 */
  L1_SOL.areaDet = function (p, o) {
    var u = sub(p.B, p.A), v = sub(p.C, p.A), d = cross(u, v);
    return ['先把三角形搬到「同一個頂點出發的兩個向量」：$' + ov('AB') + '=' + vt(u) + '$、$' + ov('AC') + '=' + vt(v) + '$。',
      '算行列式：$a_1b_2-a_2b_1=' + hpz(u[0]) + '\\times ' + hpz(v[1]) + '-' + hpz(u[1]) + '\\times ' + hpz(v[0]) + '=' + d + '$，取絕對值得 $' + Math.abs(d) + '$。',
      '三角形是平行四邊形的一半：面積 $=\\dfrac12\\times ' + Math.abs(d) + '=' + Fr.tex(F(p.ans[0], p.ans[1])) + '$。答案：' + o.a + '。'];
  };

  /* 1-17 平行四邊形面積 */
  L1_SOL.paraArea = function (p, o) {
    var a = p.a, b = p.b, u = add(sc(p.p, a), sc(p.q, b)), v = add(sc(p.s, a), sc(p.t, b)), k = Math.abs(p.p * p.t - p.q * p.s);
    return ['(1) 兩個向量所張平行四邊形的面積就是行列式的絕對值：$\\left|' + a[0] + '\\times ' + hpz(b[1]) + '-' + hpz(a[1]) + '\\times ' + hpz(b[0]) + '\\right|=' + p.ans[0] + '$。',
      '(2) 換成線性組合時，面積會乘上係數行列式的絕對值：$\\left|\\begin{smallmatrix}' + p.p + '&' + p.q + '\\\\' + p.s + '&' + p.t + '\\end{smallmatrix}\\right|=' + p.p + '\\times ' + hpz(p.t) + '-' + hpz(p.q) + '\\times ' + hpz(p.s) + '=' + (p.p * p.t - p.q * p.s) + '$，絕對值是 $' + k + '$。',
      '所以新的面積 $=' + k + '\\times ' + p.ans[0] + '=' + p.ans[1] + '$（直接把 $' + vt(u) + '$ 與 $' + vt(v) + '$ 代行列式也會得到同一個數）。答案：' + o.a + '。'];
  };

  /* 1-18 三邊長求內積 */
  L1_SOL.triDot = function (p, o) {
    var c = p.c, b = p.b, a = p.a, d = F(b * b + c * c - a * a, 2);
    return ['把第三邊寫成兩個向量的差：$' + ov('BC') + '=' + ov('AC') + '-' + ov('AB') + '$，兩邊平方得 $\\overline{BC}^{2}=\\overline{AB}^{2}+\\overline{AC}^{2}-2' + ov('AB') + '\\cdot' + ov('AC') + '$，移項就是 $' + ov('AB') + '\\cdot' + ov('AC') + '=\\dfrac{\\overline{AB}^{2}+\\overline{AC}^{2}-\\overline{BC}^{2}}{2}$。',
      '代入本題：$=\\dfrac{' + c + '^{2}+' + b + '^{2}-' + a + '^{2}}{2}=\\dfrac{' + (b * b + c * c - a * a) + '}{2}=' + Fr.tex(d) + '$。',
      (p.M ? '$M$ 是 $\\overline{CA}$ 的中點 ⟹ $' + ov('AM') + '=\\dfrac12' + ov('AC') + '$，所以 $' + ov('AB') + '\\cdot' + ov('AM') + '=\\dfrac12\\times ' + Fr.tex(d) + '=' + Fr.tex(Fr.div(d, F(2))) + '$。' : '題目問的就是 $' + ov('AB') + '\\cdot' + ov('AC') + '$，不必再換。') + '答案：' + o.a + '。'];
  };

  /* 1-19 柯西不等式 */
  L1_SOL.cauchyCircle = function (p, o) {
    return ['把 $' + term(p.p, 'x', true) + term(p.q, 'y', false) + '$ 看成 $(' + p.p + ',' + p.q + ')\\cdot(x,y)$，用柯西：$(px+qy)^{2}\\le(p^{2}+q^{2})(x^{2}+y^{2})$。',
      '代入本題：$\\left(' + term(p.p, 'x', true) + term(p.q, 'y', false) + '\\right)^{2}\\le\\left(' + (p.p * p.p) + '+' + (p.q * p.q) + '\\right)\\times ' + p.R2 + '=' + p.ans + '$。',
      '所以 $' + term(p.p, 'x', true) + term(p.q, 'y', false) + '\\le\\sqrt{' + p.ans + '}=' + sqrtTex(p.ans) + '$；等號在 $(x,y)$ 與 $(' + p.p + ',' + p.q + ')$ 同向時成立，所以最大值取得到。答案：' + o.a + '。'];
  };

  /* 1-20 |ta+b| 的最小值 */
  L1_SOL.minLen = function (p, o) {
    var a = p.a, b = p.b, na = n2(a), ab = dot(a, b), nb = n2(b), t0 = p.ans.t, m2 = p.ans.min2;
    return ['長度不好直接處理，先平方：$|t' + vec('a') + '+' + vec('b') + '|^{2}=t^{2}|' + vec('a') + '|^{2}+2t\\,' + vec('a') + '\\cdot' + vec('b') + '+|' + vec('b') + '|^{2}$。',
      '把 $|' + vec('a') + '|^{2}=' + na + '$、$' + vec('a') + '\\cdot' + vec('b') + '=' + ab + '$、$|' + vec('b') + '|^{2}=' + nb + '$ 代進去：$=' + term(na, 't^{2}', true) + term(2 * ab, 't', false) + term(nb, '', false) + '$。',
      '配方：$=' + na + '\\left(t' + (t0 < 0 ? '+' + (-t0) : '-' + t0) + '\\right)^{2}+' + m2 + '$，在 $t=' + t0 + '$ 時最小，最小的平方是 $' + m2 + '$，開根號得 $' + sqrtTex(m2) + '$。答案：' + o.a + '。'];
  };
  var META_L1 = [
      ['vecOps', '§1 坐標運算與長度'], ['chain', '§1 首尾相接化簡'], ['divPoint', '§1 分點坐標'], ['centroid', '§1 重心與面積'],
      ['parallelCond', '§2 平行條件'], ['collinear', '§2 三點共線'], ['linComb', '§2 線性組合解係數'], ['segCoef', '§2 線段上的點：係數判準'], ['coefRegion', '§2 係數與位置'], ['weightArea', '§2 砝碼：面積比'],
      ['dotCoord', '§3 坐標內積與夾角'], ['dotLenAngle', '§3 長度夾角求內積'], ['perpCond', '§3 垂直條件'], ['projVec', '§3 正射影'], ['angleFromDot', '§3 由內積求夾角'],
      ['areaDet', '§3 三角形面積'], ['paraArea', '§3 平行四邊形面積'], ['triDot', '§3 三邊長求內積'], ['cauchyCircle', '§3 柯西不等式'], ['minLen', '§3 |ta+b| 的最小值']
  ];
  var META_L2 = [
      ['paraIntersect', '§2 平行四邊形內的交點'], ['coefArea', '§2 係數與三個小三角形'], ['lineThroughPoint', '§2 過定點直線的截距恆等式'], ['regionArea', '§2 向量區域的面積'],
      ['cosFromLen', '§3 由長度關係求 cosθ'], ['projLen', '§3 由長度求正射影長'], ['cauchyEllipse', '§3 柯西：橢圓型'], ['detScale', '§3 行列式伸縮率'], ['circleDot', '§3 圓上動點的內積'],
      ['dotParabola', '§3 拋物線上的內積最小'], ['orthocenter', '§3 外心→重心與垂心'], ['sumRange', '§3 三向量和的範圍'], ['tripleT', '§3 平行／垂直／最短三連問'], ['bisector', '§2 角平分線分解'], ['walk', '§1 折線行走']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     坐標全部是整數、係數用 Fraction；p 只放旗標，驗算器一律從題幹重算。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};
  function sgn3(n) { return n < 0 ? '(' + n + ')' : String(n); }
  function rot90(v) { return [-v[1], v[0]]; }
  function quadOf(P) { if (P[0] === 0 || P[1] === 0) return 0; return P[0] > 0 ? (P[1] > 0 ? 1 : 4) : (P[1] > 0 ? 2 : 3); }
  var QN = ['', '一', '二', '三', '四'];
  function ratioTxt(s1, s2, m, n) { return m === n ? T('\\overline{' + s1 + '}=\\overline{' + s2 + '}') : T('\\overline{' + s1 + '}:\\overline{' + s2 + '}=' + m + ':' + n); }
  function coprimePair(r, hi) { var m, n; do { m = r.int(1, hi); n = r.int(1, hi); } while (gcd(m, n) !== 1); return [m, n]; }

  /* L3-1　三個分點：全部用 AB、AC 表示，再相加 */
  L3.threeDivPts = function (r) {
    var q = coprimePair(r, 4), p = coprimePair(r, 4), rr = coprimePair(r, 3), v = r.int(0, 2);
    var x = F(q[0], q[0] + q[1]), y = F(p[0], p[0] + p[1]), z = F(rr[0], rr[0] + rr[1]), one = F(1), two = F(2), m, n, lhs;
    if (v === 0) { m = Fr.add(x, Fr.sub(one, z)); n = Fr.sub(z, Fr.mul(two, y)); lhs = ov('PQ') + '+' + ov('PR'); }
    else if (v === 1) { m = Fr.sub(Fr.sub(one, z), Fr.mul(two, x)); n = Fr.add(y, z); lhs = ov('QP') + '+' + ov('QR'); }
    else { m = Fr.sub(x, Fr.mul(two, Fr.sub(one, z))); n = Fr.sub(y, Fr.mul(two, z)); lhs = ov('RP') + '+' + ov('RQ'); }
    return { q: T('\\triangle ABC') + ' 中，' + T('Q,P,R') + ' 分別在 ' + T('\\overline{AB},\\overline{AC},\\overline{BC}') + ' 上，' + ratioTxt('AQ', 'QB', q[0], q[1]) + '、' + ratioTxt('AP', 'PC', p[0], p[1]) + '、' + ratioTxt('BR', 'RC', rr[0], rr[1]) + '。若 ' + T(lhs + '=m' + ov('AB') + '+n' + ov('AC')) + '，求 ' + T('(m,n)') + '。',
      a: T('(m,n)=' + vtF([m, n])),
      h: '三個分點全部改用 $' + ov('AB') + '$、$' + ov('AC') + '$ 表示：$' + ov('AQ') + '=' + Fr.tex(x, true) + ov('AB') + '$、$' + ov('AP') + '=' + Fr.tex(y, true) + ov('AC') + '$、$' + ov('AR') + '=' + Fr.tex(Fr.sub(one, z), true) + ov('AB') + '+' + Fr.tex(z, true) + ov('AC') + '$（分點公式，係數交叉）。再用「終點減起點」：例如 $' + ov('PQ') + '=' + ov('AQ') + '-' + ov('AP') + '$。',
      p: { q: q, pr: p, r: rr, v: v, ans: [fr2(m), fr2(n)] } };
  };

  /* L3-2　等腰直角三角形求第三頂點：把向量旋轉 90° */
  L3.isoRightVertex = function (r) {
    var v = r.int(0, 1), A, B, C1, C2, tries = 0, M, h;
    do {
      A = [r.int(-5, 6), r.int(-5, 6)];
      if (v === 0) { h = [r.nz(-4, 4), r.nz(-4, 4)]; B = add(A, sc(2, h)); M = add(A, h); C1 = add(M, rot90(h)); C2 = sub(M, rot90(h)); }
      else { h = [r.nz(-5, 5), r.nz(-5, 5)]; B = add(A, h); C1 = add(A, rot90(h)); C2 = sub(A, rot90(h)); }
    } while ((quadOf(C1) === 0 || quadOf(C2) === 0 || quadOf(C1) === quadOf(C2)) && tries++ < 500);
    var C = r.int(0, 1) ? C1 : C2;
    var cond = v === 0 ? T('\\overline{AC}=\\overline{BC}') + '、' + T('\\angle ACB=90^\\circ') : T('\\overline{AB}=\\overline{AC}') + '、' + T('\\angle BAC=90^\\circ');
    return { q: T('\\triangle ABC') + ' 為等腰直角三角形，' + cond + '，' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + ' 且 ' + T('C') + ' 在第' + QN[quadOf(C)] + '象限。求 ' + T('C') + ' 的坐標。',
      a: T('C' + vt(C)),
      h: v === 0 ? '設 $M$ 為 $\\overline{AB}$ 中點 $' + vt(M) + '$：直角在 $C$ 的等腰直角三角形，$' + ov('MC') + '\\perp' + ov('MA') + '$ 而且一樣長。把 $' + ov('MB') + '=' + vt(h) + '$ 旋轉 $90^\\circ$：$(x,y)\\to(-y,x)$ 或 $(y,-x)$，兩個候選再用象限挑。'
        : '直角在 $A$：$' + ov('AC') + '\\perp' + ov('AB') + '$ 而且一樣長。把 $' + ov('AB') + '=' + vt(h) + '$ 旋轉 $90^\\circ$：$(x,y)\\to(-y,x)$ 或 $(y,-x)$，接到 $A$ 上得兩個候選，再用象限挑。',
      p: { A: A, B: B, v: v, quad: quadOf(C), ans: C } };
  };

  /* L3-3　兩個括號相乘、各含 a,b 與其倒數：柯西不等式 */
  L3.cauchyProduct = function (r) {
    var m = r.int(1, 3), n = r.int(1, 3), u = r.pick([1, 2, 3]), w = r.int(1, 3); while (m === 1 && u === 1) u = r.pick([2, 3]);
    var t1 = (m === 1 ? '' : m * m) + 'a', t2 = u === 1 ? 'b' : '\\dfrac{b}{' + u * u + '}', t3 = '\\dfrac{' + w * w + '}{b}', t4 = '\\dfrac{' + n * n + '}{a}';
    var val = Fr.add(F(m * n), F(w, u)), ans = Fr.mul(val, val);
    return { q: '設 ' + T('a\\gt 0') + '、' + T('b\\gt 0') + '，求 ' + T('\\left(' + t1 + '+' + t2 + '\\right)\\left(' + t3 + '+' + t4 + '\\right)') + ' 的最小值。', a: T(Fr.tex(ans)),
      h: '柯西不等式 $(x_1^2+x_2^2)(y_1^2+y_2^2)\\ge(x_1y_1+x_2y_2)^2$：把含 $a$ 的兩項配成一對、含 $b$ 的兩項配成一對，讓 $a$、$b$ 相乘後消掉——$' + t1 + '\\cdot' + t4 + '=' + m * m * n * n + '$、$' + t2 + '\\cdot' + t3 + '=' + Fr.tex(F(w * w, u * u), true) + '$，各開根號再相加。注意第二個括號裡兩項的順序要對調才對得上。',
      p: { m: m, n: n, u: u, w: w, ans: fr2(ans) } };
  };

  /* L3-4　兩直線的交角：法向量的夾角 */
  L3.lineAngle = function (r) {
    var a, b; do { a = r.int(1, 5); b = r.int(1, 5); } while (a === b || gcd(a, b) !== 1);
    var fam = r.int(0, 1), k = r.pick([1, 1, 2, 3]), s = r.sign(), n1 = [a, b], n2 = fam === 0 ? [k * a * s, -k * b * s] : [k * b * s, k * a * s], ask = r.int(0, 2);
    var N = a * a + b * b, cs = F(Math.abs(dot(n1, n2)), k * N), sn = F(Math.abs(cross(n1, n2)), k * N), tn = Fr.div(sn, cs);
    var c1 = r.pick([2, 3, 5, 7]), c2 = r.pick([2, 3, 5, 6, 7]), ans = [cs, sn, tn][ask], nm = ['\\cos\\theta', '\\sin\\theta', '\\tan\\theta'][ask];
    var L1t = term(n1[0], 'x', true) + term(n1[1], 'y', false) + '=\\sqrt{' + c1 + '}', L2t = term(n2[0], 'x', true) + term(n2[1], 'y', false) + '=\\sqrt{' + c2 + '}';
    return { q: '兩直線 ' + T('L_1:' + L1t) + '、' + T('L_2:' + L2t) + '，' + T('\\theta') + ' 為其交角（銳角），求 ' + T(nm) + '。', a: T(nm + '=' + Fr.tex(ans)),
      h: '交角看法向量：$\\vec n_1=' + vt(n1) + '$、$\\vec n_2=' + vt(n2) + '$，$\\cos\\theta=\\dfrac{|\\vec n_1\\cdot\\vec n_2|}{|\\vec n_1||\\vec n_2|}$（取絕對值才是銳角）。等號右邊的 $\\sqrt{' + c1 + '}$、$\\sqrt{' + c2 + '}$ 只影響直線的位置，跟角度無關。' + (ask === 0 ? '' : '求出 $\\cos\\theta$ 後再用 $\\sin^2\\theta+\\cos^2\\theta=1$。'),
      p: { n1: n1, n2: n2, ask: ask, ans: fr2(ans) } };
  };

  /* L3-5　平行四邊形的第四個頂點與面積 */
  L3.paraFourth = function (r) {
    var A, B, C, D, area, v = r.int(0, 1), tries = 0;
    do { A = [r.int(-9, 9), r.int(-9, 15)]; B = [r.int(-9, 9), r.int(-15, 9)]; C = [r.int(-5, 17), r.int(-9, 9)]; D = sub(add(A, C), B); area = Math.abs(cross(sub(B, A), sub(D, A))); } while ((area < 6 || area > 500) && tries++ < 200);
    var given = v === 0 ? [['A', A], ['B', B], ['C', C]] : [['A', A], ['B', B], ['D', D]], miss = v === 0 ? 'D' : 'C', missP = v === 0 ? D : C;
    return { q: '平行四邊形 ' + T('ABCD') + ' 中 ' + given.map(function (g) { return T(g[0] + vt(g[1])); }).join('、') + '。求 (1) ' + T(miss) + ' 的坐標　(2) 平行四邊形的面積。',
      a: '(1) ' + T(miss + vt(missP)) + '　(2) ' + T(String(area)),
      h: '頂點依 $A\\to B\\to C\\to D$ 的順序：$' + ov('AD') + '=' + ov('BC') + '$ ⟹ ' + (v === 0 ? '$D=A+C-B$' : '$C=B+D-A$') + '（對角線互相平分也得到同一式）。面積 $=\\left|\\det\\big(' + ov('AB') + ',' + ov('AD') + '\\big)\\right|$，先把 $' + ov('AB') + '=' + vt(sub(B, A)) + '$ 算出來。',
      p: { A: A, B: B, v: v, ans: [missP, area] } };
  };

  /* L3-6　同一支 a+tb 問平行、垂直、最短（三個 t 都是整數） */
  L3.tripleTInt = function (r) {
    var a, b, c, t1, t2, tm, tries = 0, ok, m2;
    do {
      b = [r.nz(-3, 3), r.nz(-3, 3)]; c = [r.nz(-5, 5), r.nz(-5, 5)]; a = [r.int(-13, 13), r.int(-13, 13)];
      var cb = cross(b, c), db = dot(b, c); ok = cb !== 0 && db !== 0;
      if (ok) { t1 = -cross(a, c) / cb; t2 = -dot(a, c) / db; tm = -dot(a, b) / n2(b); ok = t1 === Math.round(t1) && t2 === Math.round(t2) && tm === Math.round(tm) && t1 !== t2 && t1 !== tm && t2 !== tm && Math.abs(t1) <= 12 && Math.abs(t2) <= 12; }
      if (ok) { m2 = n2(add(a, sc(tm, b))); ok = m2 > 0; }
    } while (!ok && tries++ < 20000);
    return { q: '設 ' + T(vec('a') + '=' + vt(a)) + '、' + T(vec('b') + '=' + vt(b)) + '、' + T(vec('c') + '=' + vt(c)) + '。求 (1) ' + T('(' + vec('a') + '+t' + vec('b') + ')\\parallel ' + vec('c')) + ' 的 ' + T('t') + '　(2) ' + T('(' + vec('a') + '+t' + vec('b') + ')\\perp ' + vec('c')) + ' 的 ' + T('t') + '　(3) ' + T('\\left|' + vec('a') + '+t' + vec('b') + '\\right|') + ' 最小時的 ' + T('t') + ' 與最小值 ' + T('m') + '。',
      a: '(1) ' + T('t=' + t1) + '　(2) ' + T('t=' + t2) + '　(3) ' + T('t=' + tm) + '、' + T('m=' + sqrtTex(m2)),
      h: '先寫出 $' + vec('a') + '+t' + vec('b') + '=(' + a[0] + term(b[0], 't', false) + ',\\ ' + a[1] + term(b[1], 't', false) + ')$。三問各一條式子：平行 ⟹ 與 $' + vec('c') + '$ 的分量交叉相乘相等；垂直 ⟹ 內積為 $0$；最短 ⟹ 長度平方是 $t$ 的二次式，配方（此時 $' + vec('a') + '+t' + vec('b') + '\\perp ' + vec('b') + '$）。',
      p: { a: a, b: b, c: c, ans: [t1, t2, tm, m2] } };
  };

  /* L3-7　線性組合後的面積：乘上係數行列式的絕對值 */
  L3.detScaleArea = function (r) {
    var p, q, s, t, d; do { p = r.nz(-4, 4); q = r.nz(-3, 3); s = r.nz(-4, 4); t = r.nz(-3, 3); d = Math.abs(p * t - q * s); } while (d < 2);
    var S = r.int(2, 9), tri = r.int(0, 1), ans = F(d * S, tri ? 2 : 1);
    var c1 = comb(p, vec('u'), true) + comb(q, vec('v'), false), c2 = comb(s, vec('u'), true) + comb(t, vec('v'), false);
    return { q: '向量 ' + T(vec('u') + ',' + vec('v')) + ' 所張平行四邊形面積為 ' + T(String(S)) + '，求 ' + T(c1) + ' 與 ' + T(c2) + ' 所張' + (tri ? '<b>三角形</b>' : '平行四邊形') + '面積。', a: T(Fr.tex(ans)),
      h: '$\\det\\big(' + c1 + ',\\ ' + c2 + '\\big)=\\begin{vmatrix}' + p + '&' + q + '\\\\ ' + s + '&' + t + '\\end{vmatrix}\\cdot\\det(' + vec('u') + ',' + vec('v') + ')$：新的平行四邊形面積是原來的「係數行列式的絕對值」倍。' + (tri ? '三角形是平行四邊形的一半，最後別忘了除以 $2$。' : ''),
      p: { M: [p, q, s, t], S: S, tri: tri, ans: fr2(ans) } };
  };

  /* L3-8　直角三角形斜邊上的等分點：建坐標 */
  L3.hypotenusePts = function (r) {
    var v = r.int(0, 3), n = r.pick([3, 4, 5, 6, 7]), i = r.int(1, Math.floor((n - 1) / 2)), j = n - i, nm = ['三', '四', '五', '六', '七'][n - 3];
    if (v < 3) {
      var cs = F(2 * i * j, i * i + j * j), sn = F(Math.abs(j * j - i * i), i * i + j * j), tn = Fr.div(sn, cs), ans = [cs, sn, tn][v], fn = ['\\cos', '\\sin', '\\tan'][v];
      return { q: T('\\triangle ABC') + ' 為等腰直角三角形，' + T('\\angle BAC=90^\\circ') + '。將斜邊 ' + T('\\overline{BC}') + ' ' + nm + '等分，由 ' + T('B') + ' 往 ' + T('C') + ' 數第 ' + T(String(i)) + ' 個與第 ' + T(String(j)) + ' 個等分點分別為 ' + T('P,Q') + '，求 ' + T(fn + '\\angle PAQ') + '。', a: T(Fr.tex(ans)),
        h: '建坐標最快：$A(0,0)$、$B(' + n + ',0)$、$C(0,' + n + ')$，等分點的坐標一眼看出：$P(' + j + ',' + i + ')$、$Q(' + i + ',' + j + ')$。再用 $\\cos\\angle PAQ=\\dfrac{' + ov('AP') + '\\cdot' + ov('AQ') + '}{|' + ov('AP') + '||' + ov('AQ') + '|}$' + (v === 0 ? '。' : '，最後由 $\\cos$ 換成 $' + fn + '$。'),
        p: { v: v, n: n, i: i, j: j, ans: fr2(ans) } };
    }
    var bl = r.int(2, 9), cl = r.int(2, 9), dv = F(i * j * (bl * bl + cl * cl), n * n);
    return { q: '直角 ' + T('\\triangle ABC') + ' 中 ' + T('\\angle BAC=90^\\circ') + '、' + T('\\overline{AB}=' + bl) + '、' + T('\\overline{AC}=' + cl) + '。將斜邊 ' + T('\\overline{BC}') + ' ' + nm + '等分，由 ' + T('B') + ' 往 ' + T('C') + ' 數第 ' + T(String(i)) + ' 個與第 ' + T(String(j)) + ' 個等分點分別為 ' + T('P,Q') + '，求 ' + T(ov('AP') + '\\cdot' + ov('AQ')) + '。', a: T(Fr.tex(dv)),
      h: '建坐標：$A(0,0)$、$B(' + bl + ',0)$、$C(0,' + cl + ')$。由 $B$ 往 $C$ 數第 $k$ 個等分點是 $\\dfrac{(' + n + '-k)B+kC}{' + n + '}$，所以 $P=\\dfrac{' + j + 'B+' + i + 'C}{' + n + '}$、$Q=\\dfrac{' + i + 'B+' + j + 'C}{' + n + '}$，再算坐標內積。',
      p: { v: v, n: n, i: i, j: j, b: bl, c: cl, ans: fr2(dv) } };
  };

  /* L3-9　由平行四邊形面積反推頂點，再求第四點 */
  L3.areaToVertex = function (r) {
    var A, B, C, u, S, yo, tries = 0, D;
    do {
      A = [r.int(-3, 4), r.int(-3, 4)]; u = [r.nz(-6, 7), r.int(-4, 4)]; B = add(A, u); C = [r.int(1, 12), r.int(1, 10)];
      S = Math.abs(cross(u, sub(C, A)));
      /* |ux(y−Ay) − uy(Cx−Ax)| = S 的另一個解 */
      var base = u[1] * (C[0] - A[0]), y1 = A[1] + (base + S) / u[0], y2 = A[1] + (base - S) / u[0]; yo = Math.abs(y1 - C[1]) < 1e-9 ? y2 : y1;
      D = sub(add(A, C), B);
    } while ((S < 6 || S > 90 || yo > 0 || (C[0] === B[0] && C[1] === B[1])) && tries++ < 2000);
    return { q: '平行四邊形 ' + T('ABCD') + ' 中 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，' + T('C') + ' 在第一象限且 ' + T('x') + ' 坐標為 ' + T(String(C[0])) + '。若面積為 ' + T(String(S)) + '，求 ' + T('D') + ' 的坐標。', a: T('D' + vt(D)),
      h: '設 $C(' + C[0] + ',y)$：面積 $=\\left|\\det\\big(' + ov('AB') + ',' + ov('AC') + '\\big)\\right|$，其中 $' + ov('AB') + '=' + vt(u) + '$、$' + ov('AC') + '=(' + (C[0] - A[0]) + ',\\ y' + term(-A[1], '', false) + ')$，得到 $y$ 的一次絕對值方程式（兩個解），用「第一象限」挑一個；最後 $D=A+C-B$。',
      p: { A: A, B: B, cx: C[0], S: S, ans: D } };
  };

  /* L3-10　內積性質判斷（多選）：每個選項舉反例或平方展開 */
  var DOTPOOL = [
    ['若 $' + '\\vec a\\cdot\\vec b=\\vec a\\cdot\\vec c$，則 $\\vec b=\\vec c$', 0], ['$|\\vec a+\\vec b|\\cdot|\\vec a-\\vec b|=|(\\vec a+\\vec b)\\cdot(\\vec a-\\vec b)|$', 0],
    ['若 $|\\vec a||\\vec b|=|\\vec a\\cdot\\vec b|$，則 $\\vec a\\parallel \\vec b$', 1], ['若 $\\vec a\\perp \\vec b$，則 $|\\vec a|^2+|\\vec b|^2=|\\vec a-\\vec b|^2$', 1],
    ['$\\vec a$ 在 $\\vec b$ 上的正射影向量與 $\\vec a$ 在 $-\\vec b$ 上的正射影向量大小相同、方向相反', 0], ['$\\vec a$ 在 $\\vec b$ 上的正射影向量與 $\\vec a$ 在 $-\\vec b$ 上的正射影向量相同', 1],
    ['$|\\vec a\\cdot\\vec b|\\le |\\vec a||\\vec b|$', 1], ['$|\\vec a+\\vec b|^2+|\\vec a-\\vec b|^2=2\\left(|\\vec a|^2+|\\vec b|^2\\right)$', 1],
    ['若 $|\\vec a+\\vec b|=|\\vec a-\\vec b|$，則 $\\vec a\\perp \\vec b$', 1], ['$(\\vec a+\\vec b)\\cdot(\\vec a-\\vec b)=|\\vec a|^2-|\\vec b|^2$', 1],
    ['$(\\vec a\\cdot\\vec b)\\,\\vec c=\\vec a\\,(\\vec b\\cdot\\vec c)$', 0], ['$|\\vec a+\\vec b|=|\\vec a|+|\\vec b|$', 0],
    ['$(\\vec a\\cdot\\vec b)^2=|\\vec a|^2|\\vec b|^2$', 0], ['若 $\\vec a\\cdot\\vec b=0$ 且 $\\vec a\\cdot\\vec c=0$，則 $\\vec b\\parallel \\vec c$', 1],
    ['若 $\\vec a\\cdot\\vec b\\lt 0$，則 $\\vec a,\\vec b$ 的夾角為鈍角或平角', 1], ['$|\\vec a-\\vec b|\\ge |\\vec a|+|\\vec b|$', 0]
  ];
  L3.dotPropsMC = function (r) {
    var pick, nT, tries = 0;
    do { pick = r.shuffle(DOTPOOL.map(function (_, i) { return i; })).slice(0, 5); nT = pick.filter(function (i) { return DOTPOOL[i][1]; }).length; }
    while ((nT < 1 || nT > 4 || (pick.indexOf(4) >= 0 && pick.indexOf(5) >= 0)) && tries++ < 100);
    var ansT = pick.map(function (i, k) { return DOTPOOL[i][1] ? '(' + (k + 1) + ')' : ''; }).join('');
    return { q: T('\\vec a,\\vec b,\\vec c') + ' 為平面上的非零向量，下列哪些正確？（可複選）<br>' + pick.map(function (i, k) { return '(' + (k + 1) + ') ' + DOTPOOL[i][0]; }).join('<br>'),
      a: ansT,
      h: (function () {
        var imp = [], eqs = [], prj = [];
        pick.forEach(function (i, k) { var s = DOTPOOL[i][0], tag = '(' + (k + 1) + ')'; if (s.indexOf('正射影') >= 0) prj.push(tag); else if (s.charAt(0) === '若') imp.push(tag); else eqs.push(tag); });
        return '別靠感覺，分類處理：' + (imp.length ? imp.join('') + ' 是「若…則…」型，先想反例（例如取 $\\vec a=(1,0)$，再挑和它垂直、或內積相同的向量），找不到反例再試著證明；' : '') + (eqs.length ? eqs.join('') + ' 是等式／不等式型，把長度<b>平方</b>後用 $|\\vec x|^2=\\vec x\\cdot\\vec x$ 展開，或用 $\\vec a\\cdot\\vec b=|\\vec a||\\vec b|\\cos\\theta$、$|\\cos\\theta|\\le 1$ 判斷；' : '') + (prj.length ? prj.join('') + ' 直接代正射影公式 $\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|^2}\\vec b$，把 $\\vec b$ 換成 $-\\vec b$ 看式子變不變；' : '') + '每個選項都要有理由。';
      })(),
      p: { pick: pick, ans: pick.map(function (i) { return DOTPOOL[i][1]; }) } };
  };

  /* L3-11　只給長度與夾角求 |PQ|：PQ=OQ−OP 寫成 a、b 的組合再平方 */
  L3.lenFromAngle = function (r) {
    var la = r.int(1, 5), lb = r.int(1, 5), deg = r.pick([60, 120, 90, 60, 120]), p, q, s, t, k1, k2, tries = 0;
    do { p = r.nz(-3, 3); q = r.nz(-3, 3); s = r.nz(-3, 3); t = r.nz(-3, 3); k1 = s - p; k2 = t - q; } while ((k1 === 0 || k2 === 0) && tries++ < 100);
    var tw = deg === 60 ? 1 : deg === 120 ? -1 : 0, len2 = k1 * k1 * la * la + k2 * k2 * lb * lb + k1 * k2 * la * lb * tw;
    return { q: '設 ' + T('|' + vec('a') + '|=' + la) + '、' + T('|' + vec('b') + '|=' + lb) + '，兩向量的夾角為 ' + T(deg + '^\\circ') + '。若 ' + T(ov('OP') + '=' + comb(p, vec('a'), true) + comb(q, vec('b'), false)) + '、' + T(ov('OQ') + '=' + comb(s, vec('a'), true) + comb(t, vec('b'), false)) + '，求 ' + T('|' + ov('PQ') + '|') + '。',
      a: T(sqrtTex(len2)),
      h: '$' + ov('PQ') + '=' + ov('OQ') + '-' + ov('OP') + '=' + comb(k1, vec('a'), true) + comb(k2, vec('b'), false) + '$。沒有坐標就用平方展開：$|k_1' + vec('a') + '+k_2' + vec('b') + '|^2=k_1^2|' + vec('a') + '|^2+2k_1k_2(' + vec('a') + '\\cdot ' + vec('b') + ')+k_2^2|' + vec('b') + '|^2$，其中 $' + vec('a') + '\\cdot ' + vec('b') + '=' + la + '\\cdot' + lb + '\\cdot\\cos' + deg + '^\\circ$。',
      p: { la: la, lb: lb, deg: deg, P: [p, q], Q: [s, t], ans: len2 } };
  };

  /* L3-12／L3-15　AD ⊥ BC（或 ∥ BC）且 |AD| 已知，求 D（兩解） */
  var PYV = [[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [6, 8, 10], [8, 6, 10], [8, 15, 17], [15, 8, 17]];
  function adPoint(r, perp) {
    var pv = r.pick(PYV), bc = [pv[0] * r.sign(), pv[1] * r.sign()], k = r.int(1, 3), L = k * pv[2], g = gcd(pv[0], pv[1]), unit = [bc[0] / g, bc[1] / g], ulen = pv[2] / g;
    var A = [r.int(-5, 6), r.int(-5, 6)], B = [r.int(-6, 6), r.int(-6, 6)], C = add(B, bc), dir = perp ? rot90(unit) : unit, step = sc(L / ulen, dir), D1 = add(A, step), D2 = sub(A, step);
    var rel = perp ? '\\perp ' : '\\parallel ';
    return { q: '已知 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '、' + T('C' + vt(C)) + '。若 ' + T(ov('AD') + rel + ov('BC')) + ' 且 ' + T('|' + ov('AD') + '|=' + L) + '，求 ' + T('D') + ' 的坐標。',
      a: T('D' + vt(D1)) + ' 或 ' + T(vt(D2)),
      h: '$' + ov('BC') + '=' + vt(bc) + '$，長度 $' + pv[2] + '$。' + (perp ? '先取它的垂直方向：$(x,y)\\to(-y,x)$，得 $' + vt(rot90(bc)) + '$（長度一樣是 $' + pv[2] + '$）；' : '') + '再把長度縮放成 $' + L + '$——要乘 $\\pm\\dfrac{' + L + '}{' + pv[2] + '}$，<b>正負各一解</b>，最後接到 $A$ 上。',
      p: { A: A, B: B, C: C, L: L, perp: perp ? 1 : 0, ans: [D1, D2] } };
  }
  L3.perpPoint = function (r) { return adPoint(r, true); };
  L3.paraPoint = function (r) { return adPoint(r, false); };

  /* L3-13　三力平衡：c=−(a+b) */
  L3.forceBalance = function (r) {
    var la = r.int(1, 6), lb = r.int(1, 6), deg = r.pick([60, 120, 90, 60, 120]), tw = deg === 60 ? 1 : deg === 120 ? -1 : 0, c2 = la * la + lb * lb + la * lb * tw, v = r.int(0, 1);
    if (v === 0) return { q: T(vec('a') + ',' + vec('b') + ',' + vec('c')) + ' 三力同時作用於 ' + T('P') + ' 點而達到平衡。已知 ' + T('|' + vec('a') + '|=' + la) + '、' + T('|' + vec('b') + '|=' + lb) + '，' + T(vec('a')) + ' 與 ' + T(vec('b')) + ' 的夾角為 ' + T(deg + '^\\circ') + '，求 ' + T('|' + vec('c') + '|') + '。', a: T(sqrtTex(c2)),
      h: '平衡 ⟹ $' + vec('a') + '+' + vec('b') + '+' + vec('c') + '=\\vec 0$ ⟹ $' + vec('c') + '=-(' + vec('a') + '+' + vec('b') + ')$，所以 $|' + vec('c') + '|=|' + vec('a') + '+' + vec('b') + '|$。平方展開：$' + la + '^2+' + lb + '^2+2\\cdot' + la + '\\cdot' + lb + '\\cdot\\cos' + deg + '^\\circ$。', p: { la: la, lb: lb, deg: deg, v: v, ans: c2 } };
    return { q: T(vec('a') + ',' + vec('b') + ',' + vec('c')) + ' 三力同時作用於 ' + T('P') + ' 點而達到平衡。已知 ' + T('|' + vec('a') + '|=' + la) + '、' + T('|' + vec('b') + '|=' + lb) + '、' + T('|' + vec('c') + '|=' + sqrtTex(c2)) + '，求 ' + T(vec('a')) + ' 與 ' + T(vec('b')) + ' 的夾角。', a: T(deg + '^\\circ'),
      h: '平衡 ⟹ $' + vec('c') + '=-(' + vec('a') + '+' + vec('b') + ')$，所以 $|' + vec('a') + '+' + vec('b') + '|^2=|' + vec('c') + '|^2=' + c2 + '$。左邊展開成 $' + la + '^2+' + lb + '^2+2(' + vec('a') + '\\cdot ' + vec('b') + ')$，先解出 $' + vec('a') + '\\cdot ' + vec('b') + '$，再用 $\\cos\\theta=\\dfrac{' + vec('a') + '\\cdot ' + vec('b') + '}{|' + vec('a') + '||' + vec('b') + '|}$。', p: { la: la, lb: lb, deg: deg, v: v, ans: deg } };
  };

  /* L3-14　向量在「直線」上的正射影：取直線的方向向量 */
  L3.projOnLine = function (r) {
    var a, b; do { a = r.nz(-4, 4); b = r.nz(-4, 4); } while (gcd(a, b) !== 1);
    if (a < 0) { a = -a; b = -b; }
    var c = r.int(-9, 9), A = [r.int(-5, 5), r.int(-5, 5)], B, d = [b, -a], ab, dp, v = r.int(0, 1), tries = 0;
    do { B = [r.int(-6, 6), r.int(-6, 6)]; ab = sub(B, A); dp = dot(ab, d); } while ((dp === 0 || cross(ab, d) === 0) && tries++ < 100);
    var N = n2(d), proj = [F(dp * d[0], N), F(dp * d[1], N)], line = term(a, 'x', true) + term(b, 'y', false) + '=' + c;
    return { q: '已知 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，求 ' + T(ov('AB')) + ' 在直線 ' + T(line) + ' 上的正射影' + (v === 0 ? '（向量）' : '長') + '。',
      a: v === 0 ? T(vtF(proj)) : T(rootTexF(F(dp * dp, N))),
      h: '對「直線」作正射影，要用直線的<b>方向向量</b>：法向量是 $(' + a + ',' + b + ')$，轉 $90^\\circ$ 得方向向量 $\\vec d=' + vt(d) + '$。$' + ov('AB') + '=' + vt(ab) + '$，正射影 $=\\dfrac{' + ov('AB') + '\\cdot\\vec d}{|\\vec d|^2}\\,\\vec d$；直線的常數項 $' + c + '$ 不影響方向。',
      p: { A: A, B: B, line: [a, b, c], v: v, ans: v === 0 ? [fr2(proj[0]), fr2(proj[1])] : [dp * dp, N] } };
  };

  var META_L3 = [['threeDivPts', '三個分點用 AB、AC 表示'], ['isoRightVertex', '等腰直角三角形求頂點'], ['cauchyProduct', '兩括號相乘的柯西'], ['lineAngle', '兩直線的交角'], ['paraFourth', '平行四邊形第四點與面積'], ['tripleTInt', 'a+tb 的平行、垂直、最短'], ['detScaleArea', '線性組合後的面積倍率'], ['hypotenusePts', '斜邊等分點（建坐標）'], ['areaToVertex', '由面積反推頂點'], ['dotPropsMC', '內積性質判斷（多選）'], ['lenFromAngle', '由長度與夾角求 |PQ|'], ['perpPoint', 'AD⊥BC 且長度已知求 D'], ['forceBalance', '三力平衡'], ['projOnLine', '向量在直線上的正射影'], ['paraPoint', 'AD∥BC 且長度已知求 D']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'threeDivPts', 'L3-2': 'isoRightVertex', 'L3-3': 'cauchyProduct', 'L3-4': 'lineAngle', 'L3-5': 'paraFourth', 'L3-6': 'tripleTInt', 'L3-7': 'detScaleArea', 'L3-8': 'hypotenusePts', 'L3-9': 'areaToVertex', 'L3-10': 'dotPropsMC', 'L3-11': 'lenFromAngle', 'L3-12': 'perpPoint', 'L3-13': 'forceBalance', 'L3-14': 'projOnLine', 'L3-15': 'paraPoint' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：兩點距離與中點（高一上 ch2）、特殊角的 sin／cos、餘弦定理（高一下 ch4）、二元一次聯立（國中）、配方求最小值（高一上 ch3）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  L0.distMid = function (r) {
    var A = [r.int(-6, 6), r.int(-6, 6)], B; do { B = [r.int(-6, 6), r.int(-6, 6)]; } while (B[0] === A[0] || B[1] === A[1]);
    var d2v = n2(sub(B, A)), M = [F(A[0] + B[0], 2), F(A[1] + B[1], 2)];
    return { q: '已知 ' + T('A' + vt(A)) + '、' + T('B' + vt(B)) + '，求 (1) ' + T('\\overline{AB}') + '　(2) ' + T('\\overline{AB}') + ' 的中點坐標。', a: '(1) ' + T(sqrtTex(d2v)) + '　(2) ' + T(vtF(M)),
      h: '距離公式 $\\overline{AB}=\\sqrt{(' + sgn3(B[0]) + '-' + sgn3(A[0]) + ')^2+(' + sgn3(B[1]) + '-' + sgn3(A[1]) + ')^2}$，根號要化簡；中點是兩個坐標各取平均。本章「向量的長度」就是這條距離公式。',
      p: { A: A, B: B } };
  };
  var TRIG = { 30: ['\\dfrac{1}{2}', '\\dfrac{\\sqrt{3}}{2}'], 45: ['\\dfrac{\\sqrt{2}}{2}', '\\dfrac{\\sqrt{2}}{2}'], 60: ['\\dfrac{\\sqrt{3}}{2}', '\\dfrac{1}{2}'], 90: ['1', '0'], 120: ['\\dfrac{\\sqrt{3}}{2}', '-\\dfrac{1}{2}'], 135: ['\\dfrac{\\sqrt{2}}{2}', '-\\dfrac{\\sqrt{2}}{2}'], 150: ['\\dfrac{1}{2}', '-\\dfrac{\\sqrt{3}}{2}'] };
  L0.trigSpecial = function (r) {
    var deg = r.pick([30, 45, 60, 120, 135, 150, 120, 135, 150, 90]), v = r.pick([0, 1, 2, 2, 2]), ref = deg > 90 ? 180 - deg : deg;
    if (v === 2) {           /* 直接算 |a||b|cosθ：本章最常用的形式 */
      var ka = r.int(1, 6), kb = r.int(1, 6), cr = cosR(deg);
      return { q: '求 ' + T(ka + '\\times ' + kb + '\\times\\cos' + deg + '^\\circ') + ' 的值。', a: T(radTex(ka * kb * cr[0], cr[1], cr[2])),
        h: '先寫出 $\\cos' + deg + '^\\circ=' + TRIG[deg][1] + '$' + (deg > 90 ? '（鈍角的 $\\cos$ 是負的：$\\cos' + deg + '^\\circ=-\\cos' + ref + '^\\circ$）' : '') + '，再乘上 $' + ka + '\\times ' + kb + '$ 並約分。內積 $|\\vec a||\\vec b|\\cos\\theta$ 就是這個算式。',
        p: { deg: deg, v: v, ka: ka, kb: kb } };
    }
    if (v === 0) return { q: '求 ' + T('\\cos' + deg + '^\\circ') + ' 與 ' + T('\\sin' + deg + '^\\circ') + ' 的值。', a: T('\\cos' + deg + '^\\circ=' + TRIG[deg][1]) + '，' + T('\\sin' + deg + '^\\circ=' + TRIG[deg][0]),
      h: (deg > 90 ? '鈍角用補角：$\\cos' + deg + '^\\circ=-\\cos' + ref + '^\\circ$、$\\sin' + deg + '^\\circ=\\sin' + ref + '^\\circ$（第二象限 $\\cos$ 為負、$\\sin$ 為正）。' : deg === 90 ? '$90^\\circ$ 在單位圓上是點 $(0,1)$：$x$ 坐標是 $\\cos$、$y$ 坐標是 $\\sin$。' : '特殊直角三角形：$30^\\circ$-$60^\\circ$-$90^\\circ$ 的邊長比 $1:\\sqrt3:2$、$45^\\circ$-$45^\\circ$-$90^\\circ$ 的邊長比 $1:1:\\sqrt2$，$\\cos' + deg + '^\\circ=\\dfrac{\\text{鄰邊}}{\\text{斜邊}}$。') + '內積 $|\\vec a||\\vec b|\\cos\\theta$ 每一題都要用到這些值。',
      p: { deg: deg, v: v } };
    var d2 = r.pick([30, 45, 60, 120, 135, 150]), cv = TRIG[d2][1];
    return { q: '已知 ' + T('0^\\circ\\le\\theta\\le180^\\circ') + ' 且 ' + T('\\cos\\theta=' + cv) + '，求 ' + T('\\theta') + '。', a: T('\\theta=' + d2 + '^\\circ'),
      h: '$\\cos\\theta$ ' + (d2 > 90 ? '是負的 ⟹ $\\theta$ 是鈍角：先找 $\\cos$ 值為 $' + TRIG[180 - d2][1] + '$ 的銳角，再用 $180^\\circ$ 去減。' : '是正的 ⟹ $\\theta$ 是銳角，直接對特殊角的表。') + '由內積反求夾角就是在做這件事。',
      p: { deg: d2, v: v } };
  };
  L0.cosLaw = function (r) {
    var b = r.int(2, 8), c = r.int(2, 8), deg = r.pick([60, 120, 90, 60, 120]), tw = deg === 60 ? -1 : deg === 120 ? 1 : 0, a2 = b * b + c * c + tw * b * c;
    return { q: T('\\triangle ABC') + ' 中 ' + T('\\overline{AB}=' + c) + '、' + T('\\overline{AC}=' + b) + '、' + T('\\angle A=' + deg + '^\\circ') + '，求 ' + T('\\overline{BC}') + '。', a: T(sqrtTex(a2)),
      h: '餘弦定理：$\\overline{BC}^2=' + c + '^2+' + b + '^2-2\\cdot' + c + '\\cdot' + b + '\\cdot\\cos' + deg + '^\\circ$' + (deg === 120 ? '，注意 $\\cos120^\\circ$ 是負的，減負變加' : '') + '。本章 $|\\vec a-\\vec b|^2$ 的展開式其實就是餘弦定理。',
      p: { b: b, c: c, deg: deg } };
  };
  L0.linSys2 = function (r) {
    var x = r.int(-4, 5), y = r.int(-4, 5), a1, b1, a2, b2;
    do { a1 = r.nz(-4, 4); b1 = r.nz(-4, 4); a2 = r.nz(-4, 4); b2 = r.nz(-4, 4); } while (a1 * b2 - a2 * b1 === 0 || (a1 < 0 && b1 < 0) || (a2 < 0 && b2 < 0));
    var e1 = term(a1, 'x', true) + term(b1, 'y', false) + '=' + (a1 * x + b1 * y), e2 = term(a2, 'x', true) + term(b2, 'y', false) + '=' + (a2 * x + b2 * y);
    return { q: '解聯立方程式 ' + T('\\begin{cases}' + e1 + '\\\\ ' + e2 + '\\end{cases}') + '。', a: T('(x,y)=' + vt([x, y])),
      h: '加減消去法：先決定消 $x$ 還是消 $y$（這題 $y$ 的係數是 $' + b1 + '$ 與 $' + b2 + '$），把兩式乘到係數絕對值相同，同號相減、異號相加。本章「把 $\\vec c$ 寫成 $x\\vec a+y\\vec b$」比較兩個分量後就是它。',
      p: { l1: [a1, b1], l2: [a2, b2], ans: [x, y] } };
  };
  L0.quadMinT = function (r) {
    var a = r.pick([1, 2, 5, 10, 13]), h = r.nz(-4, 4), k = r.int(1, 30), bq = -2 * a * h, cq = a * h * h + k;
    return { q: '設 ' + T('t') + ' 為實數，求 ' + T((a === 1 ? '' : a) + 't^2' + term(bq, 't', false) + term(cq, '', false)) + ' 的最小值，以及此時的 ' + T('t') + '。', a: T('t=' + h) + ' 時，最小值 ' + T(String(k)),
      h: '配方：' + (a === 1 ? '' : '先把 $' + a + '$ 提出來，') + '$t$ 的一次項係數' + (a === 1 ? '' : '除以 $' + a + '$ 後') + '是 $' + (-2 * h) + '$，取一半得 $' + (-h) + '$ ⟹ $' + (a === 1 ? '' : a) + '(t' + term(-h, '', false) + ')^2+\\square$。本章 $|t\\vec a+\\vec b|^2$ 展開後就是 $t$ 的二次式，最短距離靠配方。',
      p: { a: a, h: h, k: k } };
  };
  var META_L0 = [['distMid', '兩點距離與中點'], ['trigSpecial', '特殊角的 sin 與 cos'], ['cosLaw', '餘弦定理'], ['linSys2', '二元一次聯立方程式'], ['quadMinT', '配方求最小值']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    distMid: { txt: '兩點距離公式與中點（高一上第二章 直線與圓）——向量的長度、分點公式都從這裡來', link: '../g10a-ch02/practice.html#L1' },
    trigSpecial: { txt: '特殊角（含鈍角）的 sin、cos 值（高一下第四章 三角比）——內積 |a||b|cosθ 每題都用', link: '../g10b-ch04/practice.html#L1' },
    cosLaw: { txt: '餘弦定理（高一下第四章 三角比）——|a−b|² 的展開式就是它', link: '../g10b-ch04/practice.html#L1' },
    linSys2: { txt: '二元一次聯立方程式（國中）——線性組合求係數、求交點都在解它', link: null },
    quadMinT: { txt: '二次函數配方求最小值（高一上第三章 多項式函數）——|ta+b| 的最小值靠配方', link: '../g10a-ch03/practice.html#L1' }
  };

  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  function sign3(x) { return x > 0 ? 1 : x < 0 ? -1 : 0; }
  var CONTRAST = {
    'L1.segCoef': { f: function (p) { return !!p.ext; }, why: '內分時兩個係數都在 $0$ 與 $1$ 之間；外分（$P$ 在延長線上）時有一個係數是負的。不管內分外分，兩係數的和都是 $1$——這是判斷「$P$ 在不在直線 $AB$ 上」的判準。' },
    'L1.dotCoord': { f: function (p) { return sign3(p.ans.dot); }, why: '內積的正負直接告訴你夾角的種類：正 ⟹ 銳角（或同向）、$0$ ⟹ 直角、負 ⟹ 鈍角（或反向）。算出 $\\cos\\theta$ 之前先看正負，可以檢查答案。' },
    'L1.dotLenAngle': { f: function (p) { return p.deg > 90; }, why: '夾角是鈍角時 $\\cos\\theta$ 為負，內積是負的；平方展開 $|k_1\\vec a+k_2\\vec b|^2$ 時中間那一項 $2k_1k_2(\\vec a\\cdot\\vec b)$ 的正負要跟著小心。' },
    'L1.projVec': { f: function (p) { return sign3(p.a[0] * p.b[0] + p.a[1] * p.b[1]); }, why: '正射影向量 $=\\dfrac{\\vec a\\cdot\\vec b}{|\\vec b|^2}\\vec b$：內積為正時與 $\\vec b$ 同方向，為負時與 $\\vec b$ 反方向；<b>正射影長</b>則永遠取非負。' },
    'L1.angleFromDot': { f: function (p) { return p.ans > 90; }, why: '$\\cos\\theta$ 為正是銳角、為負是鈍角：先找參考的銳角，負的再用 $180^\\circ$ 去減。' },
    'L1.triDot': { f: function (p) { return !!p.M; }, why: '只給三邊長時，內積靠餘弦定理：$\\overrightarrow{AB}\\cdot\\overrightarrow{AC}=\\dfrac{b^2+c^2-a^2}{2}$；$M$ 是 $\\overline{CA}$ 中點時 $\\overrightarrow{AM}=\\frac12\\overrightarrow{AC}$，內積只是再乘 $\\frac12$。' },
    'L1.coefRegion': { f: function (p) { return (p.ans.inside ? 'in' : 'out') + (p.ans.onBC ? 'BC' : ''); }, why: '$\\overrightarrow{AP}=x\\overrightarrow{AB}+y\\overrightarrow{AC}$：$x,y\\gt 0$ 且 $x+y\\lt 1$ 在內部、$x+y=1$ 在 $\\overline{BC}$ 上、$x+y\\gt 1$ 已經跨過 $\\overline{BC}$ 到外面。$\\triangle PBC$ 佔的比例是 $|1-x-y|$。' },
    'L2.detScale': { f: function (p) { return !!p.rev; }, why: '新面積 $=|$係數行列式$|\\times$ 舊面積：一題由舊求新用乘的，一題由新反求舊用除的。' },
    'L2.sumRange': { f: function (p) { return p.ans[0] === 0; }, why: '三個長度能圍成三角形（最長的不超過另外兩個的和）時，三向量可以首尾相接回到原點，最小值是 $0$；圍不成時最小值是「最長的減另外兩個」。最大值永遠是三個長度相加。' },
    'L2.walk': { f: function (p) { return p.turn; }, why: '「左轉 $\\theta$」是行進方向改變 $\\theta$，兩段路向量的夾角就是 $\\theta$（不是 $180^\\circ-\\theta$）；轉的角度不同，$\\cos\\theta$ 的正負與大小就不同。' },
    'L3.threeDivPts': { f: function (p) { return p.v; }, why: '不管從哪一個分點出發，都先把 $\\overrightarrow{AQ}$、$\\overrightarrow{AP}$、$\\overrightarrow{AR}$ 用 $\\overrightarrow{AB}$、$\\overrightarrow{AC}$ 寫好，再用「終點減起點」——起點換了，只是減的對象換了。' },
    'L3.isoRightVertex': { f: function (p) { return p.v; }, why: '直角在 $C$：從 $\\overline{AB}$ 的中點出發，把「半條 $\\overline{AB}$」旋轉 $90^\\circ$；直角在 $A$：直接把 $\\overrightarrow{AB}$ 旋轉 $90^\\circ$ 接到 $A$。旋轉的向量不同、接的起點也不同。' },
    'L3.lineAngle': { f: function (p) { return p.ask; }, why: '同樣由法向量算出 $\\cos\\theta$；要 $\\sin\\theta$ 就用 $\\sin^2\\theta+\\cos^2\\theta=1$，要 $\\tan\\theta$ 再相除。交角取銳角，所以三個值都是正的。' },
    'L3.paraFourth': { f: function (p) { return p.v; }, why: '頂點依序 $A,B,C,D$：缺 $D$ 用 $D=A+C-B$、缺 $C$ 用 $C=B+D-A$——都來自「對角線互相平分」$A+C=B+D$。' },
    'L3.detScaleArea': { f: function (p) { return p.tri; }, why: '兩向量所張的三角形面積是平行四邊形的一半：係數行列式的倍率一樣，問三角形就多除以 $2$。' },
    'L3.hypotenusePts': { f: function (p) { return p.v === 3; }, why: '等腰直角時兩個對稱的等分點到 $A$ 一樣遠，$\\cos$ 是有理數；一般的直角三角形改問內積，建坐標後內積只要坐標相乘相加，不必算長度。' },
    'L3.lenFromAngle': { f: function (p) { return p.deg; }, why: '夾角 $60^\\circ$ 時 $\\vec a\\cdot\\vec b$ 為正、$120^\\circ$ 為負、$90^\\circ$ 為 $0$：平方展開式中間那一項 $2k_1k_2(\\vec a\\cdot\\vec b)$ 跟著變。' },
    'L3.forceBalance': { f: function (p) { return p.v; }, why: '平衡就是 $\\vec a+\\vec b+\\vec c=\\vec 0$，所以 $|\\vec c|=|\\vec a+\\vec b|$：一題由夾角求 $|\\vec c|$，一題由 $|\\vec c|$ 反求夾角，用的是同一條平方展開式。' },
    'L3.projOnLine': { f: function (p) { return p.v; }, why: '正射影「向量」有方向、要乘回方向向量；正射影「長」只是 $\\dfrac{|\\overrightarrow{AB}\\cdot\\vec d|}{|\\vec d|}$ 一個非負的數。' }
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
