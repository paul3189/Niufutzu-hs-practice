/* ══════════════════════════════════════════════════════════════
   g10a-ch02 直線與圓・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）
     a：答案（HTML）
     h：一行提示（做不出來時看）
     p：產生這題用的參數與結構化答案（給 Node／sympy 獨立驗算用，頁面不顯示）
   所有答案都由程式用「精確算術」算出（整數、分數、根式），不用浮點。
   同時可在瀏覽器（window.PGEN）與 Node（module.exports）使用。
   ══════════════════════════════════════════════════════════════ */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.PGEN = factory();
}(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  /* ────────── 亂數（可指定種子，方便重現） ────────── */
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

  /* ────────── 整數工具 ────────── */
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function gcd3(a, b, c) { return gcd(gcd(a, b), c); }
  function simpSqrt(n) {          /* n = c²·r，r 無平方因數 */
    var c = 1, r = n;
    for (var k = 2; k * k <= r; k++) { while (r % (k * k) === 0) { r /= k * k; c *= k; } }
    return { c: c, r: r };
  }
  function isSquare(n) { var s = Math.round(Math.sqrt(n)); return s * s === n; }

  /* ────────── 分數 ────────── */
  function F(n, d) {
    if (d === undefined) d = 1;
    if (d < 0) { n = -n; d = -d; }
    var g = gcd(n, d) || 1;
    return { n: n / g, d: d / g };
  }
  var Fr = {
    add: function (x, y) { return F(x.n * y.d + y.n * x.d, x.d * y.d); },
    sub: function (x, y) { return F(x.n * y.d - y.n * x.d, x.d * y.d); },
    mul: function (x, y) { return F(x.n * y.n, x.d * y.d); },
    div: function (x, y) { return F(x.n * y.d, x.d * y.n); },
    eq: function (x, y) { return x.n * y.d === y.n * x.d; },
    lt: function (x, y) { return x.n * y.d < y.n * x.d; },
    toNum: function (x) { return x.n / x.d; },
    tex: function (x, small) {
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };

  /* ────────── 排版工具 ────────── */
  function T(s) { return '$' + s + '$'; }
  function sqrtTex(n) {           /* √n 化簡後的 LaTeX，n 正整數 */
    var s = simpSqrt(n);
    if (s.r === 1) return String(s.c);
    return (s.c === 1 ? '' : s.c) + '\\sqrt{' + s.r + '}';
  }
  /* (n/d)·√r 的排版；r=1 即分數 */
  function surdFrac(n, d, r) {
    var f = F(n, d);
    if (r === 1) return Fr.tex(f);
    if (f.n === 0) return '0';
    var num = (Math.abs(f.n) === 1 ? '' : Math.abs(f.n)) + '\\sqrt{' + r + '}';
    var s = (f.n < 0 ? '-' : '');
    if (f.d === 1) return s + num;
    return s + '\\dfrac{' + num + '}{' + f.d + '}';
  }
  /* num/√s 化簡（有理化）→ {n,d,r} 及 tex */
  function distSimp(num, s) {
    var q = simpSqrt(s);          /* √s = q.c √q.r */
    /* num/(q.c √r) = num √r /(q.c r) */
    var f = F(num, q.c * q.r);
    return { n: f.n, d: f.d, r: q.r, tex: surdFrac(f.n, f.d, q.r) };
  }
  function ptTex(x, y) {          /* x,y 可為數字或 tex 字串 */
    return '(' + (typeof x === 'number' ? x : x) + ',\\ ' + (typeof y === 'number' ? y : y) + ')';
  }
  function fptTex(fx, fy) { return '(' + Fr.tex(fx, true) + ',\\ ' + Fr.tex(fy, true) + ')'; }
  /* 一次項：coef·var；first=是否為第一項 */
  function term(coef, v, first) {
    if (coef === 0) return '';
    var sgn = coef < 0 ? '-' : (first ? '' : '+');
    var ab = Math.abs(coef);
    return sgn + (ab === 1 && v ? '' : ab) + v;
  }
  /* ax+by+c=0，先約分並讓第一個非零係數為正 */
  function normLine(a, b, c) {
    var g = gcd3(a, b, c) || 1; a /= g; b /= g; c /= g;
    var lead = a !== 0 ? a : b;
    if (lead < 0) { a = -a; b = -b; c = -c; }
    return [a, b, c];
  }
  /* ────────── 提示專用：把本題數字代進式子 ────────── */
  function hpz(n) { return n < 0 ? '(' + n + ')' : String(n); }     /* 負數代入時加括號 */
  function hdif(u, v) { return v === 0 ? String(u) : hpz(u) + '-' + hpz(v); }   /* u-v 的代入寫法，不寫「-0」 */
  function hmn(sym, v) { return v === 0 ? sym : sym + '-' + hpz(v); }           /* x-x0 的代入寫法 */
  function hsub(A, B, C, X, Y) {        /* A·X+B·Y+C 的「數字代入式」；係數 ±1 省略，係數或代入值為 0 的項略去 */
    function tm(co, v, first) {
      if (co === 0 || v === 0) return '';
      var sg = co < 0 ? '-' : (first ? '' : '+'), ab = Math.abs(co);
      return sg + (ab === 1 ? '' : ab + '\\times') + hpz(v);
    }
    var s = tm(A, X, true);
    s += tm(B, Y, s === '');
    s += (C === 0 ? '' : (C < 0 ? '-' + (-C) : (s === '' ? '' : '+') + C));
    return s === '' ? '0' : s;
  }
  function lineTex(a, b, c) {
    var n = normLine(a, b, c); a = n[0]; b = n[1]; c = n[2];
    var s = term(a, 'x', true);
    s += term(b, 'y', s === '');
    s += term(c, '', s === '');
    return s + '=0';
  }
  /* 「(a + b·k)」形式的係數（直線族用） */
  function kcoef(a, b) {          /* a + b k */
    var s = term(b, 'k', true) + term(a, '', b === 0);
    return s;
  }
  function kterm(a, b, v, first) {   /* (a+bk)·v */
    if (a === 0 && b === 0) return '';
    if (b === 0) return term(a, v, first);
    if (a === 0) { var s = term(b, 'k', first); return s + v; }
    return (first ? '' : '+') + '(' + kcoef(a, b) + ')' + v;
  }
  var PYTH = [[3, 4], [4, 3], [5, 12], [12, 5], [6, 8], [8, 6]];   /* 3-4-5 型法向量 */

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* 1-1 兩點斜率 */
  L1.slope2pt = function (r) {
    var x1 = r.int(-6, 6), y1 = r.int(-6, 6), x2, y2;
    do { x2 = r.int(-6, 6); y2 = r.int(-6, 6); } while (x2 === x1 || (y2 === y1 && r() < 0.7));
    var mfr = F(y2 - y1, x2 - x1);
    return { q: '求過 ' + T('A' + ptTex(x1, y1)) + '、' + T('B' + ptTex(x2, y2)) + ' 兩點的直線斜率。',
             a: T('m=' + Fr.tex(mfr)),
             h: '斜率是「$y$ 的變化量」除以「$x$ 的變化量」：$m=\\dfrac{y_2-y_1}{x_2-x_1}=\\dfrac{' + hdif(y2, y1) + '}{' + hdif(x2, x1) + '}$，分子分母各自算出來後記得約分（分母化成正的）。',
             p: { x1: x1, y1: y1, x2: x2, y2: y2, ans: [mfr.n, mfr.d] } };
  };

  /* 1-2 兩點距離 */
  L1.dist2pt = function (r) {
    var x1 = r.int(-6, 6), y1 = r.int(-6, 6), dx = r.nz(-7, 7), dy = r.nz(-7, 7);
    var s = dx * dx + dy * dy, q = simpSqrt(s);
    return { q: '求 ' + T('A' + ptTex(x1, y1)) + '、' + T('B' + ptTex(x1 + dx, y1 + dy)) + ' 兩點的距離。',
             a: T('\\overline{AB}=' + sqrtTex(s)),
             h: '兩點距離公式 $\\overline{AB}=\\sqrt{(x_2-x_1)^2+(y_2-y_1)^2}$：代入得 $\\sqrt{\\left(' + hdif(x1 + dx, x1) + '\\right)^2+\\left(' + hdif(y1 + dy, y1) + '\\right)^2}$，先算出根號裡的數，再化成最簡根式。',
             p: { x1: x1, y1: y1, x2: x1 + dx, y2: y1 + dy, ans: [q.c, q.r] } };
  };

  /* 1-3 中點與內分點 */
  L1.midDiv = function (r) {
    var x1 = r.int(-6, 6), y1 = r.int(-6, 6), x2, y2;
    do { x2 = r.int(-6, 6); y2 = r.int(-6, 6); } while (x2 === x1 && y2 === y1);
    var mn = r.pick([[1, 1], [1, 1], [1, 2], [2, 1], [1, 3], [3, 1], [2, 3], [3, 2]]);
    var m = mn[0], n = mn[1];
    var px = F(n * x1 + m * x2, m + n), py = F(n * y1 + m * y2, m + n);
    var q = (m === 1 && n === 1)
      ? '求 ' + T('A' + ptTex(x1, y1)) + '、' + T('B' + ptTex(x2, y2)) + ' 的中點 ' + T('M') + ' 坐標。'
      : '已知 ' + T('A' + ptTex(x1, y1)) + '、' + T('B' + ptTex(x2, y2)) + '，點 ' + T('P') + ' 在線段 ' + T('\\overline{AB}') + ' 上且 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '，求 ' + T('P') + ' 的坐標。';
    var hint = (m === 1 && n === 1)
      ? '中點就是兩個坐標各自取平均：$M=\\left(\\dfrac{' + hpz(x1) + '+' + hpz(x2) + '}{2},\\ \\dfrac{' + hpz(y1) + '+' + hpz(y2) + '}{2}\\right)$，兩個分數分別算出來。'
      : '分點公式 $P=\\dfrac{nA+mB}{m+n}$（靠近哪一點，那一點的權重就大）：這題 $m=' + m + '$、$n=' + n + '$，所以 $x_P=\\dfrac{' + n + '\\times' + hpz(x1) + '+' + m + '\\times' + hpz(x2) + '}{' + (m + n) + '}$，$y_P$ 同樣算法。';
    return { q: q, a: T(fptTex(px, py)),
             h: hint,
             p: { x1: x1, y1: y1, x2: x2, y2: y2, m: m, n: n, ans: [px.n, px.d, py.n, py.d] } };
  };

  /* 1-4 點斜式 → 一般式 */
  L1.lineEq = function (r) {
    var x0 = r.int(-5, 5), y0 = r.int(-5, 5), d = r.pick([1, 1, 2, 3]), n = r.nz(-5, 5);
    if (d !== 1) { n = r.nz(-5, 5); while (gcd(n, d) !== 1) n = r.nz(-5, 5); }
    var line = normLine(n, -d, d * y0 - n * x0);
    return { q: '求過點 ' + T(ptTex(x0, y0)) + ' 且斜率為 ' + T(Fr.tex(F(n, d))) + ' 的直線方程式（化為一般式）。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: '點斜式 $y-y_0=m(x-x_0)$：代入得 $' + hmn('y', y0) + '=' + Fr.tex(F(n, d), true) + '\\left(' + hmn('x', x0) + '\\right)$，' + (d === 1 ? '展開後把所有項移到左邊。' : '兩邊先同乘 $' + d + '$ 去分母，再移項整理。'),
             p: { x0: x0, y0: y0, mn: n, md: d, ans: line } };
  };

  /* 1-5 兩點式 */
  L1.line2pt = function (r) {
    var x1 = r.int(-5, 5), y1 = r.int(-5, 5), x2, y2;
    do { x2 = r.int(-5, 5); y2 = r.int(-5, 5); } while (x2 === x1 && y2 === y1);
    var line = normLine(y2 - y1, -(x2 - x1), (x2 - x1) * y1 - (y2 - y1) * x1);
    return { q: '求過 ' + T('A' + ptTex(x1, y1)) + '、' + T('B' + ptTex(x2, y2)) + ' 兩點的直線方程式（化為一般式）。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: (x1 === x2)
               ? '注意兩點的 $x$ 坐標都是 $' + x1 + '$：這種「$x$ 不動」的直線是鉛直線，沒有斜率，不能用點斜式，直接想這條線上的點 $x$ 等於多少。'
               : '先求斜率 $m=\\dfrac{' + hdif(y2, y1) + '}{' + hdif(x2, x1) + '}$，再用點斜式 $' + hmn('y', y1) + '=m\\left(' + hmn('x', x1) + '\\right)$，最後去分母、移項成一般式。',
             p: { x1: x1, y1: y1, x2: x2, y2: y2, ans: line } };
  };

  /* 1-6 截距 */
  L1.interceptForm = function (r) {
    if (r() < 0.5) {
      var a = r.nz(-6, 6), b = r.nz(-6, 6);
      var line = normLine(b, a, -a * b);
      return { q: '求 ' + T('x') + ' 截距為 ' + T(String(a)) + '、' + T('y') + ' 截距為 ' + T(String(b)) + ' 的直線方程式（化為一般式）。',
               a: T(lineTex(line[0], line[1], line[2])),
               h: '截距式 $\\dfrac{x}{a}+\\dfrac{y}{b}=1$：代入得 $\\dfrac{x}{' + a + '}+\\dfrac{y}{' + b + '}=1$，兩邊同乘 $' + (a * b) + '$ 去分母後再移項。',
               p: { type: 0, a: a, b: b, ans: line } };
    }
    var A = r.nz(-5, 5), B = r.nz(-5, 5), C = r.nz(-9, 9);
    var xi = F(-C, A), yi = F(-C, B), nl = normLine(A, B, C);
    return { q: '求直線 ' + T(lineTex(A, B, C)) + ' 的 ' + T('x') + ' 截距與 ' + T('y') + ' 截距。',
             a: T('x') + ' 截距 ' + T(Fr.tex(xi)) + '，' + T('y') + ' 截距 ' + T(Fr.tex(yi)),
             h: '截距就是與坐標軸的交點。$x$ 截距：令 $y=0$，解 $' + term(nl[0], 'x', true) + term(nl[2], '', false) + '=0$；$y$ 截距：令 $x=0$，解 $' + term(nl[1], 'y', true) + term(nl[2], '', false) + '=0$。',
             p: { type: 1, A: A, B: B, C: C, ans: [xi.n, xi.d, yi.n, yi.d] } };
  };

  /* 1-7 平行與垂直 */
  L1.parPerp = function (r) {
    var a = r.nz(-4, 4), b = r.nz(-4, 4), c = r.int(-7, 7), x0 = r.int(-5, 5), y0 = r.int(-5, 5);
    var par = r() < 0.5, line;
    if (par) line = normLine(a, b, -(a * x0 + b * y0));
    else line = normLine(b, -a, -(b * x0 - a * y0));
    var nl = normLine(a, b, c);
    return { q: '求過點 ' + T(ptTex(x0, y0)) + ' 且與直線 ' + T(lineTex(a, b, c)) + (par ? ' 平行' : ' 垂直') + ' 的直線方程式。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: par
               ? '平行 ⟹ $x,y$ 的係數照抄，只有常數不同：設所求為 $' + term(nl[0], 'x', true) + term(nl[1], 'y', false) + '=k$，把 ' + T(ptTex(x0, y0)) + ' 代入左邊算出 $k=' + hsub(nl[0], nl[1], 0, x0, y0) + '$。'
               : '垂直 ⟹ $x,y$ 的係數對調、其中一個變號：設所求為 $' + term(nl[1], 'x', true) + term(-nl[0], 'y', false) + '=k$，把 ' + T(ptTex(x0, y0)) + ' 代入左邊算出 $k=' + hsub(nl[1], -nl[0], 0, x0, y0) + '$。',
             p: { a: a, b: b, c: c, x0: x0, y0: y0, par: par ? 1 : 0, ans: line } };
  };

  /* 1-8 兩直線交點 */
  L1.intersect = function (r) {
    var x0 = r.int(-5, 5), y0 = r.int(-5, 5), a1, b1, a2, b2;
    do { a1 = r.nz(-3, 3); b1 = r.nz(-3, 3); a2 = r.nz(-3, 3); b2 = r.nz(-3, 3); } while (a1 * b2 - a2 * b1 === 0);
    var L1t = lineTex(a1, b1, -(a1 * x0 + b1 * y0)), L2t = lineTex(a2, b2, -(a2 * x0 + b2 * y0));
    var n1 = normLine(a1, b1, -(a1 * x0 + b1 * y0)), n2 = normLine(a2, b2, -(a2 * x0 + b2 * y0));
    return { q: '求兩直線 ' + T(L1t) + ' 與 ' + T(L2t) + ' 的交點。',
             a: T(ptTex(x0, y0)),
             h: '聯立消去一個變數：把第一條兩邊同乘 $' + hpz(n2[1]) + '$、第二條兩邊同乘 $' + hpz(n1[1]) + '$，兩式的 $y$ 係數就一樣（都是 $' + (n1[1] * n2[1]) + '$），相減即可消去 $y$；解出 $x$ 再代回其中一條求 $y$。',
             p: { l1: normLine(a1, b1, -(a1 * x0 + b1 * y0)), l2: normLine(a2, b2, -(a2 * x0 + b2 * y0)), ans: [x0, y0] } };
  };

  /* 2-1 點到直線距離 */
  L1.ptLineDist = function (r) {
    var nv = r.pick(PYTH.concat([[1, 1], [1, -1], [2, 1], [1, 2], [1, -2]]));
    var a = nv[0] * r.sign(), b = nv[1], c = r.int(-9, 9), x0 = r.int(-5, 5), y0 = r.int(-5, 5);
    var num = Math.abs(a * x0 + b * y0 + c), s = a * a + b * b;
    if (num === 0) c += 1, num = Math.abs(a * x0 + b * y0 + c);
    var d = distSimp(num, s), nl = normLine(a, b, c);
    return { q: '求點 ' + T(ptTex(x0, y0)) + ' 到直線 ' + T(lineTex(a, b, c)) + ' 的距離。',
             a: T('d=' + d.tex),
             h: '點到直線距離公式 $d=\\dfrac{|ax_0+by_0+c|}{\\sqrt{a^2+b^2}}$：分子 $=\\left|' + hsub(nl[0], nl[1], nl[2], x0, y0) + '\\right|$、分母 $=\\sqrt{' + hpz(nl[0]) + '^2+' + hpz(nl[1]) + '^2}$，相除後若分母還有根號要有理化。',
             p: { a: a, b: b, c: c, x0: x0, y0: y0, ans: [d.n, d.d, d.r] } };
  };

  /* 2-2 兩平行線距離 */
  L1.parDist = function (r) {
    var nv = r.pick(PYTH.concat([[1, 1], [1, -1], [2, 1], [1, 3]]));
    var a = nv[0], b = nv[1] * r.sign(), c1 = r.int(-9, 9), c2;
    do { c2 = r.int(-9, 9); } while (c2 === c1);
    var k = r.pick([1, 1, 2, 3]);
    var d = distSimp(Math.abs(c1 - c2), a * a + b * b);
    var n1 = normLine(a, b, c1), n2 = normLine(k * a, k * b, k * c2), rho = F(n2[0] || n2[1], n1[0] || n1[1]);
    var how = (rho.n === 1 && rho.d === 1) ? '兩條的 $x,y$ 係數已經一樣'
      : (rho.d === 1 ? '把第二條每一項同除以 $' + rho.n + '$' : (rho.n === 1 ? '把第二條每一項同乘 $' + rho.d + '$' : '把第二條每一項同乘 $' + rho.d + '$ 再同除以 $' + rho.n + '$'));
    return { q: '求兩平行線 ' + T(lineTex(a, b, c1)) + ' 與 ' + T(lineTex(k * a, k * b, k * c2)) + ' 之間的距離。',
             a: T('d=' + d.tex),
             h: '這兩條是平行線（$x,y$ 係數成比例）。' + how + '，讓兩條的 $x,y$ 係數完全相同之後，再用 $d=\\dfrac{|c_1-c_2|}{\\sqrt{a^2+b^2}}$；分母 $=\\sqrt{' + n1[0] + '^2+' + hpz(n1[1]) + '^2}$。',
             p: { a: a, b: b, c1: c1, c2: c2, k: k, ans: [d.n, d.d, d.r] } };
  };

  /* 2-3 三角形面積 */
  L1.triArea = function (r) {
    var P;
    do {
      P = [[r.int(-5, 5), r.int(-5, 5)], [r.int(-5, 5), r.int(-5, 5)], [r.int(-5, 5), r.int(-5, 5)]];
    } while ((P[1][0] - P[0][0]) * (P[2][1] - P[0][1]) - (P[2][0] - P[0][0]) * (P[1][1] - P[0][1]) === 0);
    var twice = Math.abs((P[1][0] - P[0][0]) * (P[2][1] - P[0][1]) - (P[2][0] - P[0][0]) * (P[1][1] - P[0][1]));
    var A = F(twice, 2);
    var bx = P[1][0] - P[0][0], by = P[1][1] - P[0][1], cx = P[2][0] - P[0][0], cy = P[2][1] - P[0][1];
    return { q: '求以 ' + T('A' + ptTex(P[0][0], P[0][1])) + '、' + T('B' + ptTex(P[1][0], P[1][1])) + '、' + T('C' + ptTex(P[2][0], P[2][1])) + ' 為頂點的三角形面積。',
             a: T(Fr.tex(A)),
             h: '把 $A$ 平移到原點（面積不變）：$B-A=' + ptTex(bx, by) + '$、$C-A=' + ptTex(cx, cy) + '$，再用 $\\dfrac12|ad-bc|$，也就是 $\\dfrac12\\left|' + hpz(bx) + '\\times' + hpz(cy) + '-' + hpz(cx) + '\\times' + hpz(by) + '\\right|$。',
             p: { P: P, ans: [A.n, A.d] } };
  };

  /* 2-4 對稱點（課綱內：x 軸、y 軸、原點、y=x） */
  L1.symAxis = function (r) {
    var x0 = r.nz(-6, 6), y0 = r.nz(-6, 6), t = r.int(0, 3);
    var names = ['x 軸', 'y 軸', '原點', '直線 $y=x$'];
    var ans = [[x0, -y0], [-x0, y0], [-x0, -y0], [y0, x0]][t];
    var hs = ['對 $x$ 軸對稱：橫坐標不動、縱坐標變號。這題 $x$ 一直是 $' + x0 + '$，要動的只有 $y=' + y0 + '$ 這一格。',
              '對 $y$ 軸對稱：縱坐標不動、橫坐標變號。這題 $y$ 一直是 $' + y0 + '$，要動的只有 $x=' + x0 + '$ 這一格。',
              '對原點對稱＝先對 $x$ 軸再對 $y$ 軸，兩個坐標都要變號：$x=' + x0 + '$ 與 $y=' + y0 + '$ 各取相反數。',
              '對直線 $y=x$ 對稱：把橫坐標與縱坐標互換位置（$' + x0 + '$ 與 $' + y0 + '$ 交換），可以用「中點在 $y=x$ 上、連線與 $y=x$ 垂直」檢驗。'];
    return { q: '求點 ' + T('P' + ptTex(x0, y0)) + ' 對 ' + names[t] + ' 的對稱點。',
             a: T(ptTex(ans[0], ans[1])),
             h: hs[t],
             p: { x0: x0, y0: y0, t: t, ans: ans } };
  };

  /* 2-5 平移直線 */
  L1.translate = function (r) {
    var a = r.nz(-4, 4), b = r.nz(-4, 4), c = r.int(-6, 6), h = r.nz(-4, 4), k = r.nz(-4, 4);
    var line = normLine(a, b, c - a * h - b * k);
    var nl = normLine(a, b, c);
    var ct = function (n, first) { return n === 1 ? (first ? '' : '+') : (n === -1 ? '-' : term(n, '', first)); };
    return { q: '將直線 ' + T(lineTex(a, b, c)) + ' 向' + (h > 0 ? '右' : '左') + '平移 ' + T(String(Math.abs(h))) + ' 單位、再向' + (k > 0 ? '上' : '下') + '平移 ' + T(String(Math.abs(k))) + ' 單位，求新直線的方程式。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: '平移用代換：右移 $h$、上移 $k$ 就是把 $x$ 換成 $x-h$、$y$ 換成 $y-k$（和移動方向相反）。這題代入後是 $' + ct(nl[0], true) + '\\left(x-' + hpz(h) + '\\right)' + ct(nl[1], false) + '\\left(y-' + hpz(k) + '\\right)' + term(nl[2], '', false) + '=0$，展開再合併常數項。',
             p: { a: a, b: b, c: c, h: h, k: k, ans: line } };
  };

  /* 2-6 中垂線 */
  L1.perpBisector = function (r) {
    var mx = r.int(-4, 4), my = r.int(-4, 4), u, v;
    do { u = r.int(-4, 4); v = r.int(-4, 4); } while (u === 0 && v === 0);
    var x1 = mx - u, y1 = my - v, x2 = mx + u, y2 = my + v;
    var line = normLine(2 * u, 2 * v, -(2 * u * mx + 2 * v * my));
    var mid = '中點 $M=\\left(\\dfrac{' + hpz(x1) + '+' + hpz(x2) + '}{2},\\ \\dfrac{' + hpz(y1) + '+' + hpz(y2) + '}{2}\\right)$';
    var hh = u === 0
      ? '中垂線＝過 $\\overline{AB}$ 中點、且與 $\\overline{AB}$ 垂直的直線。這題 $A$、$B$ 的 $x$ 坐標都是 $' + x1 + '$，$\\overline{AB}$ 是鉛直線，所以中垂線是水平線；只要算出 ' + mid + ' 的 $y$ 坐標就好。'
      : (v === 0
        ? '中垂線＝過 $\\overline{AB}$ 中點、且與 $\\overline{AB}$ 垂直的直線。這題 $A$、$B$ 的 $y$ 坐標都是 $' + y1 + '$，$\\overline{AB}$ 是水平線，所以中垂線是鉛直線；只要算出 ' + mid + ' 的 $x$ 坐標就好。'
        : '中垂線＝過 $\\overline{AB}$ 中點、且與 $\\overline{AB}$ 垂直的直線。先算 ' + mid + '；$\\overline{AB}$ 的斜率 $=\\dfrac{' + hdif(y2, y1) + '}{' + hdif(x2, x1) + '}$，中垂線的斜率與它相乘要等於 $-1$，再用點斜式過 $M$。');
    return { q: '求 ' + T('A' + ptTex(x1, y1)) + '、' + T('B' + ptTex(x2, y2)) + ' 的中垂線方程式。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: hh,
             p: { x1: x1, y1: y1, x2: x2, y2: y2, ans: line } };
  };

  /* 3-1 半平面：哪些點滿足不等式 */
  L1.halfPlane = function (r) {
    var a0 = r.nz(-3, 3), b0 = r.nz(-3, 3), c0 = r.int(-5, 5), strict = r() < 0.5, gt = r() < 0.5;
    /* 題目印的是 normLine 之後的式子，判斷也一律用它，兩者才會一致 */
    var nl = normLine(a0, b0, c0), a = nl[0], b = nl[1], c = nl[2];
    var all = [], gx, gy;
    for (gx = -4; gx <= 4; gx++) for (gy = -4; gy <= 4; gy++) all.push([gx, gy]);
    all = r.shuffle(all);
    var yes = [], no = [], i;
    for (i = 0; i < all.length; i++) {
      var v = a * all[i][0] + b * all[i][1] + c, ok;
      if (strict) ok = gt ? v > 0 : v < 0; else ok = gt ? v >= 0 : v <= 0;
      (ok ? yes : no).push(all[i]);
    }
    var ny = r.int(1, 3);                       /* 滿足的點數：1～3，四點互異 */
    if (ny > yes.length) ny = yes.length;
    if (4 - ny > no.length) ny = 4 - no.length;
    /* 有一半的機會讓其中一點剛好落在邊界線上，才考得到 ≤／≥ 與 ＜／＞ 的差別 */
    var zero = all.filter(function (pt) { return a * pt[0] + b * pt[1] + c === 0; });
    if (zero.length && r() < 0.6) {
      var z = zero[0], host = strict ? no : yes;   /* 邊界點：含等號時算滿足，嚴格時不滿足 */
      for (i = 0; i < host.length; i++) if (host[i][0] === z[0] && host[i][1] === z[1]) { host.splice(i, 1); host.unshift(z); break; }
    }
    var sel = [];
    for (i = 0; i < ny; i++) sel.push([yes[i], 1]);
    for (i = 0; i < 4 - ny; i++) sel.push([no[i], 0]);
    sel = r.shuffle(sel);
    var pts = sel.map(function (s) { return s[0]; }), ans = sel.map(function (s) { return s[1]; });
    var op = strict ? (gt ? '\\gt' : '\\lt') : (gt ? '\\ge' : '\\le');
    var lhs = lineTex(a, b, c).replace('=0', '');
    var opts = pts.map(function (p, i) { return '(' + (i + 1) + ') ' + T(ptTex(p[0], p[1])); }).join('　');
    var labels = ans.map(function (o, i) { return o ? '(' + (i + 1) + ')' : ''; }).join('');
    return { q: '下列哪些點滿足不等式 ' + T(lhs + op + '0') + '？（可複選）<br>' + opts,
             a: labels || '沒有任何一點滿足',
             h: '一個一個代進 $' + lhs + '$ 算出正負再判斷。例如 (1) 的 ' + T(ptTex(pts[0][0], pts[0][1])) + ' 代入得 $' + hsub(a, b, c, pts[0][0], pts[0][1]) + '$，四個點都算一次；注意 $' + op + '$ ' + (strict ? '不含等號，剛好落在直線上（算出來是 $0$）的點不算。' : '含等號，落在直線上（算出來是 $0$）的點也算。'),
             p: { a: a, b: b, c: c, op: op, strict: strict ? 1 : 0, gt: gt ? 1 : 0, pts: pts, ans: ans } };
  };

  /* 3-2 線性規劃：頂點代入 */
  L1.lpVertex = function (r) {
    var V, p, q, vals;
    do {
      V = [[r.int(0, 6), r.int(0, 6)], [r.int(0, 6), r.int(0, 6)], [r.int(0, 6), r.int(0, 6)]];
      p = r.nz(-4, 4); q = r.nz(-4, 4);
      vals = V.map(function (v) { return p * v[0] + q * v[1]; });
    } while ((V[1][0] - V[0][0]) * (V[2][1] - V[0][1]) - (V[2][0] - V[0][0]) * (V[1][1] - V[0][1]) === 0 ||
             vals[0] === vals[1] || vals[1] === vals[2] || vals[0] === vals[2]);
    var mx = Math.max.apply(null, vals), mn = Math.min.apply(null, vals);
    var im = vals.indexOf(mx), imn = vals.indexOf(mn);
    var f = term(p, 'x', true) + term(q, 'y', false);
    return { q: '區域 ' + T('R') + ' 是以 ' + T(ptTex(V[0][0], V[0][1])) + '、' + T(ptTex(V[1][0], V[1][1])) + '、' + T(ptTex(V[2][0], V[2][1])) + ' 為頂點的三角形（含邊界）。求 ' + T('f=' + f) + ' 在 ' + T('R') + ' 上的最大值與最小值。',
             a: '最大值 ' + T(String(mx)) + '（在 ' + T(ptTex(V[im][0], V[im][1])) + '），最小值 ' + T(String(mn)) + '（在 ' + T(ptTex(V[imn][0], V[imn][1])) + '）',
             h: '線性目標函數的最大、最小一定出現在頂點，所以把三個頂點依序代入 $f=' + f + '$ 比大小就好。例如第一個頂點 ' + T(ptTex(V[0][0], V[0][1])) + ' 代入得 $f=' + hsub(p, q, 0, V[0][0], V[0][1]) + '$。',
             p: { V: V, p: p, q: q, ans: [mx, mn] } };
  };

  /* 4-1 圓心半徑 → 標準式與一般式 */
  L1.circStd = function (r) {
    var h = r.int(-5, 5), k = r.int(-5, 5), rad = r.int(1, 6);
    var d = -2 * h, e = -2 * k, f = h * h + k * k - rad * rad;
    var std = '(x' + term(-h, '', false) + ')^2+(y' + term(-k, '', false) + ')^2=' + rad * rad;
    std = std.replace('(x)', 'x').replace('(y)', 'y');
    var gen = 'x^2+y^2' + term(d, 'x', false) + term(e, 'y', false) + term(f, '', false) + '=0';
    return { q: '求圓心 ' + T(ptTex(h, k)) + '、半徑 ' + T(String(rad)) + ' 的圓方程式，分別寫成標準式與一般式。',
             a: '標準式 ' + T(std) + '；一般式 ' + T(gen),
             h: '標準式 $(x-h)^2+(y-k)^2=r^2$ 裡，$(h,k)$ 是圓心、$r$ 是半徑：這題 $h=' + h + '$、$k=' + k + '$、$r^2=' + rad + '^2$（圓心坐標是負的時候，括號裡會變成加號）。再用 $(x-h)^2=x^2-2hx+h^2$ 展開、把常數合併，就是一般式。',
             p: { h: h, k: k, r: rad, ans: [d, e, f] } };
  };

  /* 4-2 一般式 → 圓心半徑 */
  L1.circGen = function (r) {
    var h = r.int(-5, 5), k = r.int(-5, 5), rad = r.int(1, 7);
    var d = -2 * h, e = -2 * k, f = h * h + k * k - rad * rad;
    var gen = 'x^2+y^2' + term(d, 'x', false) + term(e, 'y', false) + term(f, '', false) + '=0';
    return { q: '求圓 ' + T(gen) + ' 的圓心與半徑。',
             a: '圓心 ' + T(ptTex(h, k)) + '，半徑 ' + T(String(rad)),
             h: '對照 $x^2+y^2+dx+ey+f=0$：這題 $d=' + d + '$、$e=' + e + '$、$f=' + f + '$。圓心是 $\\left(-\\dfrac{d}{2},\\ -\\dfrac{e}{2}\\right)$，半徑 $r=\\dfrac12\\sqrt{d^2+e^2-4f}=\\dfrac12\\sqrt{' + hpz(d) + '^2+' + hpz(e) + '^2-4\\times' + hpz(f) + '}$；也可以用配方法驗算。',
             p: { d: d, e: e, f: f, ans: [h, k, rad] } };
  };

  /* 4-3 是圓、一點、還是沒有圖形 */
  L1.circKind = function (r) {
    var h = r.int(-4, 4), k = r.int(-4, 4), t = r.int(0, 2), R2;
    if (t === 0) R2 = r.int(1, 25); else if (t === 1) R2 = 0; else R2 = -r.int(1, 12);
    var d = -2 * h, e = -2 * k, f = h * h + k * k - R2;
    var gen = 'x^2+y^2' + term(d, 'x', false) + term(e, 'y', false) + term(f, '', false) + '=0';
    var ans = t === 0 ? '是圓：圓心 ' + T(ptTex(h, k)) + '、半徑 ' + T(sqrtTex(R2)) : (t === 1 ? '只有一點 ' + T(ptTex(h, k)) + '（半徑為 $0$）' : '沒有圖形（配方後右邊 $=' + R2 + '\\lt0$）');
    return { q: '判斷方程式 ' + T(gen) + ' 的圖形是圓、一點、還是沒有圖形？若是圓，求圓心與半徑。',
             a: ans,
             h: '配方後右邊等於 $\\dfrac{d^2+e^2-4f}{4}$，所以只要看 $d^2+e^2-4f$ 的正負：這題 $=' + hpz(d) + '^2+' + hpz(e) + '^2-4\\times' + hpz(f) + '$，算出來為正是圓、為零只有一點、為負沒有圖形。',
             p: { d: d, e: e, f: f, kind: t, ans: [h, k, R2] } };
  };

  /* 4-4 點與圓的位置關係 */
  L1.ptCircle = function (r) {
    var h = r.int(-4, 4), k = r.int(-4, 4), rad = r.int(2, 6), x0 = r.int(-9, 9), y0 = r.int(-9, 9);
    var s = (x0 - h) * (x0 - h) + (y0 - k) * (y0 - k), r2 = rad * rad;
    var pos = s < r2 ? 0 : (s === r2 ? 1 : 2);
    var std = '(x' + term(-h, '', false) + ')^2+(y' + term(-k, '', false) + ')^2=' + r2;
    std = std.replace('(x)', 'x').replace('(y)', 'y');
    return { q: '判斷點 ' + T('P' + ptTex(x0, y0)) + ' 在圓 ' + T(std) + ' 的內部、圓上、還是外部？',
             a: ['內部', '圓上', '外部'][pos] + '（' + T('\\overline{PC}^2=' + s + (pos === 0 ? '\\lt' : (pos === 1 ? '=' : '\\gt')) + r2) + '）',
             h: '比 $\\overline{PC}^2$ 與 $r^2$ 就好，不必開根號（$C$ 是圓心 ' + T(ptTex(h, k)) + '）：$\\overline{PC}^2=\\left(' + hdif(x0, h) + '\\right)^2+\\left(' + hdif(y0, k) + '\\right)^2$，而 $r^2=' + r2 + '$。',
             p: { h: h, k: k, r: rad, x0: x0, y0: y0, ans: pos } };
  };

  /* 5-1 直線與圓的位置關係 */
  L1.lineCircPos = function (r) {
    var nv = r.pick([[3, 4], [4, 3], [3, -4], [4, -3]]);
    var a = nv[0], b = nv[1], h = r.int(-4, 4), k = r.int(-4, 4), rad = r.int(1, 5);
    var t = r.int(0, 2), num;                       /* 0 相交 1 相切 2 相離 */
    if (t === 0) num = r.int(0, 5 * rad - 1); else if (t === 1) num = 5 * rad; else num = 5 * rad + r.int(1, 10);
    var c = num * r.sign() - a * h - b * k;
    var d = distSimp(Math.abs(a * h + b * k + c), 25);
    var std = '(x' + term(-h, '', false) + ')^2+(y' + term(-k, '', false) + ')^2=' + rad * rad;
    std = std.replace('(x)', 'x').replace('(y)', 'y');
    return { q: '判斷直線 ' + T(lineTex(a, b, c)) + ' 與圓 ' + T(std) + ' 的位置關係（相交、相切或相離）。',
             a: ['相交（交於兩點）', '相切', '相離'][t] + '：圓心到直線距離 ' + T('d=' + d.tex + (t === 0 ? '\\lt ' : (t === 1 ? '=' : '\\gt ')) + 'r') + '（' + T('r=' + rad) + '）',
             h: '不要聯立，改算圓心到直線的距離：圓心是 ' + T(ptTex(h, k)) + '，$d=\\dfrac{\\left|' + hsub(a, b, c, h, k) + '\\right|}{\\sqrt{' + a + '^2+' + hpz(b) + '^2}}$，再和 $r=' + rad + '$ 比大小（$d\\lt r$ 相交、$d=r$ 相切、$d\\gt r$ 相離）。',
             p: { a: a, b: b, c: c, h: h, k: k, r: rad, ans: t } };
  };

  /* 5-2 弦長 */
  L1.chordLen = function (r) {
    var pair = r.pick([[5, 3, 8], [5, 4, 6], [10, 6, 16], [10, 8, 12], [13, 5, 24], [13, 12, 10]]);
    var rad = pair[0], d = pair[1], chord = pair[2], h = r.int(-4, 4), k = r.int(-4, 4);
    var nv = r.pick([[3, 4], [4, 3], [3, -4], [4, -3], [1, 0], [0, 1]]);
    var a = nv[0], b = nv[1], s = Math.sqrt(a * a + b * b);   /* 5 或 1 */
    var c = d * s * r.sign() - a * h - b * k;
    var std = '(x' + term(-h, '', false) + ')^2+(y' + term(-k, '', false) + ')^2=' + rad * rad;
    std = std.replace('(x)', 'x').replace('(y)', 'y');
    return { q: '求直線 ' + T(lineTex(a, b, c)) + ' 被圓 ' + T(std) + ' 所截的弦長。',
             a: T(String(chord)) + '（圓心到直線距離 ' + T('d=' + d) + '）',
             h: '先算弦心距（圓心 ' + T(ptTex(h, k)) + ' 到直線的距離）$d=\\dfrac{\\left|' + hsub(a, b, c, h, k) + '\\right|}{\\sqrt{' + hpz(a) + '^2+' + hpz(b) + '^2}}$；再用「半弦長、$d$、$r$ 是直角三角形」：弦長 $=2\\sqrt{r^2-d^2}$，這題 $r=' + rad + '$。',
             p: { a: a, b: b, c: c, h: h, k: k, r: rad, ans: chord } };
  };

  /* 5-3 過圓上一點的切線 */
  L1.tangentAtPt = function (r) {
    var h = r.int(-4, 4), k = r.int(-4, 4);
    var off = r.pick([[3, 4, 5], [4, 3, 5], [-3, 4, 5], [4, -3, 5], [-4, -3, 5], [5, 12, 13], [12, -5, 13], [0, 3, 3], [2, 0, 2], [-1, 0, 1], [0, -4, 4]]);
    var dx = off[0], dy = off[1], rad = off[2], x0 = h + dx, y0 = k + dy;
    var line = normLine(dx, dy, -(dx * x0 + dy * y0));
    var std = '(x' + term(-h, '', false) + ')^2+(y' + term(-k, '', false) + ')^2=' + rad * rad;
    std = std.replace('(x)', 'x').replace('(y)', 'y');
    var hh = dx === 0
      ? '切線垂直於半徑 $\\overline{CP}$（$C$ 是圓心 ' + T(ptTex(h, k)) + '）。這題 $C$ 與 $P$ 的 $x$ 坐標都是 $' + h + '$，半徑是鉛直的，所以切線是水平線，只要看 $P$ 的 $y$ 坐標。'
      : (dy === 0
        ? '切線垂直於半徑 $\\overline{CP}$（$C$ 是圓心 ' + T(ptTex(h, k)) + '）。這題 $C$ 與 $P$ 的 $y$ 坐標都是 $' + k + '$，半徑是水平的，所以切線是鉛直線，只要看 $P$ 的 $x$ 坐標。'
        : '切線垂直於半徑 $\\overline{CP}$（$C$ 是圓心 ' + T(ptTex(h, k)) + '）：先算 $\\overline{CP}$ 的斜率 $=\\dfrac{' + hdif(y0, k) + '}{' + hdif(x0, h) + '}$，切線的斜率與它相乘要等於 $-1$，再用點斜式過 ' + T('P' + ptTex(x0, y0)) + '。');
    return { q: '求圓 ' + T(std) + ' 在圓上一點 ' + T('P' + ptTex(x0, y0)) + ' 處的切線方程式。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: hh,
             p: { h: h, k: k, r: rad, x0: x0, y0: y0, ans: line } };
  };

  /* 5-4 切線長 */
  L1.tangentLen = function (r) {
    var h = r.int(-3, 3), k = r.int(-3, 3), rad = r.int(1, 6), dx, dy, s;
    do { dx = r.int(-9, 9); dy = r.int(-9, 9); s = dx * dx + dy * dy - rad * rad; } while (s <= 0);
    var x0 = h + dx, y0 = k + dy, q = simpSqrt(s);
    var std = '(x' + term(-h, '', false) + ')^2+(y' + term(-k, '', false) + ')^2=' + rad * rad;
    std = std.replace('(x)', 'x').replace('(y)', 'y');
    return { q: '自圓外一點 ' + T('P' + ptTex(x0, y0)) + ' 作圓 ' + T(std) + ' 的切線，切點為 ' + T('T') + '，求切線長 ' + T('\\overline{PT}') + '。',
             a: T('\\overline{PT}=' + sqrtTex(s)),
             h: '$\\triangle PTC$ 是直角三角形（$C$ 是圓心 ' + T(ptTex(h, k)) + '），切線長 $=\\sqrt{\\overline{PC}^2-r^2}$。這題 $\\overline{PC}^2=\\left(' + hdif(x0, h) + '\\right)^2+\\left(' + hdif(y0, k) + '\\right)^2$、$r^2=' + rad + '^2$，相減後開根號再化簡。',
             p: { h: h, k: k, r: rad, x0: x0, y0: y0, ans: [q.c, q.r] } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};
  function stdTex(h, k, r2) {
    var s = '(x' + term(-h, '', false) + ')^2+(y' + term(-k, '', false) + ')^2=' + r2;
    return s.replace('(x)', 'x').replace('(y)', 'y');
  }
  function genTex(d, e, f) { return 'x^2+y^2' + term(d, 'x', false) + term(e, 'y', false) + term(f, '', false) + '=0'; }

  /* 2-1 直線族恆過定點 */
  L2.lineFamily = function (r) {
    var x0 = r.int(-4, 4), y0 = r.int(-4, 4), a1, b1, a2, b2;
    do { a1 = r.int(-3, 3); b1 = r.int(-3, 3); a2 = r.int(-3, 3); b2 = r.int(-3, 3); }
    while ((a1 === 0 && b1 === 0) || (a2 === 0 && b2 === 0) || a1 * b2 - a2 * b1 === 0);
    if (a2 < 0 || (a2 === 0 && a1 < 0)) { a1 = -a1; b1 = -b1; a2 = -a2; b2 = -b2; }
    var c1 = -(a1 * x0 + b1 * y0), c2 = -(a2 * x0 + b2 * y0);
    /* (a1 + a2 k) x + (b1 + b2 k) y + (c1 + c2 k) = 0 */
    var s = kterm(a1, a2, 'x', true);
    s += kterm(b1, b2, 'y', s === '');
    var ct = kcoef(c1, c2);
    if (ct !== '') s += (s === '' ? '' : (ct.charAt(0) === '-' ? '' : '+')) + ct;
    var grp = function (A, B, C) { var g = term(A, 'x', true); g += term(B, 'y', g === ''); g += term(C, '', g === ''); return g === '' ? '0' : g; };
    return { q: '設 ' + T('k') + ' 為任意實數，證明直線 ' + T(s + '=0') + ' 恆過一定點，並求此定點。',
             a: T(ptTex(x0, y0)),
             h: '把含 $k$ 與不含 $k$ 的部分分開整理：原式 $=\\left(' + grp(a1, b1, c1) + '\\right)+k\\left(' + grp(a2, b2, c2) + '\\right)=0$。要讓「不管 $k$ 是多少都成立」，兩個括號必須同時為 $0$，把這兩個方程式聯立就得到定點。',
             p: { a1: a1, b1: b1, c1: c1, a2: a2, b2: b2, c2: c2, ans: [x0, y0] } };
  };

  /* 2-2 三直線不能圍成三角形 */
  L2.threeLines = function (r) {
    var x0 = r.nz(-3, 3), y0 = r.int(-3, 3), a1, a2, b3 = r.pick([1, 1, 2, 3]), k0;
    do { a1 = r.nz(-3, 3); a2 = r.nz(-3, 3); } while (a1 === a2);
    do { k0 = r.int(-6, 6); } while (k0 === a1 * b3 || k0 === a2 * b3);
    var c1 = -(a1 * x0 + y0), c2 = -(a2 * x0 + y0), c3 = -(k0 * x0 + b3 * y0);
    var L3 = kterm(0, 1, 'x', true) + term(b3, 'y', false) + term(c3, '', false) + '=0';
    var ks = [a1 * b3, a2 * b3, k0].sort(function (u, v) { return u - v; });
    var n1 = normLine(a1, 1, c1), n2 = normLine(a2, 1, c2);
    return { q: '若三直線 ' + T('L_1:' + lineTex(a1, 1, c1)) + '、' + T('L_2:' + lineTex(a2, 1, c2)) + '、' + T('L_3:' + L3) + ' 無法圍成三角形，求所有可能的實數 ' + T('k') + '。',
             a: T('k=' + ks.join(',\\ ')),
             h: '「圍不成三角形」有三種情形：$L_3\\parallel L_1$、$L_3\\parallel L_2$、或 $L_3$ 通過 $L_1$ 與 $L_2$ 的交點。$L_3$ 的 $x,y$ 係數是 $\\left(k,\\ ' + b3 + '\\right)$、$L_1$ 是 $\\left(' + n1[0] + ',\\ ' + hpz(n1[1]) + '\\right)$、$L_2$ 是 $\\left(' + n2[0] + ',\\ ' + hpz(n2[1]) + '\\right)$：平行就是兩組係數成比例（交叉相乘）各解出一個 $k$；第三種先把 $L_1$、$L_2$ 聯立求交點再代進 $L_3$。',
             p: { a1: a1, c1: c1, a2: a2, c2: c2, b3: b3, c3: c3, ans: ks } };
  };

  /* 2-3 與兩正半軸圍成三角形的最小面積 */
  L2.minArea = function (r) {
    var a = r.int(1, 8), b = r.int(1, 8), t = r.int(0, 2);
    var line = normLine(b, a, -2 * a * b);
    var sq = simpSqrt(4 * a * b);                       /* OA+OB 最小值 = a+b+2√(ab) = a+b+sq.c√sq.r */
    var sumTex = (sq.r === 1) ? String(a + b + sq.c) : (a + b) + '+' + sqrtTex(4 * a * b);
    var head = '過點 ' + T('P' + ptTex(a, b)) + ' 的直線與 ' + T('x') + '、' + T('y') + ' 軸的正向分別交於 ' + T('A,B') + '，';
    var pp = { a: a, b: b, t: t, ans: [2 * a * b].concat(line), sum: [a + b, sq.c, sq.r], A: [2 * a, 0], B: [0, 2 * b] };
    if (t === 1) {
      return { q: head + '求 ' + T('\\overline{OA}+\\overline{OB}') + ' 的最小值。',
               a: '最小值 ' + T(sumTex),
               h: '設截距式 $\\dfrac{x}{p}+\\dfrac{y}{q}=1$（$p,q\\gt 0$），代入 $P$ 得 $\\dfrac{' + a + '}{p}+\\dfrac{' + b + '}{q}=1$。要求 $p+q$ 的最小值，可以把它寫成 $p+q=(p+q)\\left(\\dfrac{' + a + '}{p}+\\dfrac{' + b + '}{q}\\right)$ 展開，再對兩個交叉項用算幾不等式。',
               p: pp };
    }
    if (t === 2) {
      return { q: head + '當 ' + T('\\triangle OAB') + ' 的面積最小時，求 ' + T('A') + '、' + T('B') + ' 兩點的坐標。',
               a: T('A' + ptTex(2 * a, 0)) + '、' + T('B' + ptTex(0, 2 * b)),
               h: '設截距式 $\\dfrac{x}{p}+\\dfrac{y}{q}=1$（$p,q\\gt 0$），代入 $P$ 得 $\\dfrac{' + a + '}{p}+\\dfrac{' + b + '}{q}=1$，面積 $=\\dfrac{pq}{2}$。由算幾不等式 $1\\ge 2\\sqrt{\\dfrac{' + a * b + '}{pq}}$ 可得 $pq$ 的下界，等號成立在 $\\dfrac{' + a + '}{p}=\\dfrac{' + b + '}{q}$ 時，解出 $p,q$ 就是 $A$、$B$ 的坐標。',
               p: pp };
    }
    return { q: head + '求 ' + T('\\triangle OAB') + ' 面積的最小值，以及此時的直線方程式。',
             a: '最小面積 ' + T(String(2 * a * b)) + '，直線 ' + T(lineTex(line[0], line[1], line[2])),
             h: '設截距式 $\\dfrac{x}{p}+\\dfrac{y}{q}=1$（$p,q\\gt 0$），代入 $P$ 得 $\\dfrac{' + a + '}{p}+\\dfrac{' + b + '}{q}=1$，面積 $=\\dfrac{pq}{2}$。對左邊用算幾不等式 $1=\\dfrac{' + a + '}{p}+\\dfrac{' + b + '}{q}\\ge 2\\sqrt{\\dfrac{' + a * b + '}{pq}}$ 反推 $pq$ 的下界，等號成立在 $\\dfrac{' + a + '}{p}=\\dfrac{' + b + '}{q}$ 時。',
             p: pp };
  };

  /* 2-4 點對直線的對稱點 */
  L2.reflectPt = function (r) {
    var nv = r.pick([[1, 1], [1, -1], [3, 4], [4, 3], [1, 2], [2, 1], [1, 3], [3, 1], [2, -1], [1, -2], [3, -4], [4, -3]]);
    var a = nv[0], b = nv[1], x0 = r.int(-5, 5), y0 = r.int(-5, 5), t = r.pick([-2, -1, 1, 2]);
    var c = t * (a * a + b * b) - a * x0 - b * y0;
    var xp = x0 - 2 * t * a, yp = y0 - 2 * t * b;
    return { q: '求點 ' + T('P' + ptTex(x0, y0)) + ' 對直線 ' + T('L:' + lineTex(a, b, c)) + ' 的對稱點 ' + T("P'") + '。',
             a: T("P'" + ptTex(xp, yp)),
             h: '設 $P\'(x,\\ y)$，兩個條件同時列出來：① $\\overline{PP\'}$ 的中點 $\\left(\\dfrac{x' + term(x0, '', false) + '}{2},\\ \\dfrac{y' + term(y0, '', false) + '}{2}\\right)$ 要落在 $L$ 上（代進 $L$ 的方程式）；② $\\overline{PP\'}\\perp L$，$L$ 的斜率是 $' + Fr.tex(F(-a, b), true) + '$，所以 $\\overline{PP\'}$ 的斜率與它相乘要等於 $-1$。兩式聯立解出 $x,y$。',
             p: { a: a, b: b, c: c, x0: x0, y0: y0, ans: [xp, yp] } };
  };

  /* 2-5 反射最短路徑 */
  L2.shortestPath = function (r) {
    var t = r.int(0, 2);   /* 0: x 軸  1: y 軸  2: y=x */
    if (t < 2) {
      var y1 = r.int(1, 5), y2 = r.int(1, 5), n = r.pick([-2, -1, 1, 2]), x1 = r.int(-4, 4);
      var x2 = x1 + n * (y1 + y2), px = x1 + n * y1;
      var s = n * n + 1, sum = y1 + y2;
      var minv = distSimp(sum * s, s);            /* (y1+y2)√(n²+1) */
      var A = t === 0 ? [x1, y1] : [y1, x1], B = t === 0 ? [x2, y2] : [y2, x2], P = t === 0 ? [px, 0] : [0, px];
      var A2 = t === 0 ? [A[0], -A[1]] : [-A[0], A[1]];
      return { q: '已知 ' + T('A' + ptTex(A[0], A[1])) + '、' + T('B' + ptTex(B[0], B[1])) + '，點 ' + T('P') + ' 在 ' + (t === 0 ? '$x$ 軸' : '$y$ 軸') + ' 上，求 ' + T('\\overline{PA}+\\overline{PB}') + ' 的最小值，以及此時 ' + T('P') + ' 的坐標。',
               a: '最小值 ' + T(minv.tex) + '，' + T('P' + ptTex(P[0], P[1])),
               h: '鏡射法：$A$、$B$ 在' + (t === 0 ? '$x$ 軸' : '$y$ 軸') + '的同一側，把 $A$ 鏡射過去變成 $A\'' + ptTex(A2[0], A2[1] ) + '$（' + (t === 0 ? '$y$' : '$x$') + ' 坐標變號）。此時 $\\overline{PA}+\\overline{PB}=\\overline{PA\'}+\\overline{PB}\\ge\\overline{A\'B}$，最小值就是 $\\overline{A\'B}$，而 $P$ 是 $\\overline{A\'B}$ 與該軸的交點。',
               p: { t: t, A: A, B: B, ans: [minv.n, minv.d, minv.r, P[0], P[1]] } };
    }
    var ax = r.int(-3, 5), ay, bx, by;
    do { ay = r.int(-3, 5); } while (ay === ax);
    do { bx = r.int(-3, 5); by = r.int(-3, 5); } while ((by - bx) * (ay - ax) <= 0 || (bx === ax && by === ay));
    /* A' = (ay, ax) */
    var d2 = (bx - ay) * (bx - ay) + (by - ax) * (by - ax), q = simpSqrt(d2);
    /* 交點：A'(ay,ax)→B，與 y=x：參數 s，ay + s(bx-ay) = ax + s(by-ax) */
    var num = ax - ay, den = (bx - ay) - (by - ax);
    var sF = F(num, den);
    var Px = Fr.add(F(ay, 1), Fr.mul(sF, F(bx - ay, 1)));
    return { q: '已知 ' + T('A' + ptTex(ax, ay)) + '、' + T('B' + ptTex(bx, by)) + '，點 ' + T('P') + ' 在直線 ' + T('y=x') + ' 上，求 ' + T('\\overline{PA}+\\overline{PB}') + ' 的最小值，以及此時 ' + T('P') + ' 的坐標。',
             a: '最小值 ' + T(sqrtTex(d2)) + '，' + T('P' + fptTex(Px, Px)),
             h: '鏡射法：點對 $y=x$ 的鏡射就是把兩個坐標互換，所以 $A\'' + ptTex(ay, ax) + '$。最小值 $=\\overline{A\'B}=\\sqrt{\\left(' + hdif(bx, ay) + '\\right)^2+\\left(' + hdif(by, ax) + '\\right)^2}$，$P$ 則是直線 $A\'B$ 與 $y=x$ 的交點。',
             p: { t: 2, A: [ax, ay], B: [bx, by], ans: [q.c, q.r, Px.n, Px.d] } };
  };

  /* 2-6 直線上與兩定點等距的點 */
  L2.eqDistOnLine = function (r) {
    var x0 = r.int(-4, 4), y0 = r.int(-4, 4), a, b;
    do { a = r.int(-3, 3); b = r.int(-3, 3); } while (a === 0 && b === 0);
    var c = -(a * x0 + b * y0);
    var group = r.pick([
      [[3, 4], [4, 3], [-3, 4], [4, -3], [5, 0], [0, 5], [-5, 0], [0, -5], [3, -4], [-4, -3], [-3, -4], [-4, 3]],
      [[1, 2], [2, 1], [-1, 2], [2, -1], [1, -2], [-2, 1], [-1, -2], [-2, -1]],
      [[2, 2], [2, -2], [-2, 2], [-2, -2]], [[1, 3], [3, 1], [-1, 3], [3, -1], [-3, 1], [1, -3]]]);
    var offs = r.shuffle(group), A = null, B = null;
    /* 避免 A、B 的中垂線與 L 平行（中垂線法向量 = B-A 需不平行於 L 的法向量 (a,b)） */
    for (var i = 0; i < offs.length && B === null; i++) for (var j = i + 1; j < offs.length; j++) {
      var nx = offs[j][0] - offs[i][0], ny = offs[j][1] - offs[i][1];
      if (a * ny - b * nx !== 0) { A = [x0 + offs[i][0], y0 + offs[i][1]]; B = [x0 + offs[j][0], y0 + offs[j][1]]; break; }
    }
    return { q: '在直線 ' + T('L:' + lineTex(a, b, c)) + ' 上求一點 ' + T('P') + '，使 ' + T('\\overline{PA}=\\overline{PB}') + '，其中 ' + T('A' + ptTex(A[0], A[1])) + '、' + T('B' + ptTex(B[0], B[1])) + '。',
             a: T('P' + ptTex(x0, y0)),
             h: '與兩點等距的點都落在 $\\overline{AB}$ 的中垂線上。這題 $\\overline{AB}$ 的中點是 $\\left(\\dfrac{' + hpz(A[0]) + '+' + hpz(B[0]) + '}{2},\\ \\dfrac{' + hpz(A[1]) + '+' + hpz(B[1]) + '}{2}\\right)$，$\\overline{AB}$ 的斜率 $=\\dfrac{' + hpz(B[1]) + '-' + hpz(A[1]) + '}{' + hpz(B[0]) + '-' + hpz(A[0]) + '}$（分母為 $0$ 就是鉛直線，中垂線改成水平線）；中垂線的斜率與它相乘要等於 $-1$。寫出中垂線後再與 $L$ 聯立求兩線的交點。',
             p: { a: a, b: b, c: c, A: A, B: B, ans: [x0, y0] } };
  };

  /* 3-1 線性規劃（給不等式組） */
  function triSystem(r) {
    var V, twice;
    do {
      V = [[r.int(-3, 6), r.int(-3, 6)], [r.int(-3, 6), r.int(-3, 6)], [r.int(-3, 6), r.int(-3, 6)]];
      twice = (V[1][0] - V[0][0]) * (V[2][1] - V[0][1]) - (V[2][0] - V[0][0]) * (V[1][1] - V[0][1]);
    } while (Math.abs(twice) < 6);
    var rows = [], ineqs = [];
    for (var i = 0; i < 3; i++) {
      var P = V[i], Q = V[(i + 1) % 3], R = V[(i + 2) % 3];
      var a = Q[1] - P[1], b = -(Q[0] - P[0]), c = -(a * P[0] + b * P[1]);
      var n = normLine(a, b, c); a = n[0]; b = n[1]; c = n[2];
      var sgn = a * R[0] + b * R[1] + c > 0 ? 1 : -1;   /* 區域在使 ax+by+c 同號的一側 */
      var lhs = lineTex(a, b, c).replace('=0', '');
      rows.push(lhs + (sgn > 0 ? '\\ge0' : '\\le0'));
      ineqs.push([a, b, c, sgn]);
    }
    return { V: V, twice: Math.abs(twice), tex: '\\begin{cases}' + rows.join('\\\\ ') + '\\end{cases}', ineqs: ineqs };
  }
  L2.lpOpt = function (r) {
    var S, p, q, vals;
    do {
      S = triSystem(r); p = r.nz(-4, 4); q = r.nz(-4, 4);
      vals = S.V.map(function (v) { return p * v[0] + q * v[1]; });
    } while (vals[0] === vals[1] || vals[1] === vals[2] || vals[0] === vals[2]);
    var mx = Math.max.apply(null, vals), mn = Math.min.apply(null, vals), im = vals.indexOf(mx), imn = vals.indexOf(mn);
    var f = term(p, 'x', true) + term(q, 'y', false);
    var ls = S.ineqs.map(function (g) { return T(lineTex(g[0], g[1], g[2])); }).join('、');
    return { q: '設 ' + T('(x,y)') + ' 滿足 ' + T(S.tex) + '，求 ' + T('f=' + f) + ' 的最大值與最小值。',
             a: '最大值 ' + T(String(mx)) + '（在 ' + T(ptTex(S.V[im][0], S.V[im][1])) + '），最小值 ' + T(String(mn)) + '（在 ' + T(ptTex(S.V[imn][0], S.V[imn][1])) + '）',
             h: '先把三個不等式的等號部分看成三條直線 ' + ls + '，兩兩聯立求出三個頂點（求完記得檢查它有沒有滿足第三個不等式）；再把每個頂點代入 $f=' + f + '$ 比大小，最大最小一定出現在頂點。',
             p: { ineqs: S.ineqs, V: S.V, p: p, q: q, ans: [mx, mn] } };
  };

  /* 3-2 區域面積 */
  L2.regionArea = function (r) {
    var S = triSystem(r), A = F(S.twice, 2);
    var ls = S.ineqs.map(function (g) { return T(lineTex(g[0], g[1], g[2])); }).join('、');
    return { q: '求聯立不等式 ' + T(S.tex) + ' 所表示區域的面積。',
             a: T(Fr.tex(A)),
             h: '這個區域是三角形。先把三個不等式的等號部分看成三條直線 ' + ls + '，兩兩聯立得三個頂點，再用坐標面積公式 $\\dfrac12\\left|x_1(y_2-y_3)+x_2(y_3-y_1)+x_3(y_1-y_2)\\right|$。',
             p: { ineqs: S.ineqs, V: S.V, ans: [A.n, A.d] } };
  };

  /* 3-3 格子點計數 */
  L2.latticeCount = function (r) {
    var a = r.int(1, 3), b = r.int(1, 3), c = r.int(6, 14), cnt = 0;
    for (var x = 0; a * x <= c; x++) cnt += Math.floor((c - a * x) / b) + 1;
    var lhs = term(a, 'x', true) + term(b, 'y', false);
    return { q: '求滿足 ' + T('\\begin{cases}x\\ge0\\\\ y\\ge0\\\\ ' + lhs + '\\le' + c + '\\end{cases}') + ' 的格子點（' + T('x,y') + ' 皆為整數）個數。',
             a: T(String(cnt)) + ' 個',
             h: '固定 $x$ 逐行數：由 ' + T(term(a, 'x', true) + '\\le' + c) + ' 知 $x$ 只能取 $0$ 到 $\\dfrac{' + c + '}{' + a + '}$ 的整數部分。固定一個 $x$ 之後，$y$ 要滿足 $0\\le y\\le\\dfrac{' + c + '-' + (a === 1 ? '' : a) + 'x}{' + b + '}$，個數是它的整數部分再 $+1$；把每一行的個數加起來。',
             p: { a: a, b: b, c: c, ans: cnt } };
  };

  /* 4-1 含參數圓的條件 */
  L2.circParam = function (r) {
    var b = r.nz(-4, 4), m = r.int(1, 5), f = b * b - m * m, sg = r.sign();
    var eq = 'x^2+y^2' + (sg > 0 ? '+2kx' : '-2kx') + term(2 * b, 'y', false) + '+2k^2' + term(f, '', false) + '=0';
    return { q: '設 ' + T('k') + ' 為實數，若方程式 ' + T(eq) + ' 的圖形是一個圓，求 ' + T('k') + ' 的範圍，並求此圓半徑的最大值。',
             a: T('-' + m + '\\lt k\\lt' + m) + '，半徑最大值 ' + T(String(m)) + '（' + T('k=0') + ' 時）',
             h: '對 $x$ 與 $y$ 各自配方：$\\left(x' + (sg > 0 ? '+k' : '-k') + '\\right)^2+\\left(y' + term(b, '', false) + '\\right)^2=$ 右邊，而右邊 $=k^2+' + hpz(b) + '^2-\\left(2k^2' + term(f, '', false) + '\\right)$。是圓 $\\iff$ 右邊 $\\gt 0$，解這個關於 $k$ 的不等式；右邊就是 $r^2$，所以 $k^2$ 愈小半徑愈大。',
             p: { b: b, f: f, sg: sg, ans: m } };
  };

  /* 4-2 過三點的圓 */
  L2.circ3pt = function (r) {
    var h = r.int(-4, 4), k = r.int(-4, 4), sc = r.pick([1, 1, 2]), rad = 5 * sc;
    var offs = r.shuffle([[3, 4], [4, 3], [-3, 4], [-4, 3], [3, -4], [4, -3], [-3, -4], [-4, -3], [5, 0], [-5, 0], [0, 5], [0, -5]]).slice(0, 3);
    var P = offs.map(function (o) { return [h + o[0] * sc, k + o[1] * sc]; });
    var d = -2 * h, e = -2 * k, f = h * h + k * k - rad * rad;
    return { q: '求過 ' + T('A' + ptTex(P[0][0], P[0][1])) + '、' + T('B' + ptTex(P[1][0], P[1][1])) + '、' + T('C' + ptTex(P[2][0], P[2][1])) + ' 三點的圓方程式。',
             a: T(stdTex(h, k, rad * rad)) + '，即 ' + T(genTex(d, e, f)),
             h: '設圓為 $x^2+y^2+dx+ey+f=0$，三點各代一次得到三個式子。例如 $A$ 代入是 $\\left(' + hpz(P[0][0]) + '\\right)^2+\\left(' + hpz(P[0][1]) + '\\right)^2' + term(P[0][0], 'd', false) + term(P[0][1], 'e', false) + '+f=0$，$B$、$C$ 同理；三式兩兩相減可以消掉 $f$，剩下 $d,e$ 的二元一次方程組。（也可以改用兩條中垂線的交點求圓心。）',
             p: { P: P, ans: [h, k, rad] } };
  };

  /* 4-3 圓心在直線上且過兩點 */
  L2.circCenterOnLine = function (r) {
    var h = r.int(-4, 4), k = r.int(-4, 4), a, b;
    do { a = r.int(-3, 3); b = r.int(-3, 3); } while (a === 0 && b === 0);
    var c = -(a * h + b * k), sc = r.pick([1, 1, 2]), rad = 5 * sc;
    var offs = r.shuffle([[3, 4], [4, 3], [-3, 4], [-4, 3], [3, -4], [4, -3], [-3, -4], [-4, -3], [5, 0], [-5, 0], [0, 5], [0, -5]]);
    var A = [h + offs[0][0] * sc, k + offs[0][1] * sc], B = [h + offs[1][0] * sc, k + offs[1][1] * sc];
    /* 避免 AB 中垂線與 L 平行（無解／無限多解） */
    var nx = B[0] - A[0], ny = B[1] - A[1];
    if (a * ny - b * nx === 0) { B = [h + offs[2][0] * sc, k + offs[2][1] * sc]; }
    return { q: '圓 ' + T('C') + ' 的圓心在直線 ' + T('L:' + lineTex(a, b, c)) + ' 上，且通過 ' + T('A' + ptTex(A[0], A[1])) + '、' + T('B' + ptTex(B[0], B[1])) + ' 兩點，求圓 ' + T('C') + ' 的方程式。',
             a: T(stdTex(h, k, rad * rad)),
             h: '圓心到 $A$、$B$ 等距，所以圓心同時在 $\\overline{AB}$ 的中垂線上與 $L$ 上。這題 $\\overline{AB}$ 的中點是 $\\left(\\dfrac{' + hpz(A[0]) + '+' + hpz(B[0]) + '}{2},\\ \\dfrac{' + hpz(A[1]) + '+' + hpz(B[1]) + '}{2}\\right)$，$\\overline{AB}$ 的斜率 $=\\dfrac{' + hpz(B[1]) + '-' + hpz(A[1]) + '}{' + hpz(B[0]) + '-' + hpz(A[0]) + '}$（分母為 $0$ 時 $\\overline{AB}$ 是鉛直線，中垂線就是水平線），中垂線的斜率與它相乘要等於 $-1$；兩線聯立得圓心後，半徑用 $\\overline{CA}$ 算。',
             p: { a: a, b: b, c: c, A: A, B: B, ans: [h, k, rad] } };
  };

  /* 4-4 圓心已知、與直線相切 */
  L2.circTangentLine = function (r) {
    var nv = r.pick([[3, 4], [4, 3], [3, -4], [4, -3], [5, 12], [12, 5]]);
    var a = nv[0], b = nv[1], s = a * a + b * b, sq = Math.sqrt(s), h = r.int(-5, 5), k = r.int(-5, 5), rad = r.int(1, 6);
    var c = rad * sq * r.sign() - a * h - b * k;
    return { q: '求圓心為 ' + T(ptTex(h, k)) + ' 且與直線 ' + T(lineTex(a, b, c)) + ' 相切的圓方程式。',
             a: T(stdTex(h, k, rad * rad)),
             h: '相切 $\\iff$ 半徑等於圓心到直線的距離：$r=\\dfrac{\\left|' + hsub(a, b, c, h, k) + '\\right|}{\\sqrt{' + a + '^2+' + hpz(b) + '^2}}$。算出 $r$ 之後代進標準式 $\\left(' + hmn('x', h) + '\\right)^2+\\left(' + hmn('y', k) + '\\right)^2=r^2$。',
             p: { a: a, b: b, c: c, h: h, k: k, ans: rad } };
  };

  /* 5-1 過圓外一點的切線（兩條） */
  L2.tangentExt = function (r) {
    var h = r.int(-3, 3), k = r.int(-3, 3), rad = r.int(1, 4), m;
    do { m = r.int(-6, 6); } while (m === 0 || Math.abs(m) === rad);
    var t = r.int(0, 3), P, l1, sl;
    if (t === 0) { P = [h + rad, k + m]; l1 = [1, 0, -(h + rad)]; sl = F(m * m - rad * rad, 2 * rad * m); }
    else if (t === 1) { P = [h - rad, k + m]; l1 = [1, 0, -(h - rad)]; sl = F(-(m * m - rad * rad), 2 * rad * m); }
    else if (t === 2) { P = [h + m, k + rad]; l1 = [0, 1, -(k + rad)]; sl = F(2 * rad * m, m * m - rad * rad); }
    else { P = [h + m, k - rad]; l1 = [0, 1, -(k - rad)]; sl = F(-2 * rad * m, m * m - rad * rad); }
    /* 第二條：斜率 sl.n/sl.d，過 P：sl.n (x-Px) - sl.d (y-Py) = 0 */
    var l2 = normLine(sl.n, -sl.d, -(sl.n * P[0] - sl.d * P[1]));
    var chk = t < 2
      ? '先檢查沒有斜率的那一條：圓心到鉛直線 $x=' + P[0] + '$ 的距離是 $\\left|' + hpz(h) + '-' + hpz(P[0]) + '\\right|$，和 $r=' + rad + '$ 比一下就知道它算不算切線'
      : '先檢查水平的那一條：圓心到 $y=' + P[1] + '$ 的距離是 $\\left|' + hpz(k) + '-' + hpz(P[1]) + '\\right|$，和 $r=' + rad + '$ 比一下就知道它算不算切線';
    return { q: '求過點 ' + T('P' + ptTex(P[0], P[1])) + ' 且與圓 ' + T(stdTex(h, k, rad * rad)) + ' 相切的直線方程式（兩條都要）。',
             a: T(lineTex(l1[0], l1[1], l1[2])) + ' 與 ' + T(lineTex(l2[0], l2[1], l2[2])),
             h: chk + '。另一條設 $' + hmn('y', P[1]) + '=m\\left(' + hmn('x', P[0]) + '\\right)$，化成 $mx-y+\\left(' + (term(P[1], '', true) + term(-P[0], 'm', P[1] === 0) || '0') + '\\right)=0$ 後，令圓心 ' + T(ptTex(h, k)) + ' 到它的距離 $=' + rad + '$ 解出 $m$；<b>用斜率設的方法會漏掉鉛直線，所以前面那一步不能跳過</b>。',
             p: { h: h, k: k, r: rad, P: P, ans: [l1, l2] } };
  };

  /* 5-2 已知弦長反求參數 */
  L2.chordParam = function (r) {
    var pair = r.pick([[5, 3, 8], [5, 4, 6], [10, 6, 16], [10, 8, 12], [13, 5, 24], [13, 12, 10]]);
    var rad = pair[0], d = pair[1], chord = pair[2], h = r.int(-4, 4), k = r.int(-4, 4);
    var nv = r.pick([[3, 4], [4, 3], [3, -4], [4, -3]]), a = nv[0], b = nv[1];
    var base = a * h + b * k, c1 = base + 5 * d, c2 = base - 5 * d;
    var lhs = term(a, 'x', true) + term(b, 'y', false);
    return { q: '若直線 ' + T(lhs + '=c') + ' 與圓 ' + T(stdTex(h, k, rad * rad)) + ' 相交所得的弦長為 ' + T(String(chord)) + '，求實數 ' + T('c') + '。',
             a: T('c=' + Math.min(c1, c2) + '\\ \\text{或}\\ ' + Math.max(c1, c2)),
             h: '先用「半弦長、弦心距、半徑」的直角三角形反求弦心距 $d$：$\\left(\\dfrac{' + chord + '}{2}\\right)^2+d^2=' + rad + '^2$。再讓圓心 ' + T(ptTex(h, k)) + ' 到直線的距離等於 $d$：$\\dfrac{\\left|' + hsub(a, b, 0, h, k) + '-c\\right|}{\\sqrt{' + a + '^2+' + hpz(b) + '^2}}=d$，絕對值拆成兩種情形，所以 $c$ 有兩個答案。',
             p: { a: a, b: b, h: h, k: k, r: rad, chord: chord, ans: [Math.min(c1, c2), Math.max(c1, c2)] } };
  };

  /* 5-3 圓上動點到定點／直線的最遠最近 */
  L2.circMinMax = function (r) {
    var h = r.int(-4, 4), k = r.int(-4, 4), rad = r.int(1, 4), t = r.int(0, 1);
    if (t === 0) {
      var off = r.pick([[3, 4], [4, 3], [-3, 4], [-4, 3], [3, -4], [-4, -3], [6, 8], [-6, 8], [5, 12], [12, -5]]);
      var D = Math.round(Math.sqrt(off[0] * off[0] + off[1] * off[1]));
      if (D <= rad) rad = D - 1;
      var Q = [h + off[0], k + off[1]];
      return { q: '設 ' + T('P') + ' 為圓 ' + T(stdTex(h, k, rad * rad)) + ' 上的動點，' + T('Q' + ptTex(Q[0], Q[1])) + '，求 ' + T('\\overline{PQ}') + ' 的最大值與最小值。',
               a: '最大值 ' + T(String(D + rad)) + '，最小值 ' + T(String(D - rad)),
               h: '先算 $Q$ 到圓心 ' + T(ptTex(h, k)) + ' 的距離 $\\overline{QC}=\\sqrt{\\left(' + hdif(Q[0], h) + '\\right)^2+\\left(' + hdif(Q[1], k) + '\\right)^2}$，確認 $Q$ 在圓外（$\\overline{QC}\\gt r=' + rad + '$）。最遠、最近都發生在「$Q$、圓心、$P$ 共線」時：最遠 $=\\overline{QC}+r$、最近 $=\\overline{QC}-r$。',
               p: { t: 0, h: h, k: k, r: rad, Q: Q, ans: [D + rad, D - rad] } };
    }
    var nv = r.pick([[3, 4], [4, 3], [3, -4], [4, -3]]), a = nv[0], b = nv[1], dd = rad + r.int(1, 6);
    var c = 5 * dd * r.sign() - a * h - b * k;
    return { q: '設 ' + T('P') + ' 為圓 ' + T(stdTex(h, k, rad * rad)) + ' 上的動點，求 ' + T('P') + ' 到直線 ' + T(lineTex(a, b, c)) + ' 的最大距離與最小距離。',
             a: '最大 ' + T(String(dd + rad)) + '，最小 ' + T(String(dd - rad)),
             h: '先算圓心 ' + T(ptTex(h, k)) + ' 到直線的距離 $d=\\dfrac{\\left|' + hsub(a, b, c, h, k) + '\\right|}{\\sqrt{' + a + '^2+' + hpz(b) + '^2}}$，確認 $d\\gt r=' + rad + '$（相離）。沿著「過圓心的垂線」看，最遠 $=d+r$、最近 $=d-r$。',
             p: { t: 1, h: h, k: k, r: rad, a: a, b: b, c: c, ans: [dd + rad, dd - rad] } };
  };

  /* 5-4 直線與圓相交／相切的參數範圍 */
  L2.circLinePosParam = function (r) {
    var nv = r.pick([[3, 4], [4, 3], [3, -4], [4, -3]]), a = nv[0], b = nv[1], h = r.int(-4, 4), k = r.int(-4, 4), rad = r.int(1, 5);
    var base = a * h + b * k, lo = base - 5 * rad, hi = base + 5 * rad;
    var lhs = term(a, 'x', true) + term(b, 'y', false);
    return { q: '直線 ' + T(lhs + '=c') + ' 與圓 ' + T(stdTex(h, k, rad * rad)) + ' 相交於相異兩點，求實數 ' + T('c') + ' 的範圍；並求相切時的 ' + T('c') + ' 值。',
             a: '相交：' + T(lo + '\\lt c\\lt' + hi) + '；相切：' + T('c=' + lo + '\\ \\text{或}\\ ' + hi),
             h: '把直線寫成 $' + lhs + '-c=0$，圓心 ' + T(ptTex(h, k)) + ' 到它的距離是 $\\dfrac{\\left|' + hsub(a, b, 0, h, k) + '-c\\right|}{\\sqrt{' + a + '^2+' + hpz(b) + '^2}}$。相交於相異兩點 $\\iff$ 這個距離 $\\lt r=' + rad + '$，也就是解 $\\left|' + hsub(a, b, 0, h, k) + '-c\\right|\\lt ' + (5 * rad) + '$；相切則是等號。',
             p: { a: a, b: b, h: h, k: k, r: rad, ans: [lo, hi] } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p 重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     ══════════════════════════════════════════════════════════ */
  function parT(n) { return n < 0 ? '(' + n + ')' : String(n); }                 /* 負數代入時加括號 */
  function difT(u, v) { return v === 0 ? String(u) : parT(u) + '-' + parT(v); }  /* u-v 的代入寫法，不寫「-0」 */
  function mnT(sym, v) { return v === 0 ? sym : sym + '-' + parT(v); }           /* x-x0 的代入寫法 */
  function subT(A, B, C, X, Y) {                                                /* A·X+B·Y+C 的數字代入式 */
    function tm(co, v, first) {
      if (co === 0 || v === 0) return '';
      var sg = co < 0 ? '-' : (first ? '' : '+'), ab = Math.abs(co);
      return sg + (ab === 1 ? '' : ab + '\\times') + parT(v);
    }
    var s = tm(A, X, true);
    s += tm(B, Y, s === '');
    s += (C === 0 ? '' : (C < 0 ? '-' + (-C) : (s === '' ? '' : '+') + C));
    return s === '' ? '0' : s;
  }
  function lhsT(A, B, C) {                                                      /* Ax+By+C（不接 =0） */
    var s = term(A, 'x', true); s += term(B, 'y', s === ''); s += term(C, '', s === '');
    return s === '' ? '0' : s;
  }
  var L1_H1 = {
    slope2pt: '這是「兩點求斜率」：斜率就是「$y$ 的變化量」除以「$x$ 的變化量」，先把兩點的坐標對應寫成 $x_1,y_1$ 與 $x_2,y_2$。',
    dist2pt: '這是「兩點距離」：把兩點的橫坐標相減、縱坐標相減，各自平方後相加再開根號。',
    midDiv: '這是「中點與分點」：中點是兩個坐標各自取平均；有比例時改用分點公式，靠近哪一點，那一點的權重就大。',
    lineEq: '這是「點斜式化一般式」：先寫 $y-y_0=m(x-x_0)$，再去分母、把所有項移到等號左邊。',
    line2pt: '這是「兩點求直線」：先用兩點算斜率，再用其中一點寫點斜式；先檢查兩點的 $x$ 坐標是不是一樣（鉛直線沒有斜率）。',
    interceptForm: '這是「截距」：截距就是與坐標軸的交點，$x$ 截距令 $y=0$、$y$ 截距令 $x=0$；由截距寫方程式則用截距式。',
    parPerp: '這是「平行線與垂直線」：平行就把 $x,y$ 的係數照抄、只改常數；垂直就把係數對調並讓其中一個變號，最後代點求常數。',
    intersect: '這是「兩直線交點」：把兩個方程式聯立，乘上適當倍數讓某一個變數的係數相同，相減消掉它。',
    ptLineDist: '這是「點到直線的距離」：套 $d=\\dfrac{|ax_0+by_0+c|}{\\sqrt{a^2+b^2}}$，分子是把點代進左邊再取絕對值。',
    parDist: '這是「兩平行線的距離」：先把兩條的 $x,y$ 係數化成一模一樣，再用兩個常數項的差除以 $\\sqrt{a^2+b^2}$。',
    triArea: '這是「坐標三角形面積」：先把其中一個頂點平移到原點（面積不變），再用 $\\dfrac12|ad-bc|$。',
    symAxis: '這是「對稱點」：對 $x$ 軸、$y$ 軸、原點都是把坐標變號，對 $y=x$ 則是把兩個坐標互換。',
    translate: '這是「平移直線」：平移用代換，把 $x$ 換成 $x-h$、$y$ 換成 $y-k$，代換方向和移動方向相反。',
    perpBisector: '這是「中垂線」：它同時要過 $\\overline{AB}$ 的中點、又要與 $\\overline{AB}$ 垂直，所以先求中點、再處理斜率。',
    halfPlane: '這是「半平面判定」：把每個點代進不等式左邊算出正負再判斷，特別注意不等號有沒有含等號。',
    lpVertex: '這是「線性規劃（頂點代入）」：線性目標函數的最大、最小一定出現在頂點，把每個頂點代進去比大小就好。',
    circStd: '這是「由圓心半徑寫圓方程式」：先寫標準式 $(x-h)^2+(y-k)^2=r^2$，展開合併後就是一般式。',
    circGen: '這是「由一般式求圓心半徑」：對照 $x^2+y^2+dx+ey+f=0$，用配方法或直接套圓心與半徑的公式。',
    circKind: '這是「判斷圖形是圓、一點還是沒有圖形」：配方後看右邊的正負，也就是看 $d^2+e^2-4f$ 的正負。',
    ptCircle: '這是「點與圓的位置」：算點到圓心距離的平方，再和半徑的平方比大小，不必開根號。',
    lineCircPos: '這是「直線與圓的位置關係」：不要聯立，改算圓心到直線的距離 $d$，再和半徑比大小。',
    chordLen: '這是「弦長」：先算圓心到直線的距離（弦心距），再用半弦長、弦心距、半徑組成的直角三角形。',
    tangentAtPt: '這是「過圓上一點的切線」：切線與該點的半徑垂直，所以先處理半徑的斜率，再用點斜式過切點。',
    tangentLen: '這是「切線長」：切點、圓心、圓外點會形成直角三角形，用畢氏定理把切線長算出來。'
  };
  var L1_SOL = {};

  L1_SOL.slope2pt = function (p) {
    var dy = p.y2 - p.y1, dx = p.x2 - p.x1, m = F(p.ans[0], p.ans[1]);
    return ['斜率的定義是「$y$ 的變化量」除以「$x$ 的變化量」：$m=\\dfrac{y_2-y_1}{x_2-x_1}$，分子分母的「誰減誰」順序要一致。',
      '代入 $A' + ptTex(p.x1, p.y1) + '$、$B' + ptTex(p.x2, p.y2) + '$：$m=\\dfrac{' + difT(p.y2, p.y1) + '}{' + difT(p.x2, p.x1) + '}=\\dfrac{' + dy + '}{' + dx + '}$。',
      (dy === 0 ? '分子是 $0$，所以斜率為 $0$（這是一條水平線）' : (dx < 0 || gcd(dy, dx) !== 1 ? '約分（分母要化成正的）' : '分子分母已經互質，分母也是正的')) + '，所以 $m=' + Fr.tex(m) + '$。'];
  };

  L1_SOL.dist2pt = function (p) {
    var dx = p.x2 - p.x1, dy = p.y2 - p.y1, s = dx * dx + dy * dy, q = simpSqrt(s);
    return ['兩點距離公式：$\\overline{AB}=\\sqrt{(x_2-x_1)^2+(y_2-y_1)^2}$。',
      '代入：$\\overline{AB}=\\sqrt{\\left(' + difT(p.x2, p.x1) + '\\right)^2+\\left(' + difT(p.y2, p.y1) + '\\right)^2}=\\sqrt{' + (dx * dx) + '+' + (dy * dy) + '}=\\sqrt{' + s + '}$。',
      (q.r === 1 ? '$' + s + '$ 是完全平方數' : '把 $' + s + '$ 分解出平方因數 $' + (q.c * q.c) + '$ 提到根號外') + '，所以 $\\overline{AB}=' + sqrtTex(s) + '$。'];
  };

  L1_SOL.midDiv = function (p) {
    var px = F(p.ans[0], p.ans[1]), py = F(p.ans[2], p.ans[3]), m = p.m, n = p.n;
    if (m === 1 && n === 1) return [
      '中點就是兩個坐標各自取平均：$M=\\left(\\dfrac{x_1+x_2}{2},\\ \\dfrac{y_1+y_2}{2}\\right)$。',
      '代入：$M=\\left(\\dfrac{' + parT(p.x1) + '+' + parT(p.x2) + '}{2},\\ \\dfrac{' + parT(p.y1) + '+' + parT(p.y2) + '}{2}\\right)=\\left(\\dfrac{' + (p.x1 + p.x2) + '}{2},\\ \\dfrac{' + (p.y1 + p.y2) + '}{2}\\right)$。',
      '兩個分數各自約分，所以 $' + fptTex(px, py) + '$。'];
    return [
      '分點公式：$\\overline{AP}:\\overline{PB}=' + m + ':' + n + '$ 時 $P=\\dfrac{' + n + 'A+' + m + 'B}{' + (m + n) + '}$（靠近哪一點，那一點的權重就大）。',
      '橫坐標：$x_P=\\dfrac{' + n + '\\times' + parT(p.x1) + '+' + m + '\\times' + parT(p.x2) + '}{' + (m + n) + '}=\\dfrac{' + (n * p.x1 + m * p.x2) + '}{' + (m + n) + '}$。',
      '縱坐標：$y_P=\\dfrac{' + n + '\\times' + parT(p.y1) + '+' + m + '\\times' + parT(p.y2) + '}{' + (m + n) + '}=\\dfrac{' + (n * p.y1 + m * p.y2) + '}{' + (m + n) + '}$。',
      '兩個分數各自約分，所以 $' + fptTex(px, py) + '$。'];
  };

  L1_SOL.lineEq = function (p) {
    var mf = F(p.mn, p.md), L = p.ans;
    return ['已知一點與斜率，用點斜式：$y-y_0=m(x-x_0)$。',
      '代入 $(x_0,y_0)=' + ptTex(p.x0, p.y0) + '$ 與 $m=' + Fr.tex(mf, true) + '$：$' + mnT('y', p.y0) + '=' + Fr.tex(mf, true) + '\\left(' + mnT('x', p.x0) + '\\right)$。',
      (p.md === 1 ? '展開後把所有項移到左邊' : '兩邊同乘 $' + p.md + '$ 去分母，再把所有項移到左邊') + '，整理成一般式：$' + lineTex(L[0], L[1], L[2]) + '$。'];
  };

  L1_SOL.line2pt = function (p) {
    var L = p.ans;
    if (p.x1 === p.x2) return [
      '先看兩點的 $x$ 坐標：$A$、$B$ 的 $x$ 都是 $' + p.x1 + '$，所以這是一條鉛直線，沒有斜率，不能用點斜式。',
      '鉛直線上每一點的 $x$ 都相同，所以方程式是 $' + lineTex(L[0], L[1], L[2]) + '$。'];
    var dy = p.y2 - p.y1, dx = p.x2 - p.x1, m = F(dy, dx);
    return ['先用兩點求斜率：$m=\\dfrac{' + difT(p.y2, p.y1) + '}{' + difT(p.x2, p.x1) + '}=\\dfrac{' + dy + '}{' + dx + '}=' + Fr.tex(m, true) + '$。',
      '再用點斜式（取 $A$ 這一點）：$' + mnT('y', p.y1) + '=' + Fr.tex(m, true) + '\\left(' + mnT('x', p.x1) + '\\right)$。',
      '去分母、移項整理成一般式：$' + lineTex(L[0], L[1], L[2]) + '$。'];
  };

  L1_SOL.interceptForm = function (p) {
    if (p.type === 0) {
      var L = p.ans;
      return ['已知兩個截距，用截距式：$\\dfrac{x}{a}+\\dfrac{y}{b}=1$，其中 $a$ 是 $x$ 截距、$b$ 是 $y$ 截距。',
        '代入 $a=' + p.a + '$、$b=' + p.b + '$：$\\dfrac{x}{' + p.a + '}+\\dfrac{y}{' + p.b + '}=1$。',
        '兩邊同乘 $' + (p.a * p.b) + '$ 去分母後移項，整理成一般式：$' + lineTex(L[0], L[1], L[2]) + '$。'];
    }
    var nl = normLine(p.A, p.B, p.C), xi = F(p.ans[0], p.ans[1]), yi = F(p.ans[2], p.ans[3]);
    return ['截距就是直線與坐標軸的交點：$x$ 截距令 $y=0$、$y$ 截距令 $x=0$。',
      '令 $y=0$：$' + term(nl[0], 'x', true) + term(nl[2], '', false) + '=0$，解得 $x=' + Fr.tex(xi, true) + '$。',
      '令 $x=0$：$' + term(nl[1], 'y', true) + term(nl[2], '', false) + '=0$，解得 $y=' + Fr.tex(yi, true) + '$。',
      '所以 $x$ 截距是 $' + Fr.tex(xi) + '$、$y$ 截距是 $' + Fr.tex(yi) + '$。'];
  };

  L1_SOL.parPerp = function (p) {
    var nl = normLine(p.a, p.b, p.c), L = p.ans;
    if (p.par) {
      var k1 = nl[0] * p.x0 + nl[1] * p.y0;
      return ['兩直線平行 $\\iff$ $x,y$ 的係數成比例，所以可以把係數照抄、只改常數：設所求為 $' + term(nl[0], 'x', true) + term(nl[1], 'y', false) + '=k$。',
        '把 $' + ptTex(p.x0, p.y0) + '$ 代入左邊求 $k$：$k=' + subT(nl[0], nl[1], 0, p.x0, p.y0) + '=' + k1 + '$。',
        '所以直線是 $' + term(nl[0], 'x', true) + term(nl[1], 'y', false) + '=' + k1 + '$，移項整理成 $' + lineTex(L[0], L[1], L[2]) + '$。'];
    }
    var k2 = nl[1] * p.x0 - nl[0] * p.y0;
    return ['兩直線垂直時，把 $x,y$ 的係數對調、其中一個變號就會垂直：設所求為 $' + term(nl[1], 'x', true) + term(-nl[0], 'y', false) + '=k$。',
      '把 $' + ptTex(p.x0, p.y0) + '$ 代入左邊求 $k$：$k=' + subT(nl[1], -nl[0], 0, p.x0, p.y0) + '=' + k2 + '$。',
      '所以直線是 $' + term(nl[1], 'x', true) + term(-nl[0], 'y', false) + '=' + k2 + '$，移項整理成 $' + lineTex(L[0], L[1], L[2]) + '$。'];
  };

  L1_SOL.intersect = function (p) {
    var A = p.l1, B = p.l2, x = p.ans[0], y = p.ans[1];
    var m1 = B[1], m2 = A[1], dA = A[0] * m1 - B[0] * m2, dC = A[2] * m1 - B[2] * m2;
    return ['兩直線的交點就是聯立方程組的解，先消去一個變數。',
      '第一式乘 $' + parT(m1) + '$、第二式乘 $' + parT(m2) + '$，兩式的 $y$ 係數都變成 $' + (A[1] * B[1]) + '$；相減得 $' + term(dA, 'x', true) + term(dC, '', false) + '=0$，解得 $x=' + x + '$。',
      '把 $x=' + x + '$ 代回 $' + lineTex(A[0], A[1], A[2]) + '$ 解出 $y=' + y + '$，所以交點是 $' + ptTex(x, y) + '$。'];
  };

  L1_SOL.ptLineDist = function (p) {
    var nl = normLine(p.a, p.b, p.c), num = Math.abs(nl[0] * p.x0 + nl[1] * p.y0 + nl[2]);
    var s = nl[0] * nl[0] + nl[1] * nl[1], qq = simpSqrt(s), dt = surdFrac(p.ans[0], p.ans[1], p.ans[2]);
    return ['點到直線的距離公式：$d=\\dfrac{|ax_0+by_0+c|}{\\sqrt{a^2+b^2}}$。',
      '分子：把 $' + ptTex(p.x0, p.y0) + '$ 代進左邊再取絕對值，$\\left|' + subT(nl[0], nl[1], nl[2], p.x0, p.y0) + '\\right|=' + num + '$。',
      '分母：$\\sqrt{' + parT(nl[0]) + '^2+' + parT(nl[1]) + '^2}=\\sqrt{' + s + '}' + (qq.r === 1 ? '=' + qq.c : '') + '$。',
      '相除' + (qq.r === 1 ? '並約分' : '後把分母的根號有理化（分子分母同乘 $\\sqrt{' + qq.r + '}$）') + '，所以 $d=' + dt + '$。'];
  };

  L1_SOL.parDist = function (p) {
    var s = p.a * p.a + p.b * p.b, dif = Math.abs(p.c1 - p.c2), qq = simpSqrt(s);
    var dt = surdFrac(p.ans[0], p.ans[1], p.ans[2]);
    return ['兩平行線的距離：先把兩條的 $x,y$ 係數化成一模一樣，再用 $d=\\dfrac{|c_1-c_2|}{\\sqrt{a^2+b^2}}$。',
      '把兩條都乘上適當倍數，寫成 $' + term(p.a, 'x', true) + term(p.b, 'y', false) + '+c=0$ 的形式，這時 $c_1=' + p.c1 + '$、$c_2=' + p.c2 + '$。',
      '分子 $\\left|' + difT(p.c1, p.c2) + '\\right|=' + dif + '$；分母 $\\sqrt{' + p.a + '^2+' + parT(p.b) + '^2}=\\sqrt{' + s + '}' + (qq.r === 1 ? '=' + qq.c : '') + '$。',
      '相除' + (qq.r === 1 ? '並約分' : '並把分母有理化') + '，所以 $d=' + dt + '$。'];
  };

  L1_SOL.triArea = function (p) {
    var P = p.P, bx = P[1][0] - P[0][0], by = P[1][1] - P[0][1], cx = P[2][0] - P[0][0], cy = P[2][1] - P[0][1];
    var det = bx * cy - cx * by, A = F(p.ans[0], p.ans[1]);
    return ['把 $A$ 平移到原點（整個三角形一起平移，面積不變），只要看另外兩點相對於 $A$ 的位移。',
      '$B-A=' + ptTex(bx, by) + '$、$C-A=' + ptTex(cx, cy) + '$。',
      '面積 $=\\dfrac12|ad-bc|=\\dfrac12\\left|' + parT(bx) + '\\times' + parT(cy) + '-' + parT(cx) + '\\times' + parT(by) + '\\right|=\\dfrac12\\times' + Math.abs(det) + '$，所以面積是 $' + Fr.tex(A) + '$。'];
  };

  L1_SOL.symAxis = function (p) {
    var rules = ['對 $x$ 軸對稱：橫坐標不變、縱坐標變號。', '對 $y$ 軸對稱：縱坐標不變、橫坐標變號。',
      '對原點對稱：兩個坐標都變號。', '對直線 $y=x$ 對稱：把橫坐標與縱坐標互換。'];
    var acts = ['橫坐標維持 $' + p.x0 + '$，縱坐標由 $' + p.y0 + '$ 變成 $' + (-p.y0) + '$',
      '縱坐標維持 $' + p.y0 + '$，橫坐標由 $' + p.x0 + '$ 變成 $' + (-p.x0) + '$',
      '$' + p.x0 + '$ 變成 $' + (-p.x0) + '$、$' + p.y0 + '$ 變成 $' + (-p.y0) + '$',
      '橫坐標變成原本的縱坐標 $' + p.y0 + '$、縱坐標變成原本的橫坐標 $' + p.x0 + '$'];
    return [rules[p.t],
      '把 $P' + ptTex(p.x0, p.y0) + '$ 套進規則：' + acts[p.t] + '。',
      '所以對稱點是 $' + ptTex(p.ans[0], p.ans[1]) + '$。'];
  };

  L1_SOL.translate = function (p) {
    var nl = normLine(p.a, p.b, p.c), L = p.ans;
    var ct = function (n, first) { return n === 1 ? (first ? '' : '+') : (n === -1 ? '-' : term(n, '', first)); };
    return ['平移用「代換」：圖形向右移 $h$、向上移 $k$ 時，方程式裡要把 $x$ 換成 $x-h$、$y$ 換成 $y-k$（和移動方向相反）。',
      '這題是向' + (p.h > 0 ? '右' : '左') + '移 $' + Math.abs(p.h) + '$、向' + (p.k > 0 ? '上' : '下') + '移 $' + Math.abs(p.k) + '$，代換後：$' + ct(nl[0], true) + '\\left(x-' + parT(p.h) + '\\right)' + ct(nl[1], false) + '\\left(y-' + parT(p.k) + '\\right)' + term(nl[2], '', false) + '=0$。',
      '展開、把常數項合併，得到 $' + lineTex(L[0], L[1], L[2]) + '$。'];
  };

  L1_SOL.perpBisector = function (p) {
    var L = p.ans, mx = (p.x1 + p.x2) / 2, my = (p.y1 + p.y2) / 2, nx = p.x2 - p.x1, ny = p.y2 - p.y1;
    var st = ['中垂線要同時滿足兩件事：通過 $\\overline{AB}$ 的中點、而且與 $\\overline{AB}$ 垂直。',
      '中點 $M=\\left(\\dfrac{' + parT(p.x1) + '+' + parT(p.x2) + '}{2},\\ \\dfrac{' + parT(p.y1) + '+' + parT(p.y2) + '}{2}\\right)=' + ptTex(mx, my) + '$。'];
    if (nx === 0) st.push('$\\overline{AB}$ 是鉛直線（兩點的 $x$ 都是 $' + p.x1 + '$），所以中垂線是通過 $M$ 的水平線 $' + lineTex(L[0], L[1], L[2]) + '$。');
    else if (ny === 0) st.push('$\\overline{AB}$ 是水平線（兩點的 $y$ 都是 $' + p.y1 + '$），所以中垂線是通過 $M$ 的鉛直線 $' + lineTex(L[0], L[1], L[2]) + '$。');
    else {
      var mAB = F(ny, nx), mPB = F(-nx, ny);
      st.push('$\\overline{AB}$ 的斜率 $=\\dfrac{' + difT(p.y2, p.y1) + '}{' + difT(p.x2, p.x1) + '}=' + Fr.tex(mAB, true) + '$，中垂線的斜率與它相乘要等於 $-1$，所以是 $' + Fr.tex(mPB, true) + '$。');
      st.push('用點斜式過 $M$：$' + mnT('y', my) + '=' + Fr.tex(mPB, true) + '\\left(' + mnT('x', mx) + '\\right)$，整理成 $' + lineTex(L[0], L[1], L[2]) + '$。');
    }
    return st;
  };

  L1_SOL.halfPlane = function (p) {
    var lhs = lhsT(p.a, p.b, p.c), yes = [];
    var det = p.pts.map(function (pt, i) {
      var v = p.a * pt[0] + p.b * pt[1] + p.c;
      if (p.ans[i]) yes.push('(' + (i + 1) + ')');
      return '(' + (i + 1) + ') $' + subT(p.a, p.b, p.c, pt[0], pt[1]) + '=' + v + '$，' + (p.ans[i] ? '符合' : '不符合');
    });
    return ['判斷一個點在不在半平面裡，就把它的坐標代進不等式左邊 $' + lhs + '$，算出來的值再和 $0$ 比。',
      '四個點依序代入：' + det.slice(0, 2).join('；') + '。',
      '剩下兩點：' + det.slice(2).join('；') + '。',
      '注意 $' + p.op + '$ ' + (p.strict ? '不含等號，算出來剛好是 $0$ 的點不算' : '含等號，算出來剛好是 $0$ 的點也算') + '，所以答案是 ' + (yes.length ? yes.join('') : '沒有任何一點滿足') + '。'];
  };

  L1_SOL.lpVertex = function (p) {
    var vals = p.V.map(function (v) { return p.p * v[0] + p.q * v[1]; });
    var f = term(p.p, 'x', true) + term(p.q, 'y', false);
    var im = vals.indexOf(p.ans[0]), imn = vals.indexOf(p.ans[1]);
    return ['$f$ 是一次式（線性），在凸區域上的最大值與最小值一定出現在頂點，所以只要把三個頂點代進去比大小。',
      '代入三個頂點：' + p.V.map(function (v, i) { return '$' + ptTex(v[0], v[1]) + '$ 得 $f=' + subT(p.p, p.q, 0, v[0], v[1]) + '=' + vals[i] + '$'; }).join('；') + '。',
      '比大小：最大值 $' + p.ans[0] + '$（在 $' + ptTex(p.V[im][0], p.V[im][1]) + '$），最小值 $' + p.ans[1] + '$（在 $' + ptTex(p.V[imn][0], p.V[imn][1]) + '$）。'];
  };

  L1_SOL.circStd = function (p) {
    var d = p.ans[0], e = p.ans[1], f = p.ans[2];
    var std = ('(x' + term(-p.h, '', false) + ')^2+(y' + term(-p.k, '', false) + ')^2=' + (p.r * p.r)).replace('(x)', 'x').replace('(y)', 'y');
    var gen = 'x^2+y^2' + term(d, 'x', false) + term(e, 'y', false) + term(f, '', false) + '=0';
    return ['圓的標準式：圓心 $(h,k)$、半徑 $r$ 時是 $(x-h)^2+(y-k)^2=r^2$。',
      '代入 $h=' + p.h + '$、$k=' + p.k + '$、$r=' + p.r + '$（圓心坐標是負的時候，括號裡會變成加號），得 $' + std + '$。',
      '展開：$x^2' + term(d, 'x', false) + term(p.h * p.h, '', false) + '+y^2' + term(e, 'y', false) + term(p.k * p.k, '', false) + '=' + (p.r * p.r) + '$，把常數移到左邊合併。',
      '所以標準式是 $' + std + '$，一般式是 $' + gen + '$。'];
  };

  L1_SOL.circGen = function (p) {
    var h = p.ans[0], k = p.ans[1], rad = p.ans[2], inside = p.d * p.d + p.e * p.e - 4 * p.f;
    return ['對照一般式 $x^2+y^2+dx+ey+f=0$：這題 $d=' + p.d + '$、$e=' + p.e + '$、$f=' + p.f + '$。',
      '圓心 $=\\left(-\\dfrac{d}{2},\\ -\\dfrac{e}{2}\\right)$：把 $d$、$e$ 各取一半再變號，得 $' + ptTex(h, k) + '$。',
      '半徑 $r=\\dfrac12\\sqrt{d^2+e^2-4f}=\\dfrac12\\sqrt{' + parT(p.d) + '^2+' + parT(p.e) + '^2-4\\times' + parT(p.f) + '}=\\dfrac12\\sqrt{' + inside + '}=' + rad + '$。',
      '所以圓心是 $' + ptTex(h, k) + '$、半徑是 $' + rad + '$。'];
  };

  L1_SOL.circKind = function (p) {
    var h = p.ans[0], k = p.ans[1], R2 = p.ans[2], inside = p.d * p.d + p.e * p.e - 4 * p.f;
    var st = ['先配方：$x^2+dx+y^2+ey+f=0$ 配成 $\\left(x+\\dfrac{d}{2}\\right)^2+\\left(y+\\dfrac{e}{2}\\right)^2=\\dfrac{d^2+e^2-4f}{4}$，所以只要看 $d^2+e^2-4f$ 的正負。',
      '代入 $d=' + p.d + '$、$e=' + p.e + '$、$f=' + p.f + '$：$d^2+e^2-4f=' + parT(p.d) + '^2+' + parT(p.e) + '^2-4\\times' + parT(p.f) + '=' + inside + '$。'];
    if (p.kind === 0) st.push('$' + inside + '\\gt 0$，是圓：圓心 $\\left(-\\dfrac{d}{2},\\ -\\dfrac{e}{2}\\right)=' + ptTex(h, k) + '$、半徑 $=\\dfrac12\\sqrt{' + inside + '}=' + sqrtTex(R2) + '$。');
    else if (p.kind === 1) st.push('$' + inside + '=0$，右邊是 $0$：兩個平方和等於 $0$ 只有一種可能，圖形只有一點 $' + ptTex(h, k) + '$（半徑為 $0$）。');
    else st.push('$' + inside + '\\lt 0$：配方後右邊 $=' + R2 + '\\lt0$，而左邊是兩個平方的和不可能為負，所以沒有圖形。');
    return st;
  };

  L1_SOL.ptCircle = function (p) {
    var s = (p.x0 - p.h) * (p.x0 - p.h) + (p.y0 - p.k) * (p.y0 - p.k), r2 = p.r * p.r;
    var op = p.ans === 0 ? '\\lt' : (p.ans === 1 ? '=' : '\\gt'), nm = ['內部', '圓上', '外部'][p.ans];
    return ['判斷點與圓的位置，只要比 $\\overline{PC}^2$ 與 $r^2$ 的大小（$C$ 是圓心 $' + ptTex(p.h, p.k) + '$），不必開根號。',
      '$\\overline{PC}^2=\\left(' + difT(p.x0, p.h) + '\\right)^2+\\left(' + difT(p.y0, p.k) + '\\right)^2=' + ((p.x0 - p.h) * (p.x0 - p.h)) + '+' + ((p.y0 - p.k) * (p.y0 - p.k)) + '=' + s + '$，而 $r^2=' + r2 + '$。',
      '比大小：$\\overline{PC}^2=' + s + op + r2 + '$，所以 $P$ 在圓的' + nm + '。'];
  };

  L1_SOL.lineCircPos = function (p) {
    var num = Math.abs(p.a * p.h + p.b * p.k + p.c), d = distSimp(num, 25);
    var op = p.ans === 0 ? '\\lt ' : (p.ans === 1 ? '=' : '\\gt '), nm = ['相交（交於兩點）', '相切', '相離'][p.ans];
    return ['直線與圓的位置關係，看「圓心到直線的距離 $d$」和半徑 $r$ 誰大誰小就好，不用聯立。',
      '圓心是 $' + ptTex(p.h, p.k) + '$：$d=\\dfrac{\\left|' + subT(p.a, p.b, p.c, p.h, p.k) + '\\right|}{\\sqrt{' + p.a + '^2+' + parT(p.b) + '^2}}=\\dfrac{' + num + '}{5}=' + d.tex + '$。',
      '半徑 $r=' + p.r + '$，比大小得 $d=' + d.tex + op + 'r$，所以兩者' + nm + '。'];
  };

  L1_SOL.chordLen = function (p) {
    var num = Math.abs(p.a * p.h + p.b * p.k + p.c), s = p.a * p.a + p.b * p.b;
    var d = Math.round(num / Math.sqrt(s)), half = p.ans / 2;
    return ['弦心距 $d$（圓心到直線的距離）、半徑 $r$、半弦長會組成一個直角三角形，所以弦長 $=2\\sqrt{r^2-d^2}$。',
      '先算弦心距：$d=\\dfrac{\\left|' + subT(p.a, p.b, p.c, p.h, p.k) + '\\right|}{\\sqrt{' + parT(p.a) + '^2+' + parT(p.b) + '^2}}=\\dfrac{' + num + '}{' + Math.round(Math.sqrt(s)) + '}=' + d + '$。',
      '半弦長 $=\\sqrt{r^2-d^2}=\\sqrt{' + p.r + '^2-' + d + '^2}=\\sqrt{' + (p.r * p.r - d * d) + '}=' + half + '$，所以弦長 $=2\\times' + half + '=' + p.ans + '$。'];
  };

  L1_SOL.tangentAtPt = function (p) {
    var L = p.ans, dx = p.x0 - p.h, dy = p.y0 - p.k;
    var st = ['切線與切點處的半徑 $\\overline{CP}$ 垂直（$C$ 是圓心 $' + ptTex(p.h, p.k) + '$），所以先看 $\\overline{CP}$ 的方向。'];
    if (dx === 0) st.push('$C$ 與 $P$ 的 $x$ 坐標都是 $' + p.h + '$，半徑是鉛直的，所以切線是通過 $P$ 的水平線 $' + lineTex(L[0], L[1], L[2]) + '$。');
    else if (dy === 0) st.push('$C$ 與 $P$ 的 $y$ 坐標都是 $' + p.k + '$，半徑是水平的，所以切線是通過 $P$ 的鉛直線 $' + lineTex(L[0], L[1], L[2]) + '$。');
    else {
      var mC = F(dy, dx), mT = F(-dx, dy);
      st.push('$\\overline{CP}$ 的斜率 $=\\dfrac{' + difT(p.y0, p.k) + '}{' + difT(p.x0, p.h) + '}=' + Fr.tex(mC, true) + '$，切線的斜率與它相乘要等於 $-1$，所以是 $' + Fr.tex(mT, true) + '$。');
      st.push('用點斜式過 $P' + ptTex(p.x0, p.y0) + '$：$' + mnT('y', p.y0) + '=' + Fr.tex(mT, true) + '\\left(' + mnT('x', p.x0) + '\\right)$，整理成 $' + lineTex(L[0], L[1], L[2]) + '$。');
    }
    return st;
  };

  L1_SOL.tangentLen = function (p) {
    var dx = p.x0 - p.h, dy = p.y0 - p.k, pc2 = dx * dx + dy * dy, s = pc2 - p.r * p.r, qq = simpSqrt(s);
    return ['切點 $T$ 處切線垂直半徑，所以 $\\triangle PTC$ 是直角三角形（$C$ 是圓心 $' + ptTex(p.h, p.k) + '$），用畢氏定理：$\\overline{PT}=\\sqrt{\\overline{PC}^2-r^2}$。',
      '$\\overline{PC}^2=\\left(' + difT(p.x0, p.h) + '\\right)^2+\\left(' + difT(p.y0, p.k) + '\\right)^2=' + pc2 + '$，而 $r^2=' + (p.r * p.r) + '$。',
      '相減：$' + pc2 + '-' + (p.r * p.r) + '=' + s + '$，' + (qq.r === 1 ? '剛好是完全平方數' : '把平方因數 $' + (qq.c * qq.c) + '$ 提出根號') + '，所以 $\\overline{PT}=' + sqrtTex(s) + '$。'];
  };

  var META_L1 = [
      ['slope2pt', '§1 兩點求斜率'], ['dist2pt', '§1 兩點距離'], ['midDiv', '§1 中點與內分點'], ['lineEq', '§1 點斜式→一般式'],
      ['line2pt', '§1 兩點式'], ['interceptForm', '§1 截距'], ['parPerp', '§1 平行線與垂直線'], ['intersect', '§1 兩直線交點'],
      ['ptLineDist', '§2 點到直線的距離'], ['parDist', '§2 兩平行線的距離'], ['triArea', '§2 三角形面積'], ['symAxis', '§2 對稱點（軸、原點、y=x）'],
      ['translate', '§2 平移直線'], ['perpBisector', '§2 中垂線'],
      ['halfPlane', '§3 半平面判定'], ['lpVertex', '§3 線性規劃：頂點代入'],
      ['circStd', '§4 圓心半徑→方程式'], ['circGen', '§4 一般式→圓心半徑'], ['circKind', '§4 圓、一點或無圖形'], ['ptCircle', '§4 點與圓的位置'],
      ['lineCircPos', '§5 直線與圓的位置關係'], ['chordLen', '§5 弦長'], ['tangentAtPt', '§5 過圓上一點的切線'], ['tangentLen', '§5 切線長']
  ];
  var META_L2 = [
      ['lineFamily', '§1 直線族恆過定點'], ['threeLines', '§1 三直線圍不成三角形'], ['minArea', '§1 截距式＋算幾：最小面積'],
      ['reflectPt', '§2 點對直線的對稱點'], ['shortestPath', '§2 反射最短路徑'], ['eqDistOnLine', '§2 直線上與兩點等距的點'],
      ['lpOpt', '§3 線性規劃（不等式組）'], ['regionArea', '§3 不等式區域面積'], ['latticeCount', '§3 格子點計數'],
      ['circParam', '§4 含參數的圓'], ['circ3pt', '§4 過三點的圓'], ['circCenterOnLine', '§4 圓心在直線上'], ['circTangentLine', '§4 與直線相切的圓'],
      ['tangentExt', '§5 過圓外一點的切線'], ['chordParam', '§5 弦長反求參數'], ['circMinMax', '§5 圓上動點的最遠最近'], ['circLinePosParam', '§5 相交／相切的參數範圍']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     答案全部精確（整數／Fraction／化簡根式）；p 給 Python 獨立驗算。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};
  function sg(n) { return n < 0 ? '(' + n + ')' : String(n); }                 /* 負數加括號 */
  function ineqTex(a, b, c, op) {                                             /* ax+by op c（不約分、保留原樣） */
    var s = term(a, 'x', true); s += term(b, 'y', s === ''); return s + op + c;
  }
  function lineThrough(P, Q) { return [Q[1] - P[1], P[0] - Q[0], -((Q[1] - P[1]) * P[0] + (P[0] - Q[0]) * P[1])]; }   /* 過兩點的 [a,b,c]：ax+by+c=0 */
  function shiftTxt(p, q) { return '向' + (p > 0 ? '右' : '左') + '平移 ' + T(String(Math.abs(p))) + ' 單位、再向' + (q > 0 ? '上' : '下') + '平移 ' + T(String(Math.abs(q))) + ' 單位'; }

  /* L3-1　平移後與自己重合 ⟹ 平移量就是直線的方向 */
  L3.shiftCoincide = function (r) {
    var p, q; do { p = r.nz(-4, 4); q = r.nz(-4, 4); } while (p === q || gcd(p, q) !== 1);
    var v = r.int(0, 1), d = distSimp(Math.abs(q - p), p * p + q * q), m = F(q, p);
    return { q: '將直線 ' + T('ax+by=0') + ' ' + shiftTxt(p, q) + '後，恰與原直線重合。' + (v === 0 ? '求兩平行線 ' + T('ax+by+a=0') + ' 與 ' + T('ax+by-b=0') + ' 之間的距離。（化為最簡分數或根式）' : '求此直線的斜率，以及兩平行線 ' + T('ax+by+a=0') + ' 與 ' + T('ax+by-b=0') + ' 之間的距離。'),
      a: v === 0 ? T(d.tex) : '斜率 ' + T(Fr.tex(m)) + '，距離 ' + T(d.tex),
      h: '平移 $(' + p + ',' + q + ')$ 後還是同一條線 ⟹ 直線的方向就是 $(' + p + ',' + q + ')$，斜率 $=' + Fr.tex(m, true) + '$。由斜率定出 $a:b$（取一組最簡整數即可，比例不影響距離），再套兩平行線距離公式。',
      p: { p: p, q: q, v: v, ans: [d.n, d.d, d.r] } };
  };

  /* L3-2　兩平行線各過一點、距離已知 ⟹ 設斜率，點到線距離 */
  L3.parTwoPts = function (r) {
    var nb, a, b, c, u, w, d, x0, y0, A2, tries = 0;
    do {
      nb = r.pick([[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13], [8, 15, 17], [15, 8, 17]]); a = nb[0] * r.sign(); b = nb[1]; c = nb[2];
      u = r.nz(-9, 9); w = r.nz(-9, 9); d = Math.abs(a * u + b * w) / c; A2 = u * u - d * d;
    } while ((d !== Math.round(d) || d < 1 || d > 4 || A2 === 0 || a * w - b * u === 0 || w * w === d * d) && tries++ < 5000);
    x0 = r.int(-5, 5); y0 = r.int(-5, 5);
    var m1 = F(-a, b), m2 = Fr.sub(F(2 * u * w, A2), m1), ms = Fr.lt(m1, m2) ? [m1, m2] : [m2, m1];
    return { q: '坐標平面上有兩條距離為 ' + T(String(d)) + ' 的平行直線，分別通過 ' + T(ptTex(x0, y0)) + ' 與 ' + T(ptTex(x0 + u, y0 + w)) + '。求這兩條直線所有可能的斜率。',
      a: T('m=' + Fr.tex(ms[0]) + '\\ \\text{或}\\ ' + Fr.tex(ms[1])),
      h: '兩平行線的距離 $=$ 其中一點到另一條線的距離。設過 $' + ptTex(x0, y0) + '$ 的直線 $y' + term(-y0, '', false) + '=m(x' + term(-x0, '', false) + ')$，令 $' + ptTex(x0 + u, y0 + w) + '$ 到它的距離為 $' + d + '$：$\\dfrac{|' + term(u, 'm', true) + term(-w, '', false) + '|}{\\sqrt{m^2+1}}=' + d + '$，平方後解 $m$ 的二次方程式。',
      p: { P: [x0, y0], Q: [x0 + u, y0 + w], d: d, ans: [[ms[0].n, ms[0].d], [ms[1].n, ms[1].d]] } };
  };

  /* L3-3　兩線與 x 軸圍三角形：高固定，底＝兩個 x 截距之差（絕對值 ⟹ 兩解） */
  L3.triAreaSlopes = function (r) {
    var h, m1, S, x1, base, xs, tries = 0, ok;
    do {
      h = r.pick([2, 3, 4, 6]) * r.sign(); m1 = r.pick([F(1), F(2), F(3), F(1, 2), F(-1), F(-2), F(3, 2), F(-1, 2)]); S = r.int(3, 20);
      x1 = Fr.div(F(-h), m1); base = F(2 * S, Math.abs(h)); xs = [Fr.sub(x1, base), Fr.add(x1, base)];
      ok = xs[0].n !== 0 && xs[1].n !== 0 && xs[0].d <= 3 && xs[1].d <= 3 && Math.abs(xs[0].n) <= 24 && Math.abs(xs[1].n) <= 24;
    } while (!ok && tries++ < 3000);
    var ms = xs.map(function (x) { return Fr.div(F(-h), x); }); if (Fr.lt(ms[1], ms[0])) ms.reverse();
    return { q: '設直線 ' + T('L_1') + ' 與 ' + T('L_2') + ' 相交於 ' + T(ptTex(0, h)) + '，且 ' + T('L_1') + ' 的斜率為 ' + T(Fr.tex(m1)) + '。若 ' + T('L_1') + '、' + T('L_2') + ' 與 ' + T('x') + ' 軸所圍的三角形面積為 ' + T(String(S)) + '，求 ' + T('L_2') + ' 所有可能的斜率。',
      a: T('m=' + Fr.tex(ms[0]) + '\\ \\text{或}\\ ' + Fr.tex(ms[1])),
      h: '頂點 $' + ptTex(0, h) + '$ 到 $x$ 軸的高是 $' + Math.abs(h) + '$，底是兩條線 $x$ 截距的差。$L_1$ 的 $x$ 截距是 $' + Fr.tex(x1, true) + '$；設 $L_2$ 的 $x$ 截距為 $t$：$\\dfrac12\\cdot' + Math.abs(h) + '\\cdot\\left|t' + (x1.n < 0 ? '+' : '-') + Fr.tex(F(Math.abs(x1.n), x1.d), true) + '\\right|=' + S + '$，絕對值拆開有<b>兩個</b> $t$，再各自換回斜率。',
      p: { h: h, m1: [m1.n, m1.d], S: S, ans: [[ms[0].n, ms[0].d], [ms[1].n, ms[1].d]] } };
  };

  /* L3-4　連續兩次鏡射的三點共圓：圓心是兩條鏡射軸的交點 */
  L3.doubleReflectCircle = function (r) {
    var h = r.int(-4, 4), k = r.int(-4, 4), n1, n2, P, tries = 0;
    do {
      n1 = [r.int(1, 3), r.nz(-3, 3)]; n2 = [r.int(1, 3), r.nz(-3, 3)]; P = [h + r.nz(-5, 5), k + r.nz(-5, 5)];
    } while ((n1[0] * n2[1] - n1[1] * n2[0] === 0 || gcd(n1[0], n1[1]) !== 1 || gcd(n2[0], n2[1]) !== 1 ||
      n1[0] * (P[0] - h) + n1[1] * (P[1] - k) === 0 || n2[0] * (P[0] - h) + n2[1] * (P[1] - k) === 0) && tries++ < 500);
    var c1 = n1[0] * h + n1[1] * k, c2 = n2[0] * h + n2[1] * k, r2 = (P[0] - h) * (P[0] - h) + (P[1] - k) * (P[1] - k);
    var e1 = ineqTex(n1[0], n1[1], c1, '='), e2 = ineqTex(n2[0], n2[1], c2, '=');
    return { q: '已知 ' + T('P' + ptTex(P[0], P[1])) + ' 對直線 ' + T('L:' + e1) + ' 的對稱點為 ' + T('Q') + '，' + T('Q') + ' 對直線 ' + T('M:' + e2) + ' 的對稱點為 ' + T('R') + '。求過 ' + T('P,Q,R') + ' 三點的圓方程式。',
      a: T(stdTex(h, k, r2)),
      h: '鏡射不改變「到鏡射軸上任一點的距離」。$L$ 與 $M$ 的交點 $O\'$ 同時在兩條軸上，所以 $\\overline{O\'P}=\\overline{O\'Q}=\\overline{O\'R}$ ⟹ $O\'$ 就是圓心，不必真的算 $Q$、$R$。先解聯立 $' + e1 + '$、$' + e2 + '$。',
      p: { P: P, L: [n1[0], n1[1], -c1], M: [n2[0], n2[1], -c2], ans: [h, k, r2] } };
  };

  /* L3-5　過定點的直線，A 的投影距離最大 ⟹ 垂足就是定點，直線 ⊥ 連線 */
  L3.maxProjDist = function (r) {
    var fx = r.pick([0, 0, 1, -1, 2, -2]), fy = fx === 0 ? 0 : r.int(-3, 3), a, b;
    a = fx + r.nz(-5, 5); b = fy + r.nz(-5, 5);
    var v = r.int(0, 1), m = F(-(a - fx), b - fy), D = (a - fx) * (a - fx) + (b - fy) * (b - fy);
    var Ltex = fx === 0 && fy === 0 ? 'y=mx' : 'y' + term(-fy, '', false) + '=m(x' + term(-fx, '', false) + ')';
    return { q: '平面上有定點 ' + T('A' + ptTex(a, b)) + ' 與直線 ' + T('L:' + Ltex) + '。令 ' + T('A') + ' 在 ' + T('L') + ' 上的投影點為 ' + T('A\'') + '，求線段 ' + T('\\overline{AA\'}') + ' 最長時的 ' + T('m') + ' 值' + (v === 1 ? '，以及這個最大長度' : '') + '。',
      a: T('m=' + Fr.tex(m)) + (v === 1 ? '，最大長度 ' + T(sqrtTex(D)) : ''),
      h: '$\\overline{AA\'}$ 是 $A$ 到 $L$ 的距離，而 $L$ 恆過定點 $F' + ptTex(fx, fy) + '$，所以 $\\overline{AA\'}\\le\\overline{AF}$；等號成立在 $A\'=F$，也就是 $L\\perp\\overline{AF}$。$\\overline{AF}$ 的斜率是 $' + Fr.tex(F(b - fy, a - fx), true) + '$。',
      p: { A: [a, b], Fp: [fx, fy], v: v, ans: [m.n, m.d, D] } };
  };

  /* L3-6　到三頂點等距的直線 ⟹ 三條中位線 */
  L3.equidistLines = function (r) {
    var x0 = r.int(-5, 3), y0 = r.int(-5, 3), p = r.int(1, 4) * r.sign(), q = r.int(1, 4) * r.sign();
    var A = [x0, y0], B = [x0 + 2 * p, y0], C = [x0, y0 + 2 * q];
    var l3 = lineTex(q, p, -(q * (x0 + p) + p * y0));
    return { q: '已知相異三點 ' + T('A' + ptTex(A[0], A[1])) + '、' + T('B' + ptTex(B[0], B[1])) + '、' + T('C' + ptTex(C[0], C[1])) + '。若直線 ' + T('L') + ' 到 ' + T('A,B,C') + ' 三點的距離都相等，求所有可能的 ' + T('L') + ' 的方程式。',
      a: T('x=' + (x0 + p)) + '、' + T('y=' + (y0 + q)) + '、' + T(l3),
      h: '三點不共線時，到三點等距的直線恰有三條：每條平行三角形的一邊、且通過另外兩邊的中點（中位線）。先求三邊中點：$\\overline{AB}$ 中點 $' + ptTex(x0 + p, y0) + '$、$\\overline{AC}$ 中點 $' + ptTex(x0, y0 + q) + '$、$\\overline{BC}$ 中點 $' + ptTex(x0 + p, y0 + q) + '$。',
      p: { A: A, B: B, C: C, ans: [[1, 0, -(x0 + p)], [0, 1, -(y0 + q)], normLine(q, p, -(q * (x0 + p) + p * y0))] } };
  };

  /* L3-7　含參數的可行域面積：參數線繞定點轉，切掉一個三角形 */
  L3.paramRegionArea = function (r) {
    var a, b, c, t, m, X, Y, tries = 0, area;
    do {
      a = r.int(1, 4); b = r.int(1, 4); c = a * b * r.int(2, 4) / gcd(a, b); X = c / a; Y = c / b; t = r.int(1, X - 1); m = r.pick([F(1), F(2), F(3), F(1, 2), F(3, 2), F(4)]);
      var yQ = Fr.div(Fr.mul(m, F(c - a * t)), Fr.add(F(a), Fr.mul(F(b), m)));
      area = Fr.sub(F(X * Y, 2), Fr.mul(F(X - t, 2), yQ));
    } while ((X !== Math.round(X) || Y !== Math.round(Y) || t < 1 || t >= X || area.d > 12 || gcd(gcd(a, b), c) !== 1) && tries++ < 3000);
    var l2 = 'mx-y\\le ' + (t === 1 ? 'm' : t + 'm');
    return { q: '若正數 ' + T('m') + ' 使聯立不等式 ' + T('\\begin{cases}' + ineqTex(a, b, c, '\\le ') + '\\\\ ' + l2 + '\\\\ x\\ge 0\\\\ y\\ge 0\\end{cases}') + ' 的解區域面積為 ' + T(Fr.tex(area)) + '，求 ' + T('m') + '。',
      a: T('m=' + Fr.tex(m)),
      h: '$mx-y\\le ' + (t === 1 ? '' : t) + 'm\\iff y\\ge m(x-' + t + ')$，這條線恆過 $(' + t + ',0)$。沒有它時區域是三角形（面積 $' + Fr.tex(F(X * Y, 2), true) + '$）；$m\\gt 0$ 時它切掉以 $(' + t + ',0)$、$(' + X + ',0)$ 與「它和 $' + ineqTex(a, b, c, '=') + '$ 的交點」為頂點的三角形，用交點的 $y$ 坐標當高列式。',
      p: { a: a, b: b, c: c, t: t, area: [area.n, area.d], ans: [m.n, m.d] } };
  };

  /* L3-8　四條不等式圍區域：剔除不在區域內的假交點，鞋帶公式 */
  L3.quadRegionArea = function (r) {
    var k, p1, p2, s, u, V, ok, tries = 0, l1, l2, area2;
    do {
      k = r.pick([1, 2, 3]); p1 = r.int(1, 5); p2 = p1 + r.int(2, 5); s = r.int(1, 4); u = s + r.int(1, 4);
      V = [[p1, 0], [p2, 0], [u, k * u], [s, k * s]];
      l1 = lineThrough(V[0], V[3]); l2 = lineThrough(V[1], V[2]);
      /* 凸性：四個轉角同號 */
      var sgn = 0; ok = true;
      for (var i = 0; i < 4; i++) { var A = V[i], B = V[(i + 1) % 4], C = V[(i + 2) % 4], cr = (B[0] - A[0]) * (C[1] - B[1]) - (B[1] - A[1]) * (C[0] - B[0]); if (cr === 0) ok = false; if (sgn === 0) sgn = cr > 0 ? 1 : -1; else if ((cr > 0 ? 1 : -1) !== sgn) ok = false; }
      var g1 = gcd3(l1[0], l1[1], l1[2]), g2 = gcd3(l2[0], l2[1], l2[2]); l1 = l1.map(function (x) { return x / g1; }); l2 = l2.map(function (x) { return x / g2; });
      if (Math.max(Math.abs(l1[0]), Math.abs(l1[1]), Math.abs(l1[2]), Math.abs(l2[0]), Math.abs(l2[1]), Math.abs(l2[2])) > 40) ok = false;
      if (l1[0] * l2[1] - l1[1] * l2[0] === 0) ok = false;                  /* 兩條斜邊平行就沒有「假交點」可剔除 */
    } while (!ok && tries++ < 3000);
    area2 = 0; for (var j = 0; j < 4; j++) { var P = V[j], Q = V[(j + 1) % 4]; area2 += P[0] * Q[1] - Q[0] * P[1]; } area2 = Math.abs(area2);
    var cx = (V[0][0] + V[1][0] + V[2][0] + V[3][0]) / 4, cy = (V[0][1] + V[1][1] + V[2][1] + V[3][1]) / 4;
    function ineq(l) { var val = l[0] * cx + l[1] * cy + l[2], a = l[0], b = l[1], c = -l[2]; if (a < 0 || (a === 0 && b < 0)) { a = -a; b = -b; c = -c; val = -val; } return [a, b, c, val > 0 ? 1 : -1]; }
    var I1 = ineq(l1), I2 = ineq(l2), kk = [k, -1, 0, 1];
    var rows = r.shuffle([I1, I2]).map(function (I) { return ineqTex(I[0], I[1], I[2], I[3] > 0 ? '\\ge ' : '\\le '); });
    rows.push(ineqTex(k, -1, 0, '\\ge ')); rows.push('y\\ge 0');
    var ar = F(area2, 2);
    return { q: '求聯立不等式 ' + T('\\begin{cases}' + rows.join('\\\\ ') + '\\end{cases}') + ' 所圍成區域的面積。',
      a: T(Fr.tex(ar)),
      h: '四條線兩兩相交最多 $6$ 個交點，但區域的頂點只有 $4$ 個——每個交點都要代回其餘不等式檢查。先求 $y=0$ 與兩條斜線的交點 $(' + p1 + ',0)$、$(' + p2 + ',0)$，再求 $' + ineqTex(k, -1, 0, '=') + '$ 與兩條斜線的交點；依序排好後用鞋帶公式（或大三角形減小三角形）。',
      p: { ineqs: [I1, I2, kk, [0, 1, 0, 1]], V: V, ans: [ar.n, ar.d] } };
  };

  /* L3-9　過兩點＋弦心距：圓心在中垂線上、離中點 d；r²＝d²＋(半弦)² */
  L3.chordDistCircle = function (r) {
    var S = r.pick([[2, 1, 2, 1], [2, 1, 1, 2], [1, 2, 2, 1], [1, 2, 1, 2], [3, 1, 1, 3], [1, 3, 3, 1], [3, 1, 3, 1], [3, 2, 2, 3], [2, 3, 3, 2]]);
    var w = S[0], t = S[1], p = S[2] * r.sign(), q = S[3] * r.sign(), M, C1, C2, quad, tries = 0;
    function quadOf(P) { if (P[0] === 0 || P[1] === 0) return 0; return P[0] > 0 ? (P[1] > 0 ? 1 : 4) : (P[1] > 0 ? 2 : 3); }
    do { M = [r.int(-5, 5), r.int(-5, 5)]; C1 = [M[0] - t * q, M[1] + t * p]; C2 = [M[0] + t * q, M[1] - t * p]; }
    while ((quadOf(C1) === 0 || quadOf(C2) === 0 || quadOf(C1) === quadOf(C2)) && tries++ < 500);
    var C = r.int(0, 1) ? C1 : C2, A = [M[0] - w * p, M[1] - w * q], B = [M[0] + w * p, M[1] + w * q];
    var r2 = (w * w + t * t) * (p * p + q * q), rad = Math.round(Math.sqrt(r2)), d2 = t * t * (p * p + q * q), v = r.int(0, 1);
    var qn = ['', '一', '二', '三', '四'][quadOf(C)];
    return { q: '圓 ' + T('C') + ' 通過 ' + T('A' + ptTex(A[0], A[1])) + '、' + T('B' + ptTex(B[0], B[1])) + '，圓心 ' + T('O(h,k)') + ' 在第' + qn + '象限，且圓心到弦 ' + T('\\overline{AB}') + ' 的距離為 ' + T(sqrtTex(d2)) + '。' + (v === 0 ? '求圓 ' + T('C') + ' 的方程式。' : '設半徑為 ' + T('r') + '，求 ' + T('h+k+r') + '。'),
      a: v === 0 ? T(stdTex(C[0], C[1], r2)) : T(String(C[0] + C[1] + rad)),
      h: '圓心在 $\\overline{AB}$ 的中垂線上，離中點 $M' + ptTex(M[0], M[1]) + '$ 恰好 $' + sqrtTex(d2) + '$。$\\overline{AB}$ 的方向是 $(' + p + ',' + q + ')$，垂直方向取 $(' + (-q) + ',' + p + ')$（長度 $' + sqrtTex(p * p + q * q) + '$）：圓心 $=M\\pm' + t + '\\cdot(' + (-q) + ',' + p + ')$，用象限挑一個；再用 $r^2=(\\text{弦心距})^2+(\\text{半弦})^2$。',
      p: { A: A, B: B, d2: d2, quad: quadOf(C), v: v, ans: [C[0], C[1], r2] } };
  };

  /* L3-10　三直線圍三角形的外接圓：先求三頂點，再設一般式 */
  L3.circumThreeLines = function (r) {
    var p, q, s, t, num, tries = 0;
    do { p = r.int(-5, 2); q = p + r.int(2, 7); s = r.int(-4, 6); t = r.nz(-5, 5); num = s * s + t * t - (p + q) * s + p * q; }
    while ((s === p || s === q || num % t !== 0 || Math.abs(num / t) > 12) && tries++ < 3000);
    var d = -(p + q), e = -num / t, f = p * q, lA = lineThrough([p, 0], [s, t]), lB = lineThrough([q, 0], [s, t]);
    return { q: '三直線 ' + T('y=0') + '、' + T(lineTex(lA[0], lA[1], lA[2])) + '、' + T(lineTex(lB[0], lB[1], lB[2])) + ' 圍成一個三角形，求其外接圓方程式（以一般式表示）。',
      a: T(genTex(d, e, f)),
      h: '外接圓＝過三個頂點的圓。先求頂點：兩條斜線與 $y=0$ 的交點是 $(' + p + ',0)$、$(' + q + ',0)$，兩條斜線的交點再解聯立。設 $x^2+y^2+dx+ey+f=0$，先代 $x$ 軸上的兩點（只剩 $d,f$），最後代第三點求 $e$。',
      p: { lines: [[0, 1, 0], normLine(lA[0], lA[1], lA[2]), normLine(lB[0], lB[1], lB[2])], V: [[p, 0], [q, 0], [s, t]], ans: [d, e, f] } };
  };

  /* L3-11　圓過原點與兩軸上的點 ⟹ AB 是直徑；切線 ⊥ 半徑 */
  L3.tangentAtAxisPt = function (r) {
    var a = r.int(1, 6) * 2 * r.sign(), b = r.int(1, 6) * 2 * r.sign(), v = r.int(0, 2); while (Math.abs(a) === Math.abs(b)) b = r.int(1, 6) * 2 * r.sign();
    var ln = v === 0 ? [a, b, 0] : v === 1 ? [a, -b, -a * a] : [-a, b, -b * b], at = v === 0 ? '原點' : v === 1 ? T('A') + ' 點' : T('B') + ' 點';
    var pt = v === 0 ? [0, 0] : v === 1 ? [a, 0] : [0, b];
    return { q: '若圓 ' + T('C') + ' 通過原點，且與兩坐標軸分別交於 ' + T('A' + ptTex(a, 0)) + '、' + T('B' + ptTex(0, b)) + '，求圓 ' + T('C') + ' 在' + at + '處的切線方程式（一般式）。',
      a: T(lineTex(ln[0], ln[1], ln[2])),
      h: '$\\angle AOB=90^\\circ$ ⟹ $\\overline{AB}$ 是直徑，圓心是 $\\overline{AB}$ 的中點 $' + ptTex(a / 2, b / 2) + '$。切線 $\\perp$「圓心到切點」的半徑：先算圓心到切點 $' + ptTex(pt[0], pt[1]) + '$ 這條半徑的斜率，切線斜率是它的負倒數，再用點斜式。',
      p: { a: a, b: b, v: v, ans: normLine(ln[0], ln[1], ln[2]) } };
  };

  /* L3-12　切於指定點：切點在線上、在圓上，且半徑 ⊥ 切線 */
  L3.tangentPointParams = function (r) {
    var A = r.pick([1, 2, 3]), t = r.nz(-4, 4), lam = r.pick([1, 2, -2, -3]), x0 = r.int(-3, 4);
    var h = x0 - lam * A, c = t * (1 + lam), s = A * x0 - t * t, k = -(x0 * x0 + t * t - 2 * h * x0 - 2 * c * t);
    var circ = 'x^2+y^2' + term(-2 * h, 'x', false) + term(-2 * c, 'y', false) + '+k=0';
    return { q: '若直線 ' + T('L:' + (A === 1 ? '' : A) + 'x-ty=s') + ' 與圓 ' + T('C:' + circ) + ' 相切於點 ' + T('(' + x0 + ',\\ t)') + '，求數對 ' + T('(k,s,t)') + '。',
      a: T('(k,s,t)=(' + k + ',\\ ' + s + ',\\ ' + t + ')'),
      h: '切點有三個身分：在直線上（給 $s$）、在圓上（給 $k$）、而且「圓心到切點」$\\perp$ 切線（給 $t$）。圓心 $' + ptTex(h, c) + '$；切線斜率 $\\dfrac{' + A + '}{t}$，半徑斜率 $' + (x0 - h < 0 ? '-' : '') + (Math.abs(x0 - h) === 1 ? '(t' + term(-c, '', false) + ')' : '\\dfrac{t' + term(-c, '', false) + '}{' + Math.abs(x0 - h) + '}') + '$，兩者相乘 $=-1$ 先解出 $t$。',
      p: { A: A, x0: x0, h: h, c: c, ans: [k, s, t] } };
  };

  /* L3-13　圓上恰有 n 個點到直線距離為 e：畫兩條平行線，看半徑卡在哪 */
  L3.pointsAtDist = function (r) {
    var nb = r.pick([[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13]]), a = nb[0], b = nb[1] * r.sign(), n = nb[2], e = r.int(1, 3), c, cnt = r.pick([2, 2, 2, 4, 3, 1]);
    c = r.int(n * e + 1, n * e + 40) * r.sign();
    var d = F(Math.abs(c), n), lo = Fr.sub(d, F(e)), hi = Fr.add(d, F(e));
    var ans = cnt === 2 ? Fr.tex(lo) + '\\lt r\\lt ' + Fr.tex(hi) : cnt === 4 ? 'r\\gt ' + Fr.tex(hi) : cnt === 3 ? 'r=' + Fr.tex(hi) : 'r=' + Fr.tex(lo);
    return { q: '若圓 ' + T('C:x^2+y^2=r^2') + '（' + T('r\\gt 0') + '）上恰有' + ['', '一', '兩', '三', '四'][cnt] + '個點到直線 ' + T('L:' + ineqTex(a, b, c, '=')) + ' 的距離為 ' + T(String(e)) + '，求 ' + T('r') + ' 的' + (cnt === 2 || cnt === 4 ? '範圍' : '值') + '。',
      a: T(ans),
      h: '到 $L$ 距離為 $' + e + '$ 的點構成兩條平行線（各在 $L$ 的一側）；圓與這兩條線的交點總數就是題目問的個數。圓心到 $L$ 的距離 $d=\\dfrac{' + Math.abs(c) + '}{' + n + '}$，兩條平行線離圓心分別是 $d-' + e + '$ 與 $d+' + e + '$；讓 $r$ 由小變大，數交點個數 $0,1,2,3,4$ 怎麼變。',
      p: { a: a, b: b, c: c, e: e, cnt: cnt, lo: [lo.n, lo.d], hi: [hi.n, hi.d] } };
  };

  /* L3-14　直線與「上半圓」恰交一點：相切、穿過直徑內部、端點三種情形 */
  L3.halfCircleOne = function (r) {
    var nb = r.pick([[3, 4, 5], [4, 3, 5], [5, 12, 13], [12, 5, 13]]), a = nb[0], b = nb[1], n = nb[2], R = r.int(1, 5), neg = r.int(0, 1), v = r.int(0, 1);
    /* neg=0：ax-by=k（斜率正）；neg=1：ax+by=k（斜率負） */
    var tang = neg === 0 ? -n * R : n * R, lo = neg === 0 ? -a * R + 1 : -a * R, hi = neg === 0 ? a * R : a * R - 1;
    var sum = tang, cnt = 1 + (hi - lo + 1); for (var k = lo; k <= hi; k++) sum += k;
    return { q: '直線 ' + T(ineqTex(a, neg === 0 ? -b : b, 'k', '=')) + ' 與半圓 ' + T('y=\\sqrt{' + (R * R) + '-x^2}') + ' 恰交於一點。若 ' + T('k') + ' 為整數，求所有可能的 ' + T('k') + ' 值' + (v === 0 ? '總和' : '共有幾個') + '。',
      a: v === 0 ? T(String(sum)) : T(String(cnt)) + ' 個',
      h: '把 $k$ 想成直線在平移。三種情形分開看：①與整個圓相切（$\\dfrac{|k|}{' + n + '}=' + R + '$），但切點要在<b>上半圓</b>才算；②直線穿過直徑內部（$x$ 截距 $\\dfrac{k}{' + a + '}$ 介於 $\\pm' + R + '$ 之間），兩交點一上一下，恰一點；③剛好過端點 $(\\pm' + R + ',0)$ 時，另一個交點在上還是在下要<b>單獨驗</b>。',
      p: { a: a, b: neg === 0 ? -b : b, R: R, v: v, ans: [sum, cnt] } };
  };

  /* L3-15　切點弦長：直角三角形斜邊上的高 ×2 */
  L3.chordOfContact = function (r) {
    var h = r.pick([0, 0, 0, 1, -2, 3]), k = h === 0 ? 0 : r.int(-3, 3), rad = r.int(1, 5), px, py, D, tries = 0;
    do { px = h + r.int(-7, 7); py = k + r.int(-7, 7); D = (px - h) * (px - h) + (py - k) * (py - k); } while ((D <= rad * rad || D > 80 || simpSqrt(D * (D - rad * rad)).r > 35) && tries++ < 500);
    var t2 = D - rad * rad, sq = simpSqrt(D * t2), val = surdFrac(2 * rad * sq.c, D, sq.r), f = F(2 * rad * sq.c, D);
    var circ = h === 0 && k === 0 ? 'x^2+y^2=' + rad * rad : stdTex(h, k, rad * rad);
    return { q: '過 ' + T('P' + ptTex(px, py)) + ' 作圓 ' + T('C:' + circ) + ' 的兩條切線，切點為 ' + T('A,B') + '，求 ' + T('\\overline{AB}') + '。',
      a: T('\\overline{AB}=' + val),
      h: '$\\overline{PA}\\perp\\overline{CA}$，而 $\\overline{AB}\\perp\\overline{PC}$：$\\overline{AB}$ 的一半就是直角 $\\triangle PAC$ 斜邊上的高。先算 $\\overline{PC}=' + sqrtTex(D) + '$、切線長 $\\overline{PA}=\\sqrt{' + D + '-' + rad * rad + '}$，再用「兩股相乘 $=$ 斜邊 $\\times$ 高」。',
      p: { P: [px, py], C: [h, k], r: rad, ans: [f.n, f.d, sq.r] } };
  };

  var META_L3 = [['shiftCoincide', '平移後與自己重合'], ['parTwoPts', '兩平行線各過一點、距離已知'], ['triAreaSlopes', '兩線與 x 軸圍三角形'], ['doubleReflectCircle', '連續兩次鏡射的三點共圓'], ['maxProjDist', '投影距離最大'], ['equidistLines', '到三頂點等距的直線'], ['paramRegionArea', '含參數的可行域面積'], ['quadRegionArea', '四條不等式圍區域的面積'], ['chordDistCircle', '過兩點＋弦心距求圓'], ['circumThreeLines', '三直線圍三角形的外接圓'], ['tangentAtAxisPt', '圓過原點與兩軸交點的切線'], ['tangentPointParams', '切於指定點求參數'], ['pointsAtDist', '圓上恰 n 點到直線等距'], ['halfCircleOne', '直線與半圓恰交一點'], ['chordOfContact', '切點弦長']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'shiftCoincide', 'L3-2': 'parTwoPts', 'L3-3': 'triAreaSlopes', 'L3-4': 'doubleReflectCircle', 'L3-5': 'maxProjDist', 'L3-6': 'equidistLines', 'L3-7': 'paramRegionArea', 'L3-8': 'quadRegionArea', 'L3-9': 'chordDistCircle', 'L3-10': 'circumThreeLines', 'L3-11': 'tangentAtAxisPt', 'L3-12': 'tangentPointParams', 'L3-13': 'pointsAtDist', 'L3-14': 'halfCircleOne', 'L3-15': 'chordOfContact' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：二元一次聯立、畢氏定理、配方（國中）；絕對值方程式、分母有理化（高一上 ch1）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  L0.linSys = function (r) {
    var x = r.int(-5, 5), y = r.int(-5, 5), a1, b1, a2, b2;
    do { a1 = r.nz(-4, 4); b1 = r.nz(-4, 4); a2 = r.nz(-4, 4); b2 = r.nz(-4, 4); } while (a1 * b2 - a2 * b1 === 0 || (a1 < 0 && b1 < 0) || (a2 < 0 && b2 < 0));
    var c1 = a1 * x + b1 * y, c2 = a2 * x + b2 * y, e1 = ineqTex(a1, b1, c1, '='), e2 = ineqTex(a2, b2, c2, '=');
    var k1 = Math.abs(b2) / gcd(b1, b2), k2 = Math.abs(b1) / gcd(b1, b2);
    return { q: '解聯立方程式 ' + T('\\begin{cases}' + e1 + '\\\\ ' + e2 + '\\end{cases}') + '。', a: T('(x,y)=' + ptTex(x, y)),
      h: '用加減消去法消 $y$：' + (k1 === 1 && k2 === 1 ? '兩式 $y$ 的係數絕對值已經相同（都是 $' + Math.abs(b1) + '$）' : (k1 === 1 ? '' : '第一式乘 $' + k1 + '$') + (k1 !== 1 && k2 !== 1 ? '、' : '') + (k2 === 1 ? '' : '第二式乘 $' + k2 + '$') + '，讓兩式 $y$ 的係數絕對值相同（都是 $' + Math.abs(b1) * k1 + '$）') + '，' + (b1 * b2 > 0 ? '同號就相減' : '異號就相加') + '；解出 $x$ 再代回任一式求 $y$。',
      p: { l1: [a1, b1, c1], l2: [a2, b2, c2], ans: [x, y] } };
  };
  L0.pythag = function (r) {
    var v = r.int(0, 2), tri = r.pick([[3, 4, 5], [5, 12, 13], [6, 8, 10], [8, 15, 17], [9, 12, 15], [7, 24, 25]]), a, b, ans, qtxt, h;
    if (v === 0) { a = r.int(1, 7); b = r.int(1, 7); ans = a * a + b * b; qtxt = '直角三角形的兩股長為 ' + T(String(a)) + ' 與 ' + T(String(b)) + '，求斜邊長。'; h = '斜邊$^2=' + a + '^2+' + b + '^2$；開根號後記得化簡（把完全平方的因數提出來）。'; }
    else if (v === 1) { a = tri[r.int(0, 1)]; ans = tri[2] * tri[2] - a * a; qtxt = '直角三角形的斜邊長為 ' + T(String(tri[2])) + '、一股長為 ' + T(String(a)) + '，求另一股長。'; h = '另一股$^2=' + tri[2] + '^2-' + a + '^2$——是<b>斜邊平方減</b>，不是加。'; }
    else { a = r.int(1, 6); b = r.int(1, 6); ans = a * a + b * b; qtxt = '在方格紙上，從 ' + T('P') + ' 點向右走 ' + T(String(a)) + ' 格、再向上走 ' + T(String(b)) + ' 格到 ' + T('Q') + ' 點，求 ' + T('\\overline{PQ}') + ' 的長。'; h = '水平位移 $' + a + '$、鉛直位移 $' + b + '$ 是直角三角形的兩股，$\\overline{PQ}$ 是斜邊：$\\overline{PQ}^2=' + a + '^2+' + b + '^2$。這就是本章距離公式的來源。'; }
    return { q: qtxt, a: T(sqrtTex(ans)), h: h, p: { v: v, sq: ans } };
  };
  L0.completeSq = function (r) {
    var h = r.nz(-6, 6), k = r.int(-9, 9), b = 2 * h, c = h * h + k;
    return { q: '將 ' + T('x^2' + term(b, 'x', false) + term(c, '', false)) + ' 配方成 ' + T('(x+h)^2+k') + ' 的形式。', a: T('(x' + term(h, '', false) + ')^2' + term(k, '', false)),
      h: '取一次項係數 $' + b + '$ 的一半 $' + h + '$，平方是 $' + h * h + '$：$x^2' + term(b, 'x', false) + '=(x' + term(h, '', false) + ')^2-' + h * h + '$，常數項再合併。圓的一般式化標準式就是對 $x$、$y$ 各配一次。',
      p: { b: b, c: c, ans: [h, k] } };
  };
  L0.absEq = function (r) {
    var a = r.pick([1, 1, 2, 3]), b = r.int(-7, 7), c = r.int(1, 9), x1 = F(-c - b, a), x2 = F(c - b, a);
    return { q: '解方程式 ' + T('|' + term(a, 'x', true) + term(b, '', false) + '|=' + c) + '。', a: T('x=' + Fr.tex(x1) + '\\ \\text{或}\\ ' + Fr.tex(x2)),
      h: '絕對值等於 $' + c + '$ ⟹ 裡面是 $' + c + '$ 或 $-' + c + '$：$' + term(a, 'x', true) + term(b, '', false) + '=' + c + '$ 或 $' + term(a, 'x', true) + term(b, '', false) + '=-' + c + '$，兩個都要解。點到直線距離公式的分子就是絕對值，反求參數時一定有兩解。',
      p: { a: a, b: b, c: c, ans: [[x1.n, x1.d], [x2.n, x2.d]] } };
  };
  L0.rationalize = function (r) {
    var n = r.pick([2, 3, 5, 6, 7, 10, 13, 8, 12, 18, 20]), k = r.int(1, 12), d = distSimp(k, n);
    return { q: '化簡 ' + T('\\dfrac{' + k + '}{\\sqrt{' + n + '}}') + '（分母有理化，並化到最簡）。', a: T(d.tex),
      h: (simpSqrt(n).c > 1 ? '先化簡分母：$\\sqrt{' + n + '}=' + sqrtTex(n) + '$；再' : '') + '分子分母同乘 $\\sqrt{' + simpSqrt(n).r + '}$，分母就變成整數，最後別忘了約分。本章的距離常常長這樣。',
      p: { k: k, n: n, ans: [d.n, d.d, d.r] } };
  };
  var META_L0 = [['linSys', '二元一次聯立方程式'], ['pythag', '畢氏定理'], ['completeSq', '配方'], ['absEq', '絕對值方程式'], ['rationalize', '分母有理化']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    linSys: { txt: '二元一次聯立方程式（國中）——求兩直線交點、過三點的圓都在解它', link: null },
    pythag: { txt: '畢氏定理（國中）——距離公式、弦長、切線長全部是它', link: null },
    completeSq: { txt: '配方（國中）——圓的一般式化成標準式，要對 x、y 各配一次', link: null },
    absEq: { txt: '絕對值方程式（高一上第一章 數與式）——點到直線距離的分子是絕對值，反求參數一定有兩解', link: '../g10a-ch01/practice.html#L1' },
    rationalize: { txt: '根式化簡與分母有理化（高一上第一章 數與式）——距離的答案常是「整數 ÷ 根號」', link: '../g10a-ch01/practice.html#L1' }
  };

  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  var CONTRAST = {
    'L1.slope2pt': { f: function (p) { return (p.y2 - p.y1) * (p.x2 - p.x1) > 0 ? 1 : ((p.y2 - p.y1) === 0 ? 0 : -1); }, why: '斜率的正負就是直線的走向：往右上是正、往右下是負、水平是 $0$。算之前先看兩點的相對位置，可以檢查正負號有沒有算反。' },
    'L1.midDiv': { f: function (p) { return p.m === p.n; }, why: '中點是 $1:1$ 的內分點，兩個坐標各取平均；比例不是 $1:1$ 時，分點靠近比例「小」的那一端，權重要交叉配。' },
    'L1.interceptForm': { f: function (p) { return p.type; }, why: '一題給截距求直線（用截距式 $\\frac xa+\\frac yb=1$ 再化一般式），一題給直線求截距（令 $y=0$、$x=0$）：同一件事的正反兩個方向。' },
    'L1.parPerp': { f: function (p) { return p.par; }, why: '平行：$x$、$y$ 的係數照抄，只換常數項；垂直：$x$、$y$ 的係數對調、其中一個變號。常數項都用「過已知點」去定。' },
    'L1.symAxis': { f: function (p) { return p.t; }, why: '對 $x$ 軸：$y$ 變號；對 $y$ 軸：$x$ 變號；對原點：兩個都變號；對 $y=x$：兩個坐標對調。先畫個草圖確認落在哪個象限。' },
    'L1.translate': { f: function (p) { return p.h > 0; }, keep: ['k'], why: '向右平移 $h$ 是把 $x$ 換成 $x-h$（不是 $x+h$），向左才是 $x+h$：圖形往右，式子裡反而是減。' },
    'L1.halfPlane': { f: function (p) { return p.strict; }, why: '$\\le$、$\\ge$ 含邊界，剛好落在直線上（代入得 $0$）的點要算；$\\lt$、$\\gt$ 不含邊界，線上的點不算。其餘的點只看代入後的正負。' },
    'L2.minArea': { f: function (p) { return p.t; }, why: '同一條截距式 $\\frac ap+\\frac bq=1$、同一個算幾：問面積就對 $\\frac ap\\cdot\\frac bq$ 用算幾，問 $\\overline{OA}+\\overline{OB}$ 就把 $p+q$ 乘上 $1=\\frac ap+\\frac bq$ 再用算幾；等號成立的條件不一樣。' },
    'L1.circKind': { f: function (p) { return p.kind; }, why: '配方後看右邊：正的是圓、$0$ 是一個點、負的沒有圖形。三種情況只差常數項。' },
    'L1.ptCircle': { f: function (p) { return p.ans; }, why: '把點代進去算「到圓心距離的平方」，跟 $r^2$ 比：小於在內部、等於在圓上、大於在外部。不必開根號。' },
    'L1.lineCircPos': { f: function (p) { return p.ans; }, why: '只比圓心到直線的距離 $d$ 與半徑 $r$：$d\\lt r$ 相交、$d=r$ 相切、$d\\gt r$ 相離。不必解聯立。' },
    'L1.tangentAtPt': { f: function (p) { return p.ans[0] === 0 || p.ans[1] === 0; }, why: '切點在圓的正上下左右時，切線是水平線或鉛直線，直接寫；其他位置才用「切線 $\\perp$ 半徑」求斜率。' },
    'L2.shortestPath': { f: function (p) { return p.t; }, why: '鏡射軸不同，鏡射點的算法就不同：對 $x$ 軸 $y$ 變號、對 $y$ 軸 $x$ 變號、對 $y=x$ 兩坐標對調；之後都是「連線段長 $=$ 最小值」。' },
    'L2.circMinMax': { f: function (p) { return p.t; }, why: '到定點：最遠最近 $=\\overline{QC}\\pm r$；到直線：最遠最近 $=d\\pm r$。共同點是「先算圓心的距離，再加減半徑」。' },
    'L2.tangentExt': { f: function (p) { return p.ans[0][1] === 0 || p.ans[1][1] === 0; }, why: '設斜率 $m$ 只解出一條時，另一條一定是<b>鉛直線</b>（沒有斜率）——過圓外一點的切線永遠有兩條，少一條就是漏了它。' },
    'L3.shiftCoincide': { f: function (p) { return p.p * p.q > 0; }, why: '平移的兩個方向同號（右上／左下）直線斜率為正，異號（右下／左上）斜率為負；斜率決定 $a:b$ 的正負，距離的分子 $|a+b|$ 就跟著不同。' },
    'L3.triAreaSlopes': { f: function (p) { return p.h > 0; }, why: '交點在 $x$ 軸上方或下方，高都是 $|h|$；但 $x$ 截距 $=-\\dfrac hm$ 的正負會跟著換，最後的斜率正負也跟著換。' },
    'L3.maxProjDist': { f: function (p) { return p.Fp[0] === 0 && p.Fp[1] === 0; }, why: '$y=mx$ 恆過原點；$y-q=m(x-p)$ 恆過 $(p,q)$。找到直線繞著轉的那個定點，答案就是「與定點連線垂直」。' },
    'L3.chordDistCircle': { f: function (p) { return p.quad; }, keep: ['d2'], why: '同樣的弦心距，圓心可以在弦的兩側——象限條件就是用來二選一的，兩個候選圓心對弦的中點對稱。' },
    'L3.tangentAtAxisPt': { f: function (p) { return p.v; }, why: '同一個圓，切點換了，半徑的方向就換了；切線永遠垂直「圓心到切點」那條半徑，不是垂直直徑 $\\overline{AB}$。' },
    'L3.pointsAtDist': { f: function (p) { return p.cnt; }, why: '半徑由小變大，圓先碰到近的那條平行線、再碰到遠的那條：交點個數依序是 $0,1,2,3,4$，題目問幾個點就停在哪一段。' },
    'L3.halfCircleOne': { f: function (p) { return p.b < 0; }, why: '斜率正的直線過右端點時另一交點在下半圓（算一點）、過左端點時在上半圓（變兩點）；斜率負的剛好相反。端點一定要單獨驗。' }
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

  /* ── HTML 安全：$…$ 裡的 < > 會被瀏覽器當成標籤，一律改成 \lt \gt ── */
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, simpSqrt: simpSqrt, normLine: normLine, lineTex: lineTex, distSimp: distSimp } };
}));
