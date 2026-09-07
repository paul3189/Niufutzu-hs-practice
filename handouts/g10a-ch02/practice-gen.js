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
             h: '$m=\\dfrac{y_2-y_1}{x_2-x_1}$，分子分母的「誰減誰」順序要一致。',
             p: { x1: x1, y1: y1, x2: x2, y2: y2, ans: [mfr.n, mfr.d] } };
  };

  /* 1-2 兩點距離 */
  L1.dist2pt = function (r) {
    var x1 = r.int(-6, 6), y1 = r.int(-6, 6), dx = r.nz(-7, 7), dy = r.nz(-7, 7);
    var s = dx * dx + dy * dy, q = simpSqrt(s);
    return { q: '求 ' + T('A' + ptTex(x1, y1)) + '、' + T('B' + ptTex(x1 + dx, y1 + dy)) + ' 兩點的距離。',
             a: T('\\overline{AB}=' + sqrtTex(s)),
             h: '$\\sqrt{(x_2-x_1)^2+(y_2-y_1)^2}$，根號內先算好再化簡。',
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
    return { q: q, a: T(fptTex(px, py)),
             h: '分點公式 $P=\\dfrac{nA+mB}{m+n}$：靠近哪一點，那一點的權重就大。',
             p: { x1: x1, y1: y1, x2: x2, y2: y2, m: m, n: n, ans: [px.n, px.d, py.n, py.d] } };
  };

  /* 1-4 點斜式 → 一般式 */
  L1.lineEq = function (r) {
    var x0 = r.int(-5, 5), y0 = r.int(-5, 5), d = r.pick([1, 1, 2, 3]), n = r.nz(-5, 5);
    if (d !== 1) { n = r.nz(-5, 5); while (gcd(n, d) !== 1) n = r.nz(-5, 5); }
    var line = normLine(n, -d, d * y0 - n * x0);
    return { q: '求過點 ' + T(ptTex(x0, y0)) + ' 且斜率為 ' + T(Fr.tex(F(n, d))) + ' 的直線方程式（化為一般式）。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: '點斜式 $y-y_0=m(x-x_0)$，再去分母、移項。',
             p: { x0: x0, y0: y0, mn: n, md: d, ans: line } };
  };

  /* 1-5 兩點式 */
  L1.line2pt = function (r) {
    var x1 = r.int(-5, 5), y1 = r.int(-5, 5), x2, y2;
    do { x2 = r.int(-5, 5); y2 = r.int(-5, 5); } while (x2 === x1 && y2 === y1);
    var line = normLine(y2 - y1, -(x2 - x1), (x2 - x1) * y1 - (y2 - y1) * x1);
    return { q: '求過 ' + T('A' + ptTex(x1, y1)) + '、' + T('B' + ptTex(x2, y2)) + ' 兩點的直線方程式（化為一般式）。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: '先算斜率再用點斜式；$x_1=x_2$ 時是鉛直線 $x=x_1$。',
             p: { x1: x1, y1: y1, x2: x2, y2: y2, ans: line } };
  };

  /* 1-6 截距 */
  L1.interceptForm = function (r) {
    if (r() < 0.5) {
      var a = r.nz(-6, 6), b = r.nz(-6, 6);
      var line = normLine(b, a, -a * b);
      return { q: '求 ' + T('x') + ' 截距為 ' + T(String(a)) + '、' + T('y') + ' 截距為 ' + T(String(b)) + ' 的直線方程式（化為一般式）。',
               a: T(lineTex(line[0], line[1], line[2])),
               h: '截距式 $\\dfrac{x}{a}+\\dfrac{y}{b}=1$，兩邊乘 $ab$。',
               p: { type: 0, a: a, b: b, ans: line } };
    }
    var A = r.nz(-5, 5), B = r.nz(-5, 5), C = r.nz(-9, 9);
    var xi = F(-C, A), yi = F(-C, B);
    return { q: '求直線 ' + T(lineTex(A, B, C)) + ' 的 ' + T('x') + ' 截距與 ' + T('y') + ' 截距。',
             a: T('x') + ' 截距 ' + T(Fr.tex(xi)) + '，' + T('y') + ' 截距 ' + T(Fr.tex(yi)),
             h: '$x$ 截距：令 $y=0$；$y$ 截距：令 $x=0$。',
             p: { type: 1, A: A, B: B, C: C, ans: [xi.n, xi.d, yi.n, yi.d] } };
  };

  /* 1-7 平行與垂直 */
  L1.parPerp = function (r) {
    var a = r.nz(-4, 4), b = r.nz(-4, 4), c = r.int(-7, 7), x0 = r.int(-5, 5), y0 = r.int(-5, 5);
    var par = r() < 0.5, line;
    if (par) line = normLine(a, b, -(a * x0 + b * y0));
    else line = normLine(b, -a, -(b * x0 - a * y0));
    return { q: '求過點 ' + T(ptTex(x0, y0)) + ' 且與直線 ' + T(lineTex(a, b, c)) + (par ? ' 平行' : ' 垂直') + ' 的直線方程式。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: par ? '平行：保留 $x,y$ 的係數，只改常數項，把點代入求常數。' : '垂直：把 $ax+by$ 換成 $bx-ay$（係數對調、一個變號），再代點。',
             p: { a: a, b: b, c: c, x0: x0, y0: y0, par: par ? 1 : 0, ans: line } };
  };

  /* 1-8 兩直線交點 */
  L1.intersect = function (r) {
    var x0 = r.int(-5, 5), y0 = r.int(-5, 5), a1, b1, a2, b2;
    do { a1 = r.nz(-3, 3); b1 = r.nz(-3, 3); a2 = r.nz(-3, 3); b2 = r.nz(-3, 3); } while (a1 * b2 - a2 * b1 === 0);
    var L1t = lineTex(a1, b1, -(a1 * x0 + b1 * y0)), L2t = lineTex(a2, b2, -(a2 * x0 + b2 * y0));
    return { q: '求兩直線 ' + T(L1t) + ' 與 ' + T(L2t) + ' 的交點。',
             a: T(ptTex(x0, y0)),
             h: '聯立解：加減消去一個變數。',
             p: { l1: normLine(a1, b1, -(a1 * x0 + b1 * y0)), l2: normLine(a2, b2, -(a2 * x0 + b2 * y0)), ans: [x0, y0] } };
  };

  /* 2-1 點到直線距離 */
  L1.ptLineDist = function (r) {
    var nv = r.pick(PYTH.concat([[1, 1], [1, -1], [2, 1], [1, 2], [1, -2]]));
    var a = nv[0] * r.sign(), b = nv[1], c = r.int(-9, 9), x0 = r.int(-5, 5), y0 = r.int(-5, 5);
    var num = Math.abs(a * x0 + b * y0 + c), s = a * a + b * b;
    if (num === 0) c += 1, num = Math.abs(a * x0 + b * y0 + c);
    var d = distSimp(num, s);
    return { q: '求點 ' + T(ptTex(x0, y0)) + ' 到直線 ' + T(lineTex(a, b, c)) + ' 的距離。',
             a: T('d=' + d.tex),
             h: '$d=\\dfrac{|ax_0+by_0+c|}{\\sqrt{a^2+b^2}}$，代完記得有理化。',
             p: { a: a, b: b, c: c, x0: x0, y0: y0, ans: [d.n, d.d, d.r] } };
  };

  /* 2-2 兩平行線距離 */
  L1.parDist = function (r) {
    var nv = r.pick(PYTH.concat([[1, 1], [1, -1], [2, 1], [1, 3]]));
    var a = nv[0], b = nv[1] * r.sign(), c1 = r.int(-9, 9), c2;
    do { c2 = r.int(-9, 9); } while (c2 === c1);
    var k = r.pick([1, 1, 2, 3]);
    var d = distSimp(Math.abs(c1 - c2), a * a + b * b);
    return { q: '求兩平行線 ' + T(lineTex(a, b, c1)) + ' 與 ' + T(lineTex(k * a, k * b, k * c2)) + ' 之間的距離。',
             a: T('d=' + d.tex),
             h: '先把兩條的 $x,y$ 係數化成一樣，距離 $=\\dfrac{|c_1-c_2|}{\\sqrt{a^2+b^2}}$。',
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
    return { q: '求以 ' + T('A' + ptTex(P[0][0], P[0][1])) + '、' + T('B' + ptTex(P[1][0], P[1][1])) + '、' + T('C' + ptTex(P[2][0], P[2][1])) + ' 為頂點的三角形面積。',
             a: T(Fr.tex(A)),
             h: '面積 $=\\dfrac12\\,|x_1(y_2-y_3)+x_2(y_3-y_1)+x_3(y_1-y_2)|$，或先平移一點到原點再用 $\\frac12|ad-bc|$。',
             p: { P: P, ans: [A.n, A.d] } };
  };

  /* 2-4 對稱點（課綱內：x 軸、y 軸、原點、y=x） */
  L1.symAxis = function (r) {
    var x0 = r.nz(-6, 6), y0 = r.nz(-6, 6), t = r.int(0, 3);
    var names = ['x 軸', 'y 軸', '原點', '直線 $y=x$'];
    var ans = [[x0, -y0], [-x0, y0], [-x0, -y0], [y0, x0]][t];
    return { q: '求點 ' + T('P' + ptTex(x0, y0)) + ' 對 ' + names[t] + ' 的對稱點。',
             a: T(ptTex(ans[0], ans[1])),
             h: '對 $x$ 軸：$y$ 變號；對 $y$ 軸：$x$ 變號；對原點：都變號；對 $y=x$：$x,y$ 對調。',
             p: { x0: x0, y0: y0, t: t, ans: ans } };
  };

  /* 2-5 平移直線 */
  L1.translate = function (r) {
    var a = r.nz(-4, 4), b = r.nz(-4, 4), c = r.int(-6, 6), h = r.nz(-4, 4), k = r.nz(-4, 4);
    var line = normLine(a, b, c - a * h - b * k);
    return { q: '將直線 ' + T(lineTex(a, b, c)) + ' 向' + (h > 0 ? '右' : '左') + '平移 ' + T(String(Math.abs(h))) + ' 單位、再向' + (k > 0 ? '上' : '下') + '平移 ' + T(String(Math.abs(k))) + ' 單位，求新直線的方程式。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: '右移 $h$、上移 $k$：把 $x$ 換成 $x-h$、$y$ 換成 $y-k$。',
             p: { a: a, b: b, c: c, h: h, k: k, ans: line } };
  };

  /* 2-6 中垂線 */
  L1.perpBisector = function (r) {
    var mx = r.int(-4, 4), my = r.int(-4, 4), u, v;
    do { u = r.int(-4, 4); v = r.int(-4, 4); } while (u === 0 && v === 0);
    var x1 = mx - u, y1 = my - v, x2 = mx + u, y2 = my + v;
    var line = normLine(2 * u, 2 * v, -(2 * u * mx + 2 * v * my));
    return { q: '求 ' + T('A' + ptTex(x1, y1)) + '、' + T('B' + ptTex(x2, y2)) + ' 的中垂線方程式。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: '過中點、且與 $\\overline{AB}$ 垂直：法向量就是 $\\overrightarrow{AB}$。',
             p: { x1: x1, y1: y1, x2: x2, y2: y2, ans: line } };
  };

  /* 3-1 半平面：哪些點滿足不等式 */
  L1.halfPlane = function (r) {
    var a = r.nz(-3, 3), b = r.nz(-3, 3), c = r.int(-5, 5), strict = r() < 0.5, gt = r() < 0.5;
    var pts = [], ans = [], sat = 0;
    for (var i = 0; i < 4; i++) {
      var x0 = r.int(-4, 4), y0 = r.int(-4, 4), v = a * x0 + b * y0 + c, ok;
      if (strict) ok = gt ? v > 0 : v < 0; else ok = gt ? v >= 0 : v <= 0;
      pts.push([x0, y0]); ans.push(ok ? 1 : 0); if (ok) sat++;
    }
    var op = strict ? (gt ? '\\gt' : '\\lt') : (gt ? '\\ge' : '\\le');
    var lhs = lineTex(a, b, c).replace('=0', '');
    var opts = pts.map(function (p, i) { return '(' + (i + 1) + ') ' + T(ptTex(p[0], p[1])); }).join('　');
    var labels = ans.map(function (o, i) { return o ? '(' + (i + 1) + ')' : ''; }).join('');
    return { q: '下列哪些點滿足不等式 ' + T(lhs + op + '0') + '？（可複選）<br>' + opts,
             a: labels || '沒有任何一點滿足',
             h: '把點代進去算 $ax+by+c$ 的正負，注意「$\\ge$」含等號（點可在線上）。',
             p: { a: a, b: b, c: c, strict: strict ? 1 : 0, gt: gt ? 1 : 0, pts: pts, ans: ans } };
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
             h: '線性目標函數的最值一定在頂點：三個頂點代進去比大小就好。',
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
             h: '標準式 $(x-h)^2+(y-k)^2=r^2$，展開就是一般式。',
             p: { h: h, k: k, r: rad, ans: [d, e, f] } };
  };

  /* 4-2 一般式 → 圓心半徑 */
  L1.circGen = function (r) {
    var h = r.int(-5, 5), k = r.int(-5, 5), rad = r.int(1, 7);
    var d = -2 * h, e = -2 * k, f = h * h + k * k - rad * rad;
    var gen = 'x^2+y^2' + term(d, 'x', false) + term(e, 'y', false) + term(f, '', false) + '=0';
    return { q: '求圓 ' + T(gen) + ' 的圓心與半徑。',
             a: '圓心 ' + T(ptTex(h, k)) + '，半徑 ' + T(String(rad)),
             h: '配方：$x^2+dx=(x+\\frac d2)^2-\\frac{d^2}4$；或直接套圓心 $(-\\frac d2,-\\frac e2)$、$r=\\frac12\\sqrt{d^2+e^2-4f}$。',
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
             h: '看 $d^2+e^2-4f$ 的正負：正→圓、零→一點、負→沒有圖形。',
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
             h: '比 $\\overline{PC}^2$ 與 $r^2$ 的大小，不用開根號。',
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
             h: '算圓心到直線的距離 $d$，和半徑比：$d\\lt r$ 相交、$d=r$ 相切、$d\\gt r$ 相離。不要聯立。',
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
             h: '弦心距 $d$、半徑 $r$、半弦長組成直角三角形：弦長 $=2\\sqrt{r^2-d^2}$。',
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
    return { q: '求圓 ' + T(std) + ' 在圓上一點 ' + T('P' + ptTex(x0, y0)) + ' 處的切線方程式。',
             a: T(lineTex(line[0], line[1], line[2])),
             h: '切線 $\\perp$ 半徑 $\\overline{CP}$：法向量取 $\\overrightarrow{CP}=(x_0-h,\\,y_0-k)$，再過 $P$。',
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
             h: '切線長 $=\\sqrt{\\overline{PC}^2-r^2}$（直角三角形 $PTC$）。',
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
    return { q: '設 ' + T('k') + ' 為任意實數，證明直線 ' + T(s + '=0') + ' 恆過一定點，並求此定點。',
             a: T(ptTex(x0, y0)),
             h: '把 $k$ 集中：$(\\cdots)+k(\\cdots)=0$，兩個括號同時為 $0$ 的點就是定點。',
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
    return { q: '若三直線 ' + T('L_1:' + lineTex(a1, 1, c1)) + '、' + T('L_2:' + lineTex(a2, 1, c2)) + '、' + T('L_3:' + L3) + ' 無法圍成三角形，求所有可能的實數 ' + T('k') + '。',
             a: T('k=' + ks.join(',\\ ')),
             h: '三種情形：$L_3\\parallel L_1$、$L_3\\parallel L_2$、或 $L_3$ 通過 $L_1,L_2$ 的交點。',
             p: { a1: a1, c1: c1, a2: a2, c2: c2, b3: b3, c3: c3, ans: ks } };
  };

  /* 2-3 與兩正半軸圍成三角形的最小面積 */
  L2.minArea = function (r) {
    var a = r.int(1, 6), b = r.int(1, 6);
    var line = normLine(b, a, -2 * a * b);
    return { q: '過點 ' + T('P' + ptTex(a, b)) + ' 的直線與 ' + T('x') + '、' + T('y') + ' 軸的正向分別交於 ' + T('A,B') + '，求 ' + T('\\triangle OAB') + ' 面積的最小值，以及此時的直線方程式。',
             a: '最小面積 ' + T(String(2 * a * b)) + '，直線 ' + T(lineTex(line[0], line[1], line[2])),
             h: '設截距式 $\\frac xp+\\frac yq=1$，代點得 $\\frac ap+\\frac bq=1$，算幾不等式：$1\\ge2\\sqrt{\\frac{ab}{pq}}$。',
             p: { a: a, b: b, ans: [2 * a * b].concat(line) } };
  };

  /* 2-4 點對直線的對稱點 */
  L2.reflectPt = function (r) {
    var nv = r.pick([[1, 1], [1, -1], [3, 4], [4, 3], [1, 2], [2, 1], [1, 3], [3, 1], [2, -1], [1, -2], [3, -4], [4, -3]]);
    var a = nv[0], b = nv[1], x0 = r.int(-5, 5), y0 = r.int(-5, 5), t = r.pick([-2, -1, 1, 2]);
    var c = t * (a * a + b * b) - a * x0 - b * y0;
    var xp = x0 - 2 * t * a, yp = y0 - 2 * t * b;
    return { q: '求點 ' + T('P' + ptTex(x0, y0)) + ' 對直線 ' + T('L:' + lineTex(a, b, c)) + ' 的對稱點 ' + T("P'") + '。',
             a: T("P'" + ptTex(xp, yp)),
             h: '設 $P\'(x,y)$：$\\overline{PP\'}$ 中點在 $L$ 上、且 $\\overline{PP\'}\\perp L$（$\\overrightarrow{PP\'}$ 與法向量平行）。',
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
      return { q: '已知 ' + T('A' + ptTex(A[0], A[1])) + '、' + T('B' + ptTex(B[0], B[1])) + '，點 ' + T('P') + ' 在 ' + (t === 0 ? '$x$ 軸' : '$y$ 軸') + ' 上，求 ' + T('\\overline{PA}+\\overline{PB}') + ' 的最小值，以及此時 ' + T('P') + ' 的坐標。',
               a: '最小值 ' + T(minv.tex) + '，' + T('P' + ptTex(P[0], P[1])),
               h: '把 $A$ 對軸鏡射成 $A\'$，$\\overline{PA}+\\overline{PB}\\ge\\overline{A\'B}$；$P$ 是 $\\overline{A\'B}$ 與軸的交點。',
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
             h: '$A$ 對 $y=x$ 的鏡射是 $(y_A,x_A)$；最小值 $=\\overline{A\'B}$，$P=\\overline{A\'B}\\cap\\{y=x\\}$。',
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
             h: '$\\overline{PA}=\\overline{PB}$ 的點在 $\\overline{AB}$ 的中垂線上：中垂線與 $L$ 聯立。',
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
    return { q: '設 ' + T('(x,y)') + ' 滿足 ' + T(S.tex) + '，求 ' + T('f=' + f) + ' 的最大值與最小值。',
             a: '最大值 ' + T(String(mx)) + '（在 ' + T(ptTex(S.V[im][0], S.V[im][1])) + '），最小值 ' + T(String(mn)) + '（在 ' + T(ptTex(S.V[imn][0], S.V[imn][1])) + '）',
             h: '先兩兩聯立求三個頂點（並確認在區域內），再把頂點代入 $f$。',
             p: { ineqs: S.ineqs, V: S.V, p: p, q: q, ans: [mx, mn] } };
  };

  /* 3-2 區域面積 */
  L2.regionArea = function (r) {
    var S = triSystem(r), A = F(S.twice, 2);
    return { q: '求聯立不等式 ' + T(S.tex) + ' 所表示區域的面積。',
             a: T(Fr.tex(A)),
             h: '三條邊界線兩兩聯立得三個頂點，再用坐標面積公式。',
             p: { ineqs: S.ineqs, V: S.V, ans: [A.n, A.d] } };
  };

  /* 3-3 格子點計數 */
  L2.latticeCount = function (r) {
    var a = r.int(1, 3), b = r.int(1, 3), c = r.int(6, 14), cnt = 0;
    for (var x = 0; a * x <= c; x++) cnt += Math.floor((c - a * x) / b) + 1;
    var lhs = term(a, 'x', true) + term(b, 'y', false);
    return { q: '求滿足 ' + T('\\begin{cases}x\\ge0\\\\ y\\ge0\\\\ ' + lhs + '\\le' + c + '\\end{cases}') + ' 的格子點（' + T('x,y') + ' 皆為整數）個數。',
             a: T(String(cnt)) + ' 個',
             h: '固定 $x=0,1,2,\\dots$，逐一數 $y$ 能取幾個整數（$0\\le y\\le\\frac{c-ax}{b}$，取整數部分 $+1$）。',
             p: { a: a, b: b, c: c, ans: cnt } };
  };

  /* 4-1 含參數圓的條件 */
  L2.circParam = function (r) {
    var b = r.nz(-4, 4), m = r.int(1, 5), f = b * b - m * m, sg = r.sign();
    var eq = 'x^2+y^2' + (sg > 0 ? '+2kx' : '-2kx') + term(2 * b, 'y', false) + '+2k^2' + term(f, '', false) + '=0';
    return { q: '設 ' + T('k') + ' 為實數，若方程式 ' + T(eq) + ' 的圖形是一個圓，求 ' + T('k') + ' 的範圍，並求此圓半徑的最大值。',
             a: T('-' + m + '\\lt k\\lt' + m) + '，半徑最大值 ' + T(String(m)) + '（' + T('k=0') + ' 時）',
             h: '配方：$(x\\pm k)^2+(y+b)^2=b^2-f-k^2$，右邊要 $\\gt0$。',
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
             h: '設 $x^2+y^2+dx+ey+f=0$ 代三點解 $d,e,f$；或用兩條中垂線的交點當圓心。',
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
             h: '圓心在 $\\overline{AB}$ 的中垂線上、也在 $L$ 上：兩線聯立得圓心，半徑 $=\\overline{CA}$。',
             p: { a: a, b: b, c: c, A: A, B: B, ans: [h, k, rad] } };
  };

  /* 4-4 圓心已知、與直線相切 */
  L2.circTangentLine = function (r) {
    var nv = r.pick([[3, 4], [4, 3], [3, -4], [4, -3], [5, 12], [12, 5]]);
    var a = nv[0], b = nv[1], s = a * a + b * b, sq = Math.sqrt(s), h = r.int(-5, 5), k = r.int(-5, 5), rad = r.int(1, 6);
    var c = rad * sq * r.sign() - a * h - b * k;
    return { q: '求圓心為 ' + T(ptTex(h, k)) + ' 且與直線 ' + T(lineTex(a, b, c)) + ' 相切的圓方程式。',
             a: T(stdTex(h, k, rad * rad)),
             h: '相切 ⟹ 半徑 $=$ 圓心到直線的距離。',
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
    return { q: '求過點 ' + T('P' + ptTex(P[0], P[1])) + ' 且與圓 ' + T(stdTex(h, k, rad * rad)) + ' 相切的直線方程式（兩條都要）。',
             a: T(lineTex(l1[0], l1[1], l1[2])) + ' 與 ' + T(lineTex(l2[0], l2[1], l2[2])),
             h: '設過 $P$ 的直線 $y-y_0=m(x-x_0)$，令圓心到它的距離 $=r$ 解 $m$；<b>別忘了鉛直線 $x=x_0$ 沒有斜率，要另外檢查</b>。',
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
             h: '弦長 $2\\sqrt{r^2-d^2}$ 反求弦心距 $d$，再由「圓心到直線距離 $=d$」解 $c$（絕對值 ⟹ 兩解）。',
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
               h: '$Q$ 在圓外：最遠 $=\\overline{QC}+r$、最近 $=\\overline{QC}-r$（連圓心那條線上）。',
               p: { t: 0, h: h, k: k, r: rad, Q: Q, ans: [D + rad, D - rad] } };
    }
    var nv = r.pick([[3, 4], [4, 3], [3, -4], [4, -3]]), a = nv[0], b = nv[1], dd = rad + r.int(1, 6);
    var c = 5 * dd * r.sign() - a * h - b * k;
    return { q: '設 ' + T('P') + ' 為圓 ' + T(stdTex(h, k, rad * rad)) + ' 上的動點，求 ' + T('P') + ' 到直線 ' + T(lineTex(a, b, c)) + ' 的最大距離與最小距離。',
             a: '最大 ' + T(String(dd + rad)) + '，最小 ' + T(String(dd - rad)),
             h: '圓心到直線距離 $d\\gt r$（相離）：最遠 $d+r$、最近 $d-r$。',
             p: { t: 1, h: h, k: k, r: rad, a: a, b: b, c: c, ans: [dd + rad, dd - rad] } };
  };

  /* 5-4 直線與圓相交／相切的參數範圍 */
  L2.circLinePosParam = function (r) {
    var nv = r.pick([[3, 4], [4, 3], [3, -4], [4, -3]]), a = nv[0], b = nv[1], h = r.int(-4, 4), k = r.int(-4, 4), rad = r.int(1, 5);
    var base = a * h + b * k, lo = base - 5 * rad, hi = base + 5 * rad;
    var lhs = term(a, 'x', true) + term(b, 'y', false);
    return { q: '直線 ' + T(lhs + '=c') + ' 與圓 ' + T(stdTex(h, k, rad * rad)) + ' 相交於相異兩點，求實數 ' + T('c') + ' 的範圍；並求相切時的 ' + T('c') + ' 值。',
             a: '相交：' + T(lo + '\\lt c\\lt' + hi) + '；相切：' + T('c=' + lo + '\\ \\text{或}\\ ' + hi),
             h: '圓心到直線距離 $\\dfrac{|ah+bk-c|}{5}\\lt r$，解絕對值不等式。',
             p: { a: a, b: b, h: h, k: k, r: rad, ans: [lo, hi] } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['slope2pt', '§1 兩點求斜率'], ['dist2pt', '§1 兩點距離'], ['midDiv', '§1 中點與內分點'], ['lineEq', '§1 點斜式→一般式'],
      ['line2pt', '§1 兩點式'], ['interceptForm', '§1 截距'], ['parPerp', '§1 平行線與垂直線'], ['intersect', '§1 兩直線交點'],
      ['ptLineDist', '§2 點到直線的距離'], ['parDist', '§2 兩平行線的距離'], ['triArea', '§2 三角形面積'], ['symAxis', '§2 對稱點（軸、原點、y=x）'],
      ['translate', '§2 平移直線'], ['perpBisector', '§2 中垂線'],
      ['halfPlane', '§3 半平面判定'], ['lpVertex', '§3 線性規劃：頂點代入'],
      ['circStd', '§4 圓心半徑→方程式'], ['circGen', '§4 一般式→圓心半徑'], ['circKind', '§4 圓、一點或無圖形'], ['ptCircle', '§4 點與圓的位置'],
      ['lineCircPos', '§5 直線與圓的位置關係'], ['chordLen', '§5 弦長'], ['tangentAtPt', '§5 過圓上一點的切線'], ['tangentLen', '§5 切線長']
    ],
    L2: [
      ['lineFamily', '§1 直線族恆過定點'], ['threeLines', '§1 三直線圍不成三角形'], ['minArea', '§1 截距式＋算幾：最小面積'],
      ['reflectPt', '§2 點對直線的對稱點'], ['shortestPath', '§2 反射最短路徑'], ['eqDistOnLine', '§2 直線上與兩點等距的點'],
      ['lpOpt', '§3 線性規劃（不等式組）'], ['regionArea', '§3 不等式區域面積'], ['latticeCount', '§3 格子點計數'],
      ['circParam', '§4 含參數的圓'], ['circ3pt', '§4 過三點的圓'], ['circCenterOnLine', '§4 圓心在直線上'], ['circTangentLine', '§4 與直線相切的圓'],
      ['tangentExt', '§5 過圓外一點的切線'], ['chordParam', '§5 弦長反求參數'], ['circMinMax', '§5 圓上動點的最遠最近'], ['circLinePosParam', '§5 相交／相切的參數範圍']
    ]
  };

  /* ── HTML 安全：$…$ 裡的 < > 會被瀏覽器當成標籤，一律改成 \lt \gt ── */
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

  return { makeRng: makeRng, L1: L1, L2: L2, META: META,
           _util: { gcd: gcd, F: F, Fr: Fr, simpSqrt: simpSqrt, normLine: normLine, lineTex: lineTex, distSimp: distSimp } };
}));
