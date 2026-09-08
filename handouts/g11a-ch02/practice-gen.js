/* ══════════════════════════════════════════════════════════════
   g11a-ch02 指數與對數函數・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示                         p：參數與結構化答案（給 verify_gen11b.py 獨立重算）
   常用對數近似值統一用 log2=0.3010、log3=0.4771、log7=0.8451（題目會標明）。
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
    lt: function (x, y) { return x.n * y.d < y.n * x.d; },
    toNum: function (x) { return x.n / x.d; },
    tex: function (x, small) {
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function simpSqrt(n) { var c = 1, r = n; for (var k = 2; k * k <= r; k++) { while (r % (k * k) === 0) { r /= k * k; c *= k; } } return { c: c, r: r }; }
  function sqrtTex(n) { var s = simpSqrt(n); if (s.r === 1) return String(s.c); return (s.c === 1 ? '' : s.c) + '\\sqrt{' + s.r + '}'; }
  function T(s) { return '$' + s + '$'; }
  function term(coef, v, first) {
    if (coef === 0) return '';
    var sgn = coef < 0 ? '-' : (first ? '' : '+');
    var ab = Math.abs(coef);
    return sgn + (ab === 1 && v ? '' : ab) + v;
  }
  /* 底數的 tex：整數直接寫，分數用 \frac，10 省略成 \log */
  function baseTex(b) { return typeof b === 'number' ? String(b) : Fr.tex(b, true); }
  function logT(b, arg) { return (b === 10 ? '\\log' : '\\log_{' + baseTex(b) + '}') + (arg.length > 1 ? '{' + arg + '}' : arg); }
  function powT(b, e) { return (typeof b === 'number' ? String(b) : '\\left(' + Fr.tex(b, true) + '\\right)') + '^{' + e + '}'; }
  /* 常用對數近似表（四位） */
  var LG = { 2: 0.3010, 3: 0.4771, 7: 0.8451 };
  LG[4] = 2 * LG[2]; LG[5] = 1 - LG[2]; LG[6] = LG[2] + LG[3]; LG[8] = 3 * LG[2]; LG[9] = 2 * LG[3];
  function lg(n) {           /* n 的常用對數近似（只含質因數 2,3,5,7） */
    var v = 0, m = n;
    while (m % 2 === 0) { v += LG[2]; m /= 2; }
    while (m % 3 === 0) { v += LG[3]; m /= 3; }
    while (m % 5 === 0) { v += LG[5]; m /= 5; }
    while (m % 7 === 0) { v += LG[7]; m /= 7; }
    if (m !== 1) throw new Error('lg: ' + n);
    return Math.round(v * 10000) / 10000;
  }
  function lead(m) {         /* 尾數 m∈[0,1) 落在 log k 與 log(k+1) 之間的 k */
    var tab = [0, 0, LG[2], LG[3], LG[4], LG[5], LG[6], LG[7], LG[8], LG[9]];
    var k = 1; for (var i = 2; i <= 9; i++) if (m >= tab[i] - 1e-12) k = i; return k;
  }
  function round4(x) { return Math.round(x * 10000) / 10000; }

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* 1-1 指數律：分數指數的化簡 */
  L1.expLaw = function (r) {
    var p = F(r.nz(-5, 5), r.pick([1, 2, 3])), q = F(r.nz(-5, 5), r.pick([1, 2, 3])), s = F(r.nz(-5, 5), r.pick([1, 2]));
    var ans = Fr.sub(Fr.add(p, q), s);
    return { q: '設 ' + T('a\\gt0') + '，化簡 ' + T('a^{' + Fr.tex(p, true) + '}\\cdot a^{' + Fr.tex(q, true) + '}\\div a^{' + Fr.tex(s, true) + '}=a^{T}') + '，求 ' + T('T') + '。',
             a: T('T=' + Fr.tex(ans)),
             h: '同底相乘指數相加、相除指數相減：$T=p+q-s$，分數先通分。',
             p: { p: [p.n, p.d], q: [q.n, q.d], s: [s.n, s.d], ans: [ans.n, ans.d] } };
  };

  /* 1-2 根式與分數指數求值 */
  L1.radicalVal = function (r) {
    var k = r.pick([2, 2, 3, 3, 5, 10]), n = r.pick([2, 3, 4]), base = Math.pow(k, n);
    if (base > 1000) { n = 2; base = k * k; }
    var m = r.pick([1, 2, 3, -1, -2]);
    var val = Math.pow(k, Math.abs(m)), ansF = m > 0 ? F(val, 1) : F(1, val);
    var e = F(m, n);
    var q = r() < 0.5 ? T(base + '^{' + Fr.tex(e, true) + '}') : (m > 0 ? T('\\sqrt[' + n + ']{' + base + '^{' + m + '}}') : T('\\dfrac{1}{\\sqrt[' + n + ']{' + base + '^{' + (-m) + '}}}'));
    return { q: '求 ' + q + ' 的值。',
             a: T(Fr.tex(ansF)),
             h: '先把底數寫成 $k^n$，$\\left(k^n\\right)^{\\frac mn}=k^m$；負指數是倒數。',
             p: { base: base, m: m, n: n, ans: [ansF.n, ansF.d] } };
  };

  /* 1-3 同底指數比大小 */
  L1.expOrder = function (r) {
    var a = r.pick([2, 3, 5, F(1, 2), F(1, 3)]), es = [], tries = 0;
    while (es.length < 3 && tries++ < 50) { var e = F(r.nz(-6, 6), r.pick([1, 2, 3, 4])); if (!es.some(function (x) { return Fr.eq(x, e); })) es.push(e); }
    var up = typeof a === 'number';
    var names = ['a', 'b', 'c'];
    var idx = [0, 1, 2].sort(function (i, j) { var d = Fr.toNum(es[i]) - Fr.toNum(es[j]); return up ? -d : d; });
    var order = idx.map(function (i) { return names[i]; }).join('\\gt ');
    return { q: '設 ' + T('a=' + powT(a, Fr.tex(es[0], true))) + '、' + T('b=' + powT(a, Fr.tex(es[1], true))) + '、' + T('c=' + powT(a, Fr.tex(es[2], true))) + '，由大到小排列三數。',
             a: T(order),
             h: up ? '底數大於 $1$：指數愈大值愈大，直接比指數。' : '底數在 $0$ 與 $1$ 之間：遞減，指數愈大值反而愈小。',
             p: { base: typeof a === 'number' ? [a, 1] : [a.n, a.d], es: es.map(function (e) { return [e.n, e.d]; }), ans: idx } };
  };

  /* 1-4 同底指數方程式 */
  L1.expEqSame = function (r) {
    var a = r.pick([2, 3, 5]), k = r.pick([2, 3]), p = r.int(-4, 4), q = r.int(-3, 3), m = r.pick([1, 1, 2, -1]);
    if (k * m === 1) m = 2;
    /* a^{x+p} = (a^k)^{m x + q}  ⇒ x + p = k(m x + q) */
    var x = F(p - k * q, k * m - 1);
    var rhsExp = term(m, 'x', true) + term(q, '', false);
    return { q: '解方程式 ' + T(a + '^{' + ('x' + term(p, '', false)) + '}=' + Math.pow(a, k) + '^{' + rhsExp + '}') + '。',
             a: T('x=' + Fr.tex(x)),
             h: '把 $' + Math.pow(a, k) + '$ 寫成 $' + a + '^{' + k + '}$，同底則指數相等。',
             p: { a: a, k: k, p: p, q: q, m: m, ans: [x.n, x.d] } };
  };

  /* 1-5 同底指數不等式（底數大於或小於 1） */
  L1.expIneqSame = function (r) {
    var up = r() < 0.5, a = up ? r.pick([2, 3, 5]) : r.pick([F(1, 2), F(1, 3), F(2, 3)]);
    var p = r.int(-4, 4), q = r.int(-4, 4);
    /* a^{2x+p} > a^{x+q} */
    var bound = q - p;   /* 2x+p > x+q ⇔ x > q-p（底>1） */
    var gt = up;         /* 底>1 時 x > bound；底<1 時 x < bound */
    return { q: '解不等式 ' + T(powT(a, '2x' + term(p, '', false)) + '\\gt' + powT(a, 'x' + term(q, '', false))) + '。',
             a: T('x' + (gt ? '\\gt' : '\\lt') + bound),
             h: up ? '底數大於 $1$，指數大的值大：直接比指數。' : '底數小於 $1$ 是遞減函數，比指數時<b>不等號要反向</b>。',
             p: { up: up ? 1 : 0, p: p, q: q, ans: [gt ? 1 : 0, bound] } };
  };

  /* 1-6 指數函數的平移 */
  L1.expShift = function (r) {
    var a = r.pick([2, 3, 5, F(1, 2)]), h = r.nz(-4, 4), k = r.nz(-5, 5);
    return { q: '將 ' + T('y=' + powT(a, 'x')) + ' 的圖形向' + (h > 0 ? '右' : '左') + '平移 ' + T(String(Math.abs(h))) + ' 單位、再向' + (k > 0 ? '上' : '下') + '平移 ' + T(String(Math.abs(k))) + ' 單位，求新圖形的方程式與漸近線。',
             a: T('y=' + powT(a, 'x' + term(-h, '', false)) + term(k, '', false)) + '，漸近線 ' + T('y=' + k),
             h: '右移 $h$：$x\\to x-h$；上移 $k$：整體加 $k$。漸近線 $y=0$ 跟著上移成 $y=k$。',
             p: { a: typeof a === 'number' ? [a, 1] : [a.n, a.d], h: h, k: k, ans: [h, k] } };
  };

  /* 1-7 換元二次的指數方程式 */
  L1.expQuadEq = function (r) {
    var a = r.pick([2, 3, 5]), u, v;
    do { u = r.int(0, 3); v = r.int(0, 3); } while (u === v);
    var U = Math.pow(a, u), V = Math.pow(a, v);
    var lhs = (a * a) + '^{x}' + term(-(U + V), '\\cdot ' + a + '^{x}', false) + term(U * V, '', false);
    return { q: '解方程式 ' + T(lhs + '=0') + '。',
             a: T('x=' + Math.min(u, v) + '\\ \\text{或}\\ ' + Math.max(u, v)),
             h: '令 $t=' + a + '^x\\gt0$，變成 $t^2-' + (U + V) + 't+' + (U * V) + '=0$，解出 $t$ 再換回 $x$。',
             p: { a: a, u: u, v: v, ans: [Math.min(u, v), Math.max(u, v)] } };
  };

  /* 1-8 每期成長 k 倍 */
  L1.growthTimes = function (r) {
    var Tm = r.pick([2, 3, 4, 5, 6]), k = r.pick([2, 3, 4, 10]), n = r.int(2, 5), unit = r.pick(['小時', '天', '年']);
    if (r() < 0.5) {
      return { q: '某細菌每 ' + T(String(Tm)) + ' ' + unit + '增為原來的 ' + T(String(k)) + ' 倍。經過 ' + T(String(n * Tm)) + ' ' + unit + '後，數量是原來的幾倍？',
               a: T(String(Math.pow(k, n))) + ' 倍',
               h: '先算經過幾個「週期」：$' + (n * Tm) + '\\div' + Tm + '=' + n + '$，倍數就是 $' + k + '^{' + n + '}$。',
               p: { T: Tm, k: k, n: n, type: 0, ans: Math.pow(k, n) } };
    }
    return { q: '某細菌每 ' + T(String(Tm)) + ' ' + unit + '增為原來的 ' + T(String(k)) + ' 倍。要從 ' + T('N') + ' 個增加到 ' + T(Math.pow(k, n) + 'N') + ' 個，需要多少' + unit + '？',
             a: T(String(n * Tm)) + ' ' + unit,
             h: '$' + Math.pow(k, n) + '=' + k + '^{' + n + '}$，共 $' + n + '$ 個週期，每個週期 $' + Tm + '$ ' + unit + '。',
             p: { T: Tm, k: k, n: n, type: 1, ans: n * Tm } };
  };

  /* 2-1 對數的定義：求 log_a b */
  L1.logDef = function (r) {
    var base = r.pick([2, 3, 5, 10, 4, 9, F(1, 2), F(1, 3)]);
    var bk = typeof base === 'number' ? base : base.d, inv = typeof base !== 'number';   /* 底 = bk 或 1/bk */
    var root = { 2: 2, 3: 3, 5: 5, 10: 10, 4: 2, 9: 3 }[bk], pw = { 2: 1, 3: 1, 5: 1, 10: 1, 4: 2, 9: 2 }[bk];   /* 底 = root^pw */
    var m = r.pick([-3, -2, -1, 1, 2, 3, 4, 5]), n = r.pick([1, 1, 1, 2, 3]);
    if (root === 10 && n > 1) n = 1;
    /* 真數 = root^{m/n}，log_{root^pw} = m/(n pw)；底為 1/bk 再變號 */
    var ans = F(inv ? -m : m, n * pw);
    var argT;
    if (n === 1) argT = m >= 0 ? String(Math.pow(root, m)) : '\\dfrac{1}{' + Math.pow(root, -m) + '}';
    else argT = (m >= 0 ? '' : '\\dfrac{1}{') + '\\sqrt' + (n === 3 ? '[3]' : '') + '{' + Math.pow(root, Math.abs(m)) + '}' + (m >= 0 ? '' : '}');
    return { q: '求 ' + T(logT(base, argT)) + ' 的值。',
             a: T(Fr.tex(ans)),
             h: '把真數與底數都寫成同一個數的次方：$\\log_{k^p}k^q=\\dfrac qp$。',
             p: { base: typeof base === 'number' ? [base, 1] : [base.n, base.d], root: root, m: m, n: n, ans: [ans.n, ans.d] } };
  };

  /* 2-2 運算律化簡成整數 */
  L1.logLaw = function (r) {
    var b = r.pick([2, 3, 5, 6, 10]), n = r.int(1, 4), N = Math.pow(b, n);
    var divs = []; for (var u = 2; u < N; u++) if (N % u === 0) divs.push(u);
    if (!divs.length) { n = 2; N = b * b; divs = [b]; }
    var u = r.pick(divs), v = N / u, t = r.int(0, 2);
    var expr, hint;
    if (t === 0) { expr = logT(b, String(u)) + '+' + logT(b, String(v)); hint = '相加變相乘：$\\log_b u+\\log_b v=\\log_b(uv)$。'; }
    else if (t === 1) { var w = r.pick([2, 3, 5, 7]); expr = logT(b, String(N * w)) + '-' + logT(b, String(w)); hint = '相減變相除：$\\log_b(Nw)-\\log_b w=\\log_b N$。'; }
    else { expr = '2' + logT(b, String(u)) + '+' + logT(b, String(v * v)); hint = '係數先搬進去當次方：$2\\log_b u=\\log_b u^2$，再相加。'; }
    return { q: '求 ' + T(expr) + ' 的值。',
             a: T(String(t === 2 ? 2 * n : n)),
             h: hint,
             p: { b: b, n: n, u: u, v: v, t: t, ans: t === 2 ? 2 * n : n } };
  };

  /* 2-3 用 a=log2、b=log3 表示 log N */
  L1.logExpress = function (r) {
    var i = r.int(0, 3), j = r.int(0, 2), k = r.int(0, 2), neg = r() < 0.3;
    if (i + j + k === 0) i = 2;
    var N = Math.pow(2, i) * Math.pow(3, j) * Math.pow(5, k);
    var ca = i - k, cb = j, c0 = k;                 /* log N = i a + j b + k(1-a) */
    if (neg) { ca = -ca; cb = -cb; c0 = -c0; }
    var s = term(ca, 'a', true); s += term(cb, 'b', s === ''); s += term(c0, '', s === '');
    if (s === '') s = '0';
    var arg = neg ? '\\dfrac{1}{' + N + '}' : String(N);
    return { q: '設 ' + T('\\log2=a') + '、' + T('\\log3=b') + '，試以 ' + T('a,b') + ' 表示 ' + T('\\log' + (neg ? '' : ' ') + arg) + '。',
             a: T(s),
             h: '把 $N$ 質因數分解成 $2^i3^j5^k$，而 $\\log5=1-\\log2$。',
             p: { i: i, j: j, k: k, neg: neg ? 1 : 0, ans: [ca, cb, c0] } };
  };

  /* 2-4 換底公式：兩個對數相乘 */
  L1.changeBase = function (r) {
    var pq = r.pick([[2, 3], [2, 5], [3, 5], [2, 7], [3, 2], [5, 2]]), p = pq[0], q = pq[1];
    var i = r.int(1, 3), j = r.int(1, 3), k = r.int(1, 3), l = r.int(1, 3);
    var ans = F(j * l, i * k);   /* log_{p^i} q^j · log_{q^k} p^l = (j/i)(l/k) */
    return { q: '求 ' + T(logT(Math.pow(p, i), String(Math.pow(q, j))) + '\\cdot' + logT(Math.pow(q, k), String(Math.pow(p, l)))) + ' 的值。',
             a: T(Fr.tex(ans)),
             h: '全部換成常用對數：$\\log_{p^i}q^j=\\dfrac{j\\log q}{i\\log p}$，相乘後 $\\log p$、$\\log q$ 會約掉。',
             p: { p: p, q: q, i: i, j: j, k: k, l: l, ans: [ans.n, ans.d] } };
  };

  /* 2-5 位數 */
  L1.digits = function (r) {
    var a = r.pick([2, 3, 6, 7, 12, 15, 18, 24, 35, 42]), n = r.int(10, 60);
    var v = round4(n * lg(a)), d = Math.floor(v + 1e-9) + 1;
    return { q: '已知 ' + T('\\log2\\approx0.3010') + '、' + T('\\log3\\approx0.4771') + '、' + T('\\log7\\approx0.8451') + '。問 ' + T(a + '^{' + n + '}') + ' 是幾位數？',
             a: T(String(d)) + ' 位（' + T('\\log ' + a + '^{' + n + '}\\approx' + v.toFixed(4)) + '）',
             h: '位數 $=$ 首數 $+1$：先算 $n\\log a$，取整數部分再加 $1$。',
             p: { a: a, n: n, ans: d } };
  };

  /* 2-6 首數與尾數的意義 */
  L1.charMant = function (r) {
    if (r() < 0.5) {
      var c = r.int(2, 12), m = r.int(1, 9);
      return { q: '若 ' + T('\\log x=' + c + '.' + m) + '，則 ' + T('x') + ' 的整數部分是幾位數？',
               a: T(String(c + 1)) + ' 位',
               h: '首數 $' + c + '$ ⟹ $10^{' + c + '}\\le x\\lt10^{' + (c + 1) + '}$ ⟹ $' + (c + 1) + '$ 位數。',
               p: { type: 0, c: c, m: m, ans: c + 1 } };
    }
    var k = r.int(1, 8), mm = r.int(1, 9);   /* log y = -k.mm = -(k+1) + (1 - 0.mm) */
    return { q: '若 ' + T('\\log y=-' + k + '.' + mm) + '，則 ' + T('y') + ' 化成小數後，從小數點後第幾位開始出現不為 ' + T('0') + ' 的數字？',
             a: '第 ' + T(String(k + 1)) + ' 位',
             h: '$-' + k + '.' + mm + '=-' + (k + 1) + '+0.' + (10 - mm) + '$：首數 $-' + (k + 1) + '$ ⟹ 第 $' + (k + 1) + '$ 位。',
             p: { type: 1, k: k, mm: mm, ans: k + 1 } };
  };

  /* 2-7 最高位數字 */
  L1.leadDigit = function (r) {
    var a = r.pick([2, 3, 6, 7, 12, 15]), n, v, mant, tries = 0, tab = [LG[2], LG[3], LG[4], LG[5], LG[6], LG[7], LG[8], LG[9]];
    do { n = r.int(8, 40); v = round4(n * lg(a)); mant = round4(v - Math.floor(v)); }
    while (tries++ < 40 && tab.some(function (t) { return Math.abs(mant - t) < 0.006; }));
    var d = lead(mant);
    return { q: '已知 ' + T('\\log2\\approx0.3010') + '、' + T('\\log3\\approx0.4771') + '、' + T('\\log7\\approx0.8451') + '。求 ' + T(a + '^{' + n + '}') + ' 的最高位數字。',
             a: T(String(d)) + '（尾數 ' + T(mant.toFixed(4)) + ' 介於 ' + T('\\log' + d) + ' 與 ' + T('\\log' + (d + 1)) + ' 之間）',
             h: '尾數 $m$ 落在 $\\log k\\le m\\lt\\log(k+1)$ 時，最高位數字就是 $k$。',
             p: { a: a, n: n, ans: d } };
  };

  /* 2-8 簡單對數方程式 */
  L1.logEqSimple = function (r) {
    var a = r.pick([2, 3, 5, 10]), c = r.int(1, 3), p = r.int(-5, 5);
    var x = Math.pow(a, c) - p;
    return { q: '解方程式 ' + T(logT(a, '(x' + term(p, '', false) + ')') + '=' + c) + '。',
             a: T('x=' + x),
             h: '對數定義：$\\log_a M=c\\iff M=a^c$。解完代回檢查真數 $\\gt0$。',
             p: { a: a, c: c, p: p, ans: x } };
  };

  /* 2-9 簡單對數不等式（定義域） */
  L1.logIneqSimple = function (r) {
    var up = r() < 0.6, a = up ? r.pick([2, 3, 10]) : r.pick([F(1, 2), F(1, 3)]);
    var ak = typeof a === 'number' ? a : a.d, c = r.int(1, 3), p = r.int(-4, 4);
    var bound = Math.pow(ak, c);
    if (up) return { q: '解不等式 ' + T(logT(a, '(x' + term(-p, '', false) + ')') + '\\lt' + c) + '。',
                     a: T(p + '\\lt x\\lt' + (p + bound)),
                     h: '先寫定義域 $x\\gt' + p + '$，再由遞增得 $x-' + p + '\\lt' + ak + '^{' + c + '}$，兩者取交集。',
                     p: { up: 1, ak: ak, c: c, p: p, ans: [p, p + bound] } };
    /* 底 <1：log_{1/ak}(x-p) < -c  ⇔  x-p > ak^c */
    return { q: '解不等式 ' + T(logT(a, '(x' + term(-p, '', false) + ')') + '\\lt' + (-c)) + '。',
             a: T('x\\gt' + (p + bound)),
             h: '底數小於 $1$ 是遞減：$\\log_{1/' + ak + '}(x-' + p + ')\\lt-' + c + '$ 等價於 $x-' + p + '\\gt' + ak + '^{' + c + '}$，方向反了。',
             p: { up: 0, ak: ak, c: c, p: p, ans: [p + bound, null] } };
  };

  /* 3-1 對數函數的平移與對稱 */
  L1.logShift = function (r) {
    var a = r.pick([2, 3, 10]), t = r.int(0, 3);
    if (t === 0) {
      var h = r.nz(-4, 4), k = r.nz(-3, 3);
      return { q: '將 ' + T('y=' + logT(a, 'x')) + ' 的圖形向' + (h > 0 ? '右' : '左') + '平移 ' + T(String(Math.abs(h))) + ' 單位、再向' + (k > 0 ? '上' : '下') + '平移 ' + T(String(Math.abs(k))) + ' 單位，求新圖形的方程式與漸近線。',
               a: T('y=' + logT(a, '(x' + term(-h, '', false) + ')') + term(k, '', false)) + '，漸近線 ' + T('x=' + h),
               h: '右移 $h$：$x\\to x-h$；上移 $k$：整體加 $k$。漸近線 $x=0$ 跟著右移成 $x=h$。',
               p: { a: a, t: 0, h: h, k: k, ans: [h, k] } };
    }
    var names = ['$x$ 軸', '$y$ 軸', '直線 $y=x$'];
    var anss = ['y=-' + logT(a, 'x') + '=' + logT(F(1, a), 'x'), 'y=' + logT(a, '(-x)'), 'y=' + a + '^{x}'][t - 1];
    return { q: '求 ' + T('y=' + logT(a, 'x')) + ' 的圖形對 ' + names[t - 1] + ' 對稱後的圖形方程式。',
             a: T(anss),
             h: '對 $x$ 軸：$y\\to-y$；對 $y$ 軸：$x\\to-x$；對 $y=x$：交換 $x,y$（反函數）。',
             p: { a: a, t: t, ans: t } };
  };

  /* 3-2 對數值比大小 */
  L1.logOrder = function (r) {
    var pool = [
      ['\\log_{2}3', Math.log(3) / Math.log(2)], ['\\log_{2}5', Math.log(5) / Math.log(2)], ['\\log_{3}2', Math.log(2) / Math.log(3)],
      ['\\log_{3}5', Math.log(5) / Math.log(3)], ['\\log_{5}2', Math.log(2) / Math.log(5)], ['\\log_{\\frac12}3', -Math.log(3) / Math.log(2)],
      ['\\log_{\\frac13}2', -Math.log(2) / Math.log(3)], ['\\log_{4}8', 1.5], ['\\log_{9}3', 0.5], ['\\log_{2}\\frac13', -Math.log(3) / Math.log(2)],
      ['\\log 50', Math.log10(50)], ['\\log_{5}\\frac{1}{25}', -2], ['\\log_{3}10', Math.log(10) / Math.log(3)], ['1', 1], ['0', 0]];
    var pick = r.shuffle(pool).slice(0, 3);
    while (Math.abs(pick[0][1] - pick[1][1]) < 0.05 || Math.abs(pick[1][1] - pick[2][1]) < 0.05 || Math.abs(pick[0][1] - pick[2][1]) < 0.05) pick = r.shuffle(pool).slice(0, 3);
    var names = ['a', 'b', 'c'];
    var idx = [0, 1, 2].sort(function (i, j) { return pick[j][1] - pick[i][1]; });
    return { q: '設 ' + T('a=' + pick[0][0]) + '、' + T('b=' + pick[1][0]) + '、' + T('c=' + pick[2][0]) + '，由大到小排列三數。',
             a: T(idx.map(function (i) { return names[i]; }).join('\\gt ')),
             h: '先判斷正負（底、真數同在 $1$ 的同側為正），再和 $1$、$2$ 這些整數比：$\\log_23$ 在 $1$ 與 $2$ 之間。',
             p: { vals: pick.map(function (x) { return x[1]; }), ans: idx } };
  };

  /* 3-3 對數的定義域 */
  L1.logDomain = function (r) {
    var p, q; do { p = r.int(-4, 4); q = r.int(-4, 4); } while (p >= q);
    if (r() < 0.5) {
      var a = r.pick([2, 3, 10]);
      var quad = 'x^2' + term(-(p + q), 'x', false) + term(p * q, '', false);
      return { q: '求 ' + T(logT(a, '(' + quad + ')')) + ' 有意義的 ' + T('x') + ' 範圍。',
               a: T('x\\lt' + p + '\\ \\text{或}\\ x\\gt' + q),
               h: '真數 $\\gt0$：$(x-' + p + ')(x-' + q + ')\\gt0$，兩根之外。',
               p: { type: 0, p: p, q: q, ans: [p, q] } };
    }
    /* log_{x-p}(x-q) 且 p<q：底 x-p>0, ≠1；真數 x-q>0 ⇒ x>q，且 x≠p+1（若 p+1>q 才需排除） */
    var excl = (p + 1 > q) ? p + 1 : null;
    return { q: '求 ' + T('\\log_{(x' + term(-p, '', false) + ')}(x' + term(-q, '', false) + ')') + ' 有意義的 ' + T('x') + ' 範圍。',
             a: T('x\\gt' + q + (excl !== null ? '\\ \\text{且}\\ x\\ne' + excl : '')),
             h: '三個條件：底 $\\gt0$、底 $\\ne1$、真數 $\\gt0$，取交集。',
             p: { type: 1, p: p, q: q, ans: [q, excl] } };
  };

  /* 3-4 對數換元的二次最值 */
  L1.logQuadMin = function (r) {
    var a = r.pick([2, 3, 10]), h = r.nz(-3, 3), k = r.int(-5, 5);
    /* y = (log_a x)^2 - 2h log_a x + (h^2 + k) = (t-h)^2 + k */
    var c = h * h + k;
    var expr = '\\left(' + logT(a, 'x') + '\\right)^2' + term(-2 * h, logT(a, 'x'), false) + term(c, '', false);
    var xm = h >= 0 ? String(Math.pow(a, h)) : '\\dfrac{1}{' + Math.pow(a, -h) + '}';
    return { q: '求 ' + T('y=' + expr) + '（' + T('x\\gt0') + '）的最小值，以及此時的 ' + T('x') + '。',
             a: '最小值 ' + T(String(k)) + '，在 ' + T('x=' + xm),
             h: '令 $t=' + logT(a, 'x') + '$（$t$ 可取任意實數），配方 $(t-' + h + ')^2' + term(k, '', false) + '$。',
             p: { a: a, h: h, k: k, ans: [k, h] } };
  };

  /* 3-5 對數刻度：地震與分貝 */
  L1.logScale = function (r) {
    if (r() < 0.5) {
      var d = r.pick([2, 4]), m1 = r.int(5, 7);
      return { q: '地震規模 ' + T('M') + ' 與能量 ' + T('E') + ' 的關係為 ' + T('\\log E=4.8+1.5M') + '。規模 ' + T(String(m1 + d)) + ' 的地震釋放的能量是規模 ' + T(String(m1)) + ' 的幾倍？',
               a: T('10^{' + (1.5 * d) + '}=' + Math.pow(10, 1.5 * d)) + ' 倍',
               h: '兩式相減：$\\log E_1-\\log E_2=1.5(M_1-M_2)$，倍數 $=10^{1.5\\Delta M}$。',
               p: { type: 0, d: d, ans: Math.pow(10, 1.5 * d) } };
    }
    var n = r.pick([10, 100, 1000]), d0 = r.pick([40, 50, 60, 70]);
    return { q: '分貝 ' + T('d=10\\log\\dfrac{I}{I_0}') + '。一台機器的噪音是 ' + T(String(d0)) + ' 分貝，' + T(String(n)) + ' 台同型機器同時運轉（強度相加）約為幾分貝？',
             a: T(String(d0 + 10 * Math.round(Math.log10(n)))) + ' 分貝',
             h: '強度變 $n$ 倍，分貝加 $10\\log n$；$n=10^k$ 時就是加 $10k$。',
             p: { type: 1, n: n, d0: d0, ans: d0 + 10 * Math.round(Math.log10(n)) } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 1-1 對稱式換元的最值：f = A(a^{2x}+a^{-2x}) - B(a^x+a^{-x}) + C */
  L2.expSymmMin = function (r) {
    var a = r.pick([2, 3]), A = r.pick([1, 1, 2, 3]), B = r.pick([2, 3, 4, 5, 6, 7, 8, 10, 12]), C = r.int(-6, 9);
    /* t = a^x + a^{-x} ≥ 2；a^{2x}+a^{-2x} = t²-2；f = A t² - B t + (C - 2A) */
    var t0 = F(B, 2 * A), c2 = C - 2 * A, tmin, fmin;
    if (Fr.toNum(t0) >= 2) { tmin = t0; fmin = Fr.add(Fr.sub(Fr.mul(F(A, 1), Fr.mul(t0, t0)), Fr.mul(F(B, 1), t0)), F(c2, 1)); }
    else { tmin = F(2, 1); fmin = F(4 * A - 2 * B + c2, 1); }
    var expr = term(A, '\\left(' + (a * a) + '^{x}+' + (a * a) + '^{-x}\\right)', true) + term(-B, '\\left(' + a + '^{x}+' + a + '^{-x}\\right)', false) + term(C, '', false);
    var where = Fr.eq(tmin, F(2, 1)) ? T('x=0') : T(a + '^{x}+' + a + '^{-x}=' + Fr.tex(tmin));
    return { q: '設 ' + T('x') + ' 為實數，' + T('f(x)=' + expr) + '，求 ' + T('f(x)') + ' 的最小值。',
             a: '最小值 ' + T(Fr.tex(fmin)) + '（在 ' + where + '）',
             h: '令 $t=' + a + '^x+' + a + '^{-x}\\ge2$（算幾），則 $' + (a * a) + '^x+' + (a * a) + '^{-x}=t^2-2$；二次函數的頂點若在 $t\\lt2$，最小值在端點 $t=2$。',
             p: { a: a, A: A, B: B, C: C, ans: [fmin.n, fmin.d, tmin.n, tmin.d] } };
  };

  /* 1-2 換元二次的指數不等式 */
  L2.expIneqQuad = function (r) {
    var a = r.pick([2, 3, 5]), u, v;
    do { u = r.int(-1, 3); v = r.int(-1, 3); } while (u >= v);
    var U = Math.pow(a, u), V = Math.pow(a, v), Uf = F(U < 1 ? 1 : U, U < 1 ? a : 1), Vf = F(V, 1);
    var sum = Fr.add(Uf, Vf), prod = Fr.mul(Uf, Vf), strict = r() < 0.5;
    /* a^{2x} - (U+V) a^x + UV < 0 ；分數係數乘以公分母 */
    var den = sum.d > prod.d ? sum.d : prod.d; den = (sum.d * prod.d) / gcd(sum.d, prod.d);
    var c2 = den, c1 = -sum.n * (den / sum.d), c0 = prod.n * (den / prod.d);
    var lhs = term(c2, (a * a) + '^{x}', true) + term(c1, '\\cdot ' + a + '^{x}', false) + term(c0, '', false);
    var op = strict ? '\\lt' : '\\le', lt = strict ? '\\lt' : '\\le';
    return { q: '解不等式 ' + T(lhs + op + '0') + '。',
             a: T(u + lt + ' x' + lt + ' ' + v),
             h: '令 $t=' + a + '^x\\gt0$ 化成二次不等式，解出 $t$ 的範圍後再取 $\\log_' + a + '$。',
             p: { a: a, u: u, v: v, strict: strict ? 1 : 0, c: [c2, c1, c0], ans: [u, v] } };
  };

  /* 1-3 乘積定值的算幾（直線上動點） */
  L2.expAMGM = function (r) {
    var a = r.pick([2, 3]), m = r.pick([1, 2]), n = r.pick([1, 2, 3]), c = r.int(2, 6);
    if (m === n && m === 1) m = 2;
    var line = term(m, 'x', true) + term(n, 'y', false) + '=' + c;
    var minv = 2 * Math.sqrt(Math.pow(a, c)), s = simpSqrt(Math.pow(a, c));
    var minTex = s.r === 1 ? String(2 * s.c) : (2 * s.c) + '\\sqrt{' + s.r + '}';
    var xe = F(c, 2 * m), ye = F(c, 2 * n);
    return { q: '當 ' + T('(x,y)') + ' 在直線 ' + T(line) + ' 上變動時，求 ' + T(Math.pow(a, m) + '^{x}+' + Math.pow(a, n) + '^{y}') + ' 的最小值，以及此時的 ' + T('(x,y)') + '。',
             a: '最小值 ' + T(minTex) + '，在 ' + T('(x,y)=\\left(' + Fr.tex(xe, true) + ',' + Fr.tex(ye, true) + '\\right)'),
             h: '兩項相乘 $=' + a + '^{' + m + 'x+' + n + 'y}=' + a + '^{' + c + '}$ 是定值 ⟹ 算幾：和 $\\ge2\\sqrt{' + a + '^{' + c + '}}$，等號在兩項相等。',
             p: { a: a, m: m, n: n, c: c, ans: [2 * s.c, s.r, xe.n, xe.d, ye.n, ye.d] } };
  };

  /* 1-4 指數在區間上的最值（指數是二次式） */
  L2.expIntervalMax = function (r) {
    var a = r.pick([2, 3, F(1, 2)]), up = typeof a === 'number', h = r.int(-2, 3), k = r.int(-3, 3), l = h - r.int(0, 3), rr = h + r.int(1, 4);
    if (l === rr) rr = l + 2;
    /* g(x) = (x-h)^2 + k = x^2 - 2h x + h^2 + k，區間 [l, rr] */
    var g = function (x) { return (x - h) * (x - h) + k; };
    var vals = [g(l), g(rr)]; if (l <= h && h <= rr) vals.push(g(h));
    var gmax = Math.max.apply(null, vals), gmin = Math.min.apply(null, vals);
    var ymax = up ? gmax : gmin, ymin = up ? gmin : gmax;   /* 指數 */
    var gT = 'x^2' + term(-2 * h, 'x', false) + term(h * h + k, '', false);
    var eT = function (e) { return powT(a, String(e)); };
    return { q: '設 ' + T(l + '\\le x\\le' + rr) + '，求 ' + T('y=' + powT(a, gT)) + ' 的最大值與最小值。',
             a: '最大值 ' + T(eT(ymax)) + '，最小值 ' + T(eT(ymin)),
             h: '先求指數 $g(x)=(x' + term(-h, '', false) + ')^2' + term(k, '', false) + '$ 在區間上的範圍（看頂點在不在區間內、比兩端點），' + (up ? '底數大於 $1$：指數最大值給最大值。' : '底數小於 $1$：指數最大反而給最小值。'),
             p: { a: up ? [a, 1] : [a.n, a.d], h: h, k: k, l: l, r: rr, ans: [ymax, ymin] } };
  };

  /* 1-5 半衰期 */
  L2.halfLife = function (r) {
    var Tm = r.pick([2, 3, 4, 5, 6, 8, 10, 12]), k = r.int(2, 5), unit = r.pick(['年', '天', '小時']);
    var pct = [50, 25, 12.5, 6.25, 3.125][k - 1];
    if (r() < 0.5) {
      return { q: '某放射性物質的半衰期為 ' + T(String(Tm)) + ' ' + unit + '。經過多久後，剩餘量會變成原來的 ' + T(pct + '\\%') + '？',
               a: T(String(k * Tm)) + ' ' + unit,
               h: '$' + pct + '\\%=\\left(\\frac12\\right)^{' + k + '}$，就是 $' + k + '$ 個半衰期。',
               p: { T: Tm, k: k, type: 0, ans: k * Tm } };
    }
    return { q: '某放射性物質經過 ' + T(String(k * Tm)) + ' ' + unit + '後，剩餘量為原來的 ' + T(pct + '\\%') + '。求此物質的半衰期。',
             a: T(String(Tm)) + ' ' + unit,
             h: '剩 $' + pct + '\\%=\\left(\\frac12\\right)^{' + k + '}$ ⟹ 經過了 $' + k + '$ 個半衰期，$' + (k * Tm) + '\\div' + k + '$。',
             p: { T: Tm, k: k, type: 1, ans: Tm } };
  };

  /* 1-6 複利／成長：至少幾期 */
  L2.compoundYears = function (r) {
    var tab = { 3: 0.0128, 4: 0.0170, 5: 0.0212, 6: 0.0253, 8: 0.0334, 10: 0.0414, 20: 0.0792 };
    var rate, k, lg1, lgk, ratio, tries = 0;
    do {
      rate = r.pick([3, 4, 5, 6, 8, 10, 20]); k = r.pick([2, 3, 5, 10]);
      lg1 = tab[rate]; lgk = { 2: 0.3010, 3: 0.4771, 5: 0.6990, 10: 1 }[k]; ratio = lgk / lg1;
      var trueRatio = Math.log10(k) / Math.log10(1 + rate / 100);   /* 表值與真值取整要一致，否則換一組 */
    } while ((Math.abs(ratio - Math.round(ratio)) < 0.12 || Math.floor(ratio) !== Math.floor(trueRatio)) && tries++ < 60);
    var n = Math.floor(ratio) + 1;
    var rateT = rate < 10 ? '1.0' + rate : '1.' + rate;
    return { q: '某城市人口每年成長 ' + T(rate + '\\%') + '。至少要經過幾年，人口才會超過現在的 ' + T(String(k)) + ' 倍？（' + T('\\log' + rateT + '\\approx' + lg1.toFixed(4)) + (k === 10 ? '' : '、' + T('\\log' + k + '\\approx' + lgk.toFixed(4))) + '）',
             a: T(String(n)) + ' 年',
             h: '$(1+r)^n\\gt k$ 兩邊取 $\\log$：$n\\gt\\dfrac{\\log k}{\\log(1+r)}\\approx' + ratio.toFixed(2) + '$，取下一個整數。',
             p: { rate: rate, k: k, lg1: lg1, lgk: lgk, ans: n } };
  };

  /* 2-1 對數換元的區間最值 */
  L2.logQuadRange = function (r) {
    var a = r.pick([2, 3]), h = r.int(-1, 3), k = r.int(-4, 4), l = h - r.int(0, 3), rr = h + r.int(1, 3);
    if (l === rr) rr = l + 1;
    /* y = (log_a x - h)^2 + k，t ∈ [l, rr] */
    var g = function (t) { return (t - h) * (t - h) + k; };
    var cand = [[l, g(l)], [rr, g(rr)]]; if (l <= h && h <= rr) cand.push([h, g(h)]);
    var mx = cand.reduce(function (p, c) { return c[1] > p[1] ? c : p; }), mn = cand.reduce(function (p, c) { return c[1] < p[1] ? c : p; });
    var pw = function (e) { return e >= 0 ? String(Math.pow(a, e)) : '\\dfrac{1}{' + Math.pow(a, -e) + '}'; };
    var expr = '\\left(' + logT(a, 'x') + '\\right)^2' + term(-2 * h, logT(a, 'x'), false) + term(h * h + k, '', false);
    return { q: '設 ' + T(pw(l) + '\\le x\\le' + pw(rr)) + '，求 ' + T('y=' + expr) + ' 的最大值與最小值。',
             a: '最大值 ' + T(String(mx[1])) + '（' + T('x=' + pw(mx[0])) + '），最小值 ' + T(String(mn[1])) + '（' + T('x=' + pw(mn[0])) + '）',
             h: '令 $t=' + logT(a, 'x') + '$，則 $' + l + '\\le t\\le' + rr + '$，$y=(t' + term(-h, '', false) + ')^2' + term(k, '', false) + '$：頂點在不在區間內決定最小值在哪；最大值一定在端點。',
             p: { a: a, h: h, k: k, l: l, r: rr, ans: [mx[1], mx[0], mn[1], mn[0]] } };
  };

  /* 2-2 對數換元的二次方程式 */
  L2.logEqQuad = function (r) {
    var a = r.pick([2, 3, 10]), u, v;
    do { u = r.int(-2, 3); v = r.int(-2, 3); } while (u >= v);
    var pw = function (e) { return e >= 0 ? String(Math.pow(a, e)) : '\\dfrac{1}{' + Math.pow(a, -e) + '}'; };
    var expr = '\\left(' + logT(a, 'x') + '\\right)^2' + term(-(u + v), logT(a, 'x'), false) + term(u * v, '', false);
    return { q: '解方程式 ' + T(expr + '=0') + '。',
             a: T('x=' + pw(u) + '\\ \\text{或}\\ ' + pw(v)),
             h: '令 $t=' + logT(a, 'x') + '$，因式分解 $(t' + term(-u, '', false) + ')(t' + term(-v, '', false) + ')=0$。',
             p: { a: a, u: u, v: v, ans: [u, v] } };
  };

  /* 2-3 真數相乘的對數方程式（含增根） */
  L2.logEqProduct = function (r) {
    var a = r.pick([2, 3, 5, 10]), c = r.pick([1, 2, 2, 3]), N = Math.pow(a, c), pairs = [];
    for (var m = 2; m * m <= N * 4 && m <= 60; m++) if (N % m === 0 && N / m < m) pairs.push([m, m - N / m]);  /* x=m, x-k = N/m ⇒ k = m - N/m */
    if (!pairs.length) { c = 2; N = a * a; pairs = [[a * a, a * a - 1]]; }
    var pr = r.pick(pairs), m0 = pr[0], k = pr[1];
    return { q: '解方程式 ' + T(logT(a, 'x') + '+' + logT(a, '(x' + term(-k, '', false) + ')') + '=' + c) + '。',
             a: T('x=' + m0) + '（另一根 ' + T('x=' + (k - m0)) + ' 使真數為負，不合）',
             h: '合併成 $x(x-' + k + ')=' + N + '$ 解二次方程式；<b>解完一定要代回檢查真數 $\\gt0$</b>。',
             p: { a: a, c: c, k: k, ans: m0 } };
  };

  /* 2-4 底數大於或小於 1 的對數不等式 */
  L2.logIneqBase = function (r) {
    var up = r() < 0.5, a = up ? r.pick([2, 3, 10]) : r.pick([F(1, 2), F(1, 3), F(1, 5)]);
    var p = r.int(-3, 3), q = p + r.pick([2, 4, 6]), mid = (p + q) / 2;
    /* log_a(x-p) > log_a(q-x)，定義域 p<x<q */
    var ansL = up ? mid : p, ansR = up ? q : mid;
    return { q: '解不等式 ' + T(logT(a, '(x' + term(-p, '', false) + ')') + '\\gt' + logT(a, '(' + q + '-x)')) + '。',
             a: T(ansL + '\\lt x\\lt' + ansR),
             h: '定義域 $' + p + '\\lt x\\lt' + q + '$；' + (up ? '底數大於 $1$ ⟹ 真數保持方向：$x-' + p + '\\gt' + q + '-x$。' : '底數小於 $1$ ⟹ 真數方向<b>反過來</b>：$x-' + p + '\\lt' + q + '-x$。'),
             p: { up: up ? 1 : 0, p: p, q: q, ans: [ansL, ansR] } };
  };

  /* 2-5 對數連加（望遠鏡） */
  L2.logSumTele = function (r) {
    var b = r.pick([10, 2, 3]), m = r.pick([1, 2, 3, 5]), j = r.int(1, 3), n = m * Math.pow(b, j) - 1;
    return { q: '求 ' + T(logT(b, '\\left(1+\\dfrac{1}{' + m + '}\\right)') + '+' + logT(b, '\\left(1+\\dfrac{1}{' + (m + 1) + '}\\right)') + '+\\cdots+' + logT(b, '\\left(1+\\dfrac{1}{' + n + '}\\right)')) + ' 的值。',
             a: T(String(j)),
             h: '$1+\\frac1k=\\frac{k+1}{k}$，相加變相乘後分子分母對消：$\\log_{' + baseTex(b) + '}\\dfrac{' + (n + 1) + '}{' + m + '}$。',
             p: { b: b, m: m, n: n, ans: j } };
  };

  /* 2-6 位數與最高位數字 */
  L2.digitsLead = function (r) {
    var a = r.pick([2, 3, 6, 7, 12, 15, 18, 21]), n, v, mant, tries = 0, tab = [LG[2], LG[3], LG[4], LG[5], LG[6], LG[7], LG[8], LG[9]];
    do { n = r.int(10, 50); v = round4(n * lg(a)); mant = round4(v - Math.floor(v)); }
    while (tries++ < 40 && tab.some(function (t) { return Math.abs(mant - t) < 0.006; }));
    var d = Math.floor(v) + 1, ld = lead(mant);
    return { q: '已知 ' + T('\\log2\\approx0.3010') + '、' + T('\\log3\\approx0.4771') + '、' + T('\\log7\\approx0.8451') + '。求 ' + T(a + '^{' + n + '}') + ' 的位數與最高位數字。',
             a: T(String(d)) + ' 位數，最高位數字 ' + T(String(ld)) + '（' + T('\\log ' + a + '^{' + n + '}\\approx' + v.toFixed(4)) + '）',
             h: '首數定位數（$+1$）、尾數定最高位（落在 $\\log k$ 與 $\\log(k+1)$ 之間）。',
             p: { a: a, n: n, ans: [d, ld] } };
  };

  /* 2-7 小數點後第幾位開始不為 0、該數字為何 */
  L2.decimalFirst = function (r) {
    var base = r.pick([2, 3, 5, 6, 7, 8, 9, 12]), n, v, pos, mant, tries = 0, tab = [LG[2], LG[3], LG[4], LG[5], LG[6], LG[7], LG[8], LG[9]];
    do { n = r.int(8, 40); v = -round4(n * lg(base)); pos = -Math.floor(v); mant = round4(v - Math.floor(v)); }
    while (tries++ < 40 && (mant < 0.006 || tab.some(function (t) { return Math.abs(mant - t) < 0.006; })));
    var dg = lead(mant);
    return { q: '已知 ' + T('\\log2\\approx0.3010') + '、' + T('\\log3\\approx0.4771') + '、' + T('\\log7\\approx0.8451') + '。將 ' + T('\\left(\\dfrac{1}{' + base + '}\\right)^{' + n + '}') + ' 化為小數：(1) 從小數點後第幾位開始出現不為 ' + T('0') + ' 的數字？(2) 該數字為何？',
             a: '(1) 第 ' + T(String(pos)) + ' 位　(2) ' + T(String(dg)) + '（' + T('\\log=' + (-n * lg(base)).toFixed(4) + '=-' + pos + '+' + mant.toFixed(4)) + '）',
             h: '把負的 $\\log$ 寫成「負整數 $+$ 正小數」：負整數的絕對值是位置，正小數（尾數）決定數字。',
             p: { base: base, n: n, ans: [pos, dg] } };
  };

  /* 3-1 對數函數上的點：多選判斷 */
  L2.logPointSym = function (r) {
    var b = r.pick([2, 3, 10]);
    var pool = [
      ['(b,\\ a)\\ \\text{在}\\ y=' + b + '^{x}\\ \\text{上}', true],
      ['\\left(\\dfrac1a,\\ -b\\right)\\ \\text{在}\\ y=' + logT(b, 'x') + '\\ \\text{上}', true],
      ['(' + b + 'a,\\ b+1)\\ \\text{在}\\ y=' + logT(b, 'x') + '\\ \\text{上}', true],
      ['(a^2,\\ 2b)\\ \\text{在}\\ y=' + logT(b, 'x') + '\\ \\text{上}', true],
      ['(a+' + b + ',\\ b+1)\\ \\text{在}\\ y=' + logT(b, 'x') + '\\ \\text{上}', false],
      ['(-a,\\ b)\\ \\text{在}\\ y=' + logT(b, 'x') + '\\ \\text{上}', false],
      ['(a,\\ -b)\\ \\text{在}\\ y=' + logT(F(1, b), 'x') + '\\ \\text{上}', true],
      ['(' + (b * b) + 'a,\\ ' + (b * b) + 'b)\\ \\text{在}\\ y=' + logT(b, 'x') + '\\ \\text{上}', false],
      ['\\left(\\dfrac{a}{' + b + '},\\ b-1\\right)\\ \\text{在}\\ y=' + logT(b, 'x') + '\\ \\text{上}', true],
      ['(b,\\ a)\\ \\text{在}\\ y=' + logT(b, 'x') + '\\ \\text{上}', false],
      ['(2a,\\ 2b)\\ \\text{在}\\ y=' + logT(b, 'x') + '\\ \\text{上}', false],
      ['(-a,\\ b)\\ \\text{在}\\ y=' + logT(b, '(-x)') + '\\ \\text{上}', true]];
    var pick = r.shuffle(pool).slice(0, 5);
    var opts = pick.map(function (o, i) { return '(' + (i + 1) + ') ' + T(o[0]); }).join('　');
    var labels = pick.map(function (o, i) { return o[1] ? '(' + (i + 1) + ')' : ''; }).join('');
    return { q: '已知 ' + T('(a,b)') + ' 在 ' + T('y=' + logT(b, 'x')) + ' 的圖形上（' + T('a\\gt0') + '）。下列哪些敘述正確？（可複選）<br>' + opts,
             a: labels || '皆不正確',
             h: '只有一件事可用：$b=' + logT(b, 'a') + '$。把每個點代進對應的函數，用運算律核對。',
             p: { b: b, ans: pick.map(function (o) { return o[1] ? 1 : 0; }), keys: pick.map(function (o) { return pool.findIndex(function (x) { return x[0] === o[0]; }); }) } };
  };

  /* 3-2 兩種物質的半衰期比 */
  L2.decayRatio = function (r) {
    var TA = r.pick([2, 3, 4, 6]), TB = r.pick([1, 2, 3, 4, 6, 12]);
    while (TB === TA) TB = r.pick([1, 2, 3, 4, 6, 12]);
    var Lc = TA * TB / gcd(TA, TB), t = Lc * r.int(1, 3), e = t / TB - t / TA;   /* A/B = 2^{t/TB - t/TA} */
    var ratio = Math.pow(2, Math.abs(e));
    return { q: '甲、乙兩物質的半衰期分別為 ' + T(String(TA)) + ' 天與 ' + T(String(TB)) + ' 天，開始時質量相等。經過 ' + T(String(t)) + ' 天後，' + (e >= 0 ? '甲' : '乙') + '的質量是' + (e >= 0 ? '乙' : '甲') + '的幾倍？',
             a: T(String(ratio)) + ' 倍',
             h: '各自寫成 $\\left(\\frac12\\right)^{t/T}$ 再相除：$2^{t/T_B-t/T_A}$，指數是整數。',
             p: { TA: TA, TB: TB, t: t, ans: ratio } };
  };

  /* 3-3 分貝疊加 */
  L2.dbMulti = function (r) {
    if (r() < 0.5) {
      var n = r.pick([2, 4, 8, 5, 20, 50]), d0 = r.pick([40, 50, 60, 70, 80]);
      var add = 10 * Math.log10(n), lgn = { 2: 0.3010, 4: 0.6020, 8: 0.9030, 5: 0.6990, 20: 1.3010, 50: 1.6990 }[n];
      var ans = Math.round(d0 + 10 * lgn);
      return { q: '分貝 ' + T('d=10\\log\\dfrac{I}{I_0}') + '。一個人說話為 ' + T(String(d0)) + ' 分貝，' + T(String(n)) + ' 個人同時說話（強度相加）約為幾分貝？（四捨五入至整數，' + T('\\log2\\approx0.3010') + '）',
               a: T(String(ans)) + ' 分貝',
               h: '強度 $n$ 倍 ⟹ 分貝加 $10\\log n=10\\times' + lgn.toFixed(4) + '$。',
               p: { type: 0, n: n, d0: d0, ans: ans } };
    }
    var d1 = r.pick([40, 50, 60]), d2 = d1 + r.pick([10, 20, 30]);
    return { q: '分貝 ' + T('d=10\\log\\dfrac{I}{I_0}') + '。' + T(String(d2)) + ' 分貝的聲音強度是 ' + T(String(d1)) + ' 分貝的幾倍？',
             a: T('10^{' + ((d2 - d1) / 10) + '}=' + Math.pow(10, (d2 - d1) / 10)) + ' 倍',
             h: '兩式相減：$d_2-d_1=10\\log\\dfrac{I_2}{I_1}$，倍數 $=10^{(d_2-d_1)/10}$。',
             p: { type: 1, d1: d1, d2: d2, ans: Math.pow(10, (d2 - d1) / 10) } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['expLaw', '§1 指數律化簡'], ['radicalVal', '§1 根式與分數指數求值'], ['expOrder', '§1 同底指數比大小'], ['expEqSame', '§1 同底指數方程式'],
      ['expIneqSame', '§1 同底指數不等式'], ['expShift', '§1 指數函數的平移'], ['expQuadEq', '§1 換元二次的指數方程式'], ['growthTimes', '§1 每期成長 k 倍'],
      ['logDef', '§2 對數的定義求值'], ['logLaw', '§2 運算律化簡'], ['logExpress', '§2 用 log2、log3 表示'], ['changeBase', '§2 換底公式'],
      ['digits', '§2 位數'], ['charMant', '§2 首數與尾數的意義'], ['leadDigit', '§2 最高位數字'], ['logEqSimple', '§2 對數方程式（定義）'], ['logIneqSimple', '§2 對數不等式（定義域）'],
      ['logShift', '§3 對數函數的平移與對稱'], ['logOrder', '§3 對數值比大小'], ['logDomain', '§3 對數的定義域'], ['logQuadMin', '§3 換元二次的最小值'], ['logScale', '§3 對數刻度：地震與分貝']
    ],
    L2: [
      ['expSymmMin', '§1 對稱式換元的最值'], ['expIneqQuad', '§1 換元二次的指數不等式'], ['expAMGM', '§1 乘積定值的算幾'], ['expIntervalMax', '§1 指數在區間上的最值'],
      ['halfLife', '§1 半衰期'], ['compoundYears', '§1 成長率：至少幾年'],
      ['logQuadRange', '§2 對數換元的區間最值'], ['logEqQuad', '§2 對數換元的二次方程式'], ['logEqProduct', '§2 真數相乘的對數方程式'], ['logIneqBase', '§2 底數決定方向的對數不等式'],
      ['logSumTele', '§2 對數連加（望遠鏡）'], ['digitsLead', '§2 位數與最高位數字'], ['decimalFirst', '§2 小數點後第幾位非零'],
      ['logPointSym', '§3 對數函數上的點（多選）'], ['decayRatio', '§3 兩種半衰期的比'], ['dbMulti', '§3 分貝的疊加與倍數']
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

  return { makeRng: makeRng, L1: L1, L2: L2, META: META, _util: { gcd: gcd, F: F, Fr: Fr, lg: lg, lead: lead, LG: LG } };
}));
