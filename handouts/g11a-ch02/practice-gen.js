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
  function logT(b, arg) { return (b === 10 ? '\\log ' : '\\log_{' + baseTex(b) + '}') + (arg.length > 1 ? '{' + arg + '}' : arg); }   /* \log x：不補空白會黏成 \logx */
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
    var L = p.d * q.d / gcd(p.d, q.d); L = L * s.d / gcd(L, s.d);
    return { q: '設 ' + T('a\\gt0') + '，化簡 ' + T('a^{' + Fr.tex(p, true) + '}\\cdot a^{' + Fr.tex(q, true) + '}\\div a^{' + Fr.tex(s, true) + '}=a^{T}') + '，求 ' + T('T') + '。',
             a: T('T=' + Fr.tex(ans)),
             h: '同底相乘指數相加、相除指數相減：$T=\\left(' + Fr.tex(p, true) + '\\right)+\\left(' + Fr.tex(q, true) + '\\right)-\\left(' + Fr.tex(s, true) + '\\right)$，三個分數先通分成分母 $' + L + '$ 再加減。',
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
             h: '根號先改成分數指數，再把底數寫成同一個數的次方：$' + base + '=' + k + '^{' + n + '}$，原式 $=\\left(' + k + '^{' + n + '}\\right)^{\\frac{' + m + '}{' + n + '}}$，指數相乘時 $' + n + '$ 會消掉' + (m < 0 ? '；負指數記得取倒數。' : '。'),
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
    var esT = es.map(function (e) { return T(Fr.tex(e, true)); }).join('、');
    return { q: '設 ' + T('a=' + powT(a, Fr.tex(es[0], true))) + '、' + T('b=' + powT(a, Fr.tex(es[1], true))) + '、' + T('c=' + powT(a, Fr.tex(es[2], true))) + '，由大到小排列三數。',
             a: T(order),
             h: up ? '底數 $' + baseTex(a) + '\\gt1$ 是遞增：直接比三個指數 ' + esT + '（分數先通分或化成小數再比），指數愈大值愈大。'
                   : '底數 $' + baseTex(a) + '$ 介於 $0$ 與 $1$ 是遞減：三個指數 ' + esT + ' 愈大，值反而愈小。',
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
             h: up ? '底數 $' + baseTex(a) + '\\gt1$ 是遞增 ⟹ 直接比指數：$2x' + term(p, '', false) + '\\gt x' + term(q, '', false) + '$，把 $x$ 移到同一邊。'
                   : '底數 $' + baseTex(a) + '$ 介於 $0$ 與 $1$ 是遞減 ⟹ 比指數時<b>不等號要反向</b>：$2x' + term(p, '', false) + '\\lt x' + term(q, '', false) + '$。',
             p: { up: up ? 1 : 0, p: p, q: q, ans: [gt ? 1 : 0, bound] } };
  };

  /* 1-6 指數函數的平移 */
  L1.expShift = function (r) {
    var a = r.pick([2, 3, 5, F(1, 2)]), h = r.nz(-4, 4), k = r.nz(-5, 5);
    return { q: '將 ' + T('y=' + powT(a, 'x')) + ' 的圖形向' + (h > 0 ? '右' : '左') + '平移 ' + T(String(Math.abs(h))) + ' 單位、再向' + (k > 0 ? '上' : '下') + '平移 ' + T(String(Math.abs(k))) + ' 單位，求新圖形的方程式與漸近線。',
             a: T('y=' + powT(a, 'x' + term(-h, '', false)) + term(k, '', false)) + '，漸近線 ' + T('y=' + k),
             h: '向' + (h > 0 ? '右' : '左') + '移 ' + T(String(Math.abs(h))) + '：把指數的 $x$ 換成 $x' + term(-h, '', false) + '$；向' + (k > 0 ? '上' : '下') + '移 ' + T(String(Math.abs(k))) + '：整個式子' + (k > 0 ? '加 ' : '減 ') + T(String(Math.abs(k))) + '。原漸近線 $y=0$ 只跟著上下移，左右移不影響它。',
             p: { a: typeof a === 'number' ? [a, 1] : [a.n, a.d], h: h, k: k, ans: [h, k] } };
  };

  /* 1-7 換元二次的指數方程式 */
  L1.expQuadEq = function (r) {
    var a, u, v, tries = 0;
    do { a = r.pick([2, 3, 5]); u = r.int(0, 4); v = r.int(0, 4); }
    while ((u === v || Math.pow(a, u + v) > 20000) && tries++ < 60);
    if (u === v || Math.pow(a, u + v) > 20000) { a = 2; u = 0; v = 1; }
    var U = Math.pow(a, u), V = Math.pow(a, v), form = r.int(0, 1);
    var head = form === 0 ? (a * a) + '^{x}' : a + '^{2x}';
    var lhs = head + term(-(U + V), '\\cdot ' + a + '^{x}', false) + term(U * V, '', false);
    return { q: '解方程式 ' + T(lhs + '=0') + '。',
             a: T('x=' + Math.min(u, v) + '\\ \\text{或}\\ ' + Math.max(u, v)),
             h: '令 $t=' + a + '^{x}\\gt0$：' + (form === 0 ? '$' + (a * a) + '^{x}=\\left(' + a + '^{2}\\right)^{x}=t^{2}$' : '$' + a + '^{2x}=\\left(' + a + '^{x}\\right)^{2}=t^{2}$') + '，方程式變成 $t^{2}-' + (U + V) + 't+' + (U * V) + '=0$；因式分解解出兩個 $t$，再各自換回 $' + a + '^{x}$ 求 $x$。',
             p: { a: a, u: u, v: v, form: form, ans: [Math.min(u, v), Math.max(u, v)] } };
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
             h: '底數與真數都寫成 $' + root + '$ 的次方：底 $' + baseTex(base) + '=' + root + '^{' + (inv ? -pw : pw) + '}$、真數 $=' + root + '^{' + Fr.tex(F(m, n), true) + '}$，再用 $\\log_{k^{s}}k^{t}=\\dfrac{t}{s}$ 相除。',
             p: { base: typeof base === 'number' ? [base, 1] : [base.n, base.d], root: root, m: m, n: n, ans: [ans.n, ans.d] } };
  };

  /* 2-2 運算律化簡成整數 */
  L1.logLaw = function (r) {
    var b = r.pick([2, 3, 5, 6, 10]), n = r.int(1, 4), N = Math.pow(b, n);
    var divs = []; for (var u = 2; u < N; u++) if (N % u === 0) divs.push(u);
    if (!divs.length) { n = 2; N = b * b; divs = [b]; }
    var u = r.pick(divs), v = N / u, t = r.int(0, 2);
    var expr, hint;
    if (t === 0) { expr = logT(b, String(u)) + '+' + logT(b, String(v)); hint = '相加變相乘：$' + logT(b, String(u)) + '+' + logT(b, String(v)) + '=' + logT(b, String(u * v)) + '$，再想 $' + b + '$ 的幾次方等於 $' + N + '$。'; }
    else if (t === 1) { var w = r.pick([2, 3, 5, 7]); expr = logT(b, String(N * w)) + '-' + logT(b, String(w)); hint = '相減變相除：$' + logT(b, String(N * w)) + '-' + logT(b, String(w)) + '=' + logT(b, '\\dfrac{' + (N * w) + '}{' + w + '}') + '=' + logT(b, String(N)) + '$，再想 $' + b + '$ 的幾次方等於 $' + N + '$。'; }
    else { expr = '2' + logT(b, String(u)) + '+' + logT(b, String(v * v)); hint = '係數先搬進去當次方：$2' + logT(b, String(u)) + '=' + logT(b, String(u * u)) + '$；再相加變相乘，真數是 $' + (u * u) + '\\times' + (v * v) + '=\\left(' + u + '\\times' + v + '\\right)^2=' + N + '^2$，而 $' + N + '=' + b + '^{' + n + '}$。'; }
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
             h: '先質因數分解：$' + N + '=2^{' + i + '}\\cdot3^{' + j + '}\\cdot5^{' + k + '}$，再拆成 $' + i + 'a+' + j + 'b+' + k + '\\log5$，而 $\\log5=1-\\log2=1-a$' + (neg ? '；取倒數時整個式子再變號。' : '。'),
             p: { i: i, j: j, k: k, neg: neg ? 1 : 0, ans: [ca, cb, c0] } };
  };

  /* 2-4 換底公式：兩個對數相乘 */
  L1.changeBase = function (r) {
    var pq = r.pick([[2, 3], [2, 5], [3, 5], [2, 7], [3, 2], [5, 2]]), p = pq[0], q = pq[1];
    var i = r.int(1, 3), j = r.int(1, 3), k = r.int(1, 3), l = r.int(1, 3);
    var ans = F(j * l, i * k);   /* log_{p^i} q^j · log_{q^k} p^l = (j/i)(l/k) */
    return { q: '求 ' + T(logT(Math.pow(p, i), String(Math.pow(q, j))) + '\\cdot' + logT(Math.pow(q, k), String(Math.pow(p, l)))) + ' 的值。',
             a: T(Fr.tex(ans)),
             h: '全部換成常用對數：$' + logT(Math.pow(p, i), String(Math.pow(q, j))) + '=\\dfrac{' + j + '\\log ' + q + '}{' + i + '\\log ' + p + '}$、$' + logT(Math.pow(q, k), String(Math.pow(p, l))) + '=\\dfrac{' + l + '\\log ' + p + '}{' + k + '\\log ' + q + '}$，相乘後 $\\log ' + p + '$ 與 $\\log ' + q + '$ 都約掉，只剩係數。',
             p: { p: p, q: q, i: i, j: j, k: k, l: l, ans: [ans.n, ans.d] } };
  };

  /* 2-5 位數 */
  L1.digits = function (r) {
    function lgT(x) { var s = [], c, PR = [2, 3, 5, 7], i, pr; for (i = 0; i < 4; i++) { pr = PR[i]; c = 0; while (x % pr === 0) { x /= pr; c++; } if (c) s.push((c === 1 ? '' : c) + '\\log ' + pr); } return s.join('+'); }
    var a = r.pick([2, 3, 6, 7, 12, 15, 18, 24, 35, 42]), n = r.int(10, 60);
    var v = round4(n * lg(a)), d = Math.floor(v + 1e-9) + 1;
    var dc = lgT(a), dec = (dc === '\\log ' + a) ? '' : '=' + dc;
    return { q: '已知 ' + T('\\log2\\approx0.3010') + '、' + T('\\log3\\approx0.4771') + '、' + T('\\log7\\approx0.8451') + '。問 ' + T(a + '^{' + n + '}') + ' 是幾位數？',
             a: T(String(d)) + ' 位（' + T('\\log ' + a + '^{' + n + '}\\approx' + v.toFixed(4)) + '）',
             h: '先湊出 $\\log ' + a + dec + '\\approx' + lg(a).toFixed(4) + '$' + (a % 5 === 0 ? '（$\\log5=1-\\log2=0.6990$）' : '') + '，再把次方拉下來：$\\log ' + a + '^{' + n + '}=' + n + '\\times' + lg(a).toFixed(4) + '$；位數 $=$ 首數（整數部分）$+1$。',
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
    function lgT(x) { var s = [], c, PR = [2, 3, 5, 7], i, pr; for (i = 0; i < 4; i++) { pr = PR[i]; c = 0; while (x % pr === 0) { x /= pr; c++; } if (c) s.push((c === 1 ? '' : c) + '\\log ' + pr); } return s.join('+'); }
    var a = r.pick([2, 3, 6, 7, 12, 15]), n, v, mant, tries = 0, tab = [LG[2], LG[3], LG[4], LG[5], LG[6], LG[7], LG[8], LG[9]];
    do { n = r.int(8, 40); v = round4(n * lg(a)); mant = round4(v - Math.floor(v)); }
    while (tries++ < 40 && tab.some(function (t) { return Math.abs(mant - t) < 0.006; }));
    var d = lead(mant);
    var dc = lgT(a), dec = (dc === '\\log ' + a) ? '' : '=' + dc;
    return { q: '已知 ' + T('\\log2\\approx0.3010') + '、' + T('\\log3\\approx0.4771') + '、' + T('\\log7\\approx0.8451') + '。求 ' + T(a + '^{' + n + '}') + ' 的最高位數字。',
             a: T(String(d)) + '（尾數 ' + T(mant.toFixed(4)) + ' 介於 ' + T('\\log' + d) + ' 與 ' + T('\\log' + (d + 1)) + ' 之間）',
             h: '$\\log ' + a + dec + '\\approx' + lg(a).toFixed(4) + '$' + (a % 5 === 0 ? '（$\\log5=1-\\log2=0.6990$）' : '') + ' ⟹ $\\log ' + a + '^{' + n + '}=' + n + '\\times' + lg(a).toFixed(4) + '=' + v.toFixed(4) + '$，尾數是 $' + mant.toFixed(4) + '$；尾數落在 $\\log k$ 與 $\\log(k+1)$ 之間時最高位就是 $k$（$\\log2=0.3010$、$\\log3=0.4771$、$\\log5=0.6990$、$\\log7=0.8451$）。',
             p: { a: a, n: n, ans: d } };
  };

  /* 2-8 簡單對數方程式 */
  L1.logEqSimple = function (r) {
    var a = r.pick([2, 3, 5, 10]), c = r.int(1, 3), p = r.int(-5, 5);
    var x = Math.pow(a, c) - p;
    return { q: '解方程式 ' + T(logT(a, '(x' + term(p, '', false) + ')') + '=' + c) + '。',
             a: T('x=' + x),
             h: '由定義 $\\log_a M=c\\iff M=a^{c}$：這裡 $a=' + a + '$、$c=' + c + '$，所以真數 $x' + term(p, '', false) + '=' + a + '^{' + c + '}=' + Math.pow(a, c) + '$，移項就得到 $x$；解完代回檢查真數 $\\gt0$。',
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
               h: '向' + (h > 0 ? '右' : '左') + '移 ' + T(String(Math.abs(h))) + '：把真數的 $x$ 換成 $x' + term(-h, '', false) + '$；向' + (k > 0 ? '上' : '下') + '移 ' + T(String(Math.abs(k))) + '：整個式子' + (k > 0 ? '加 ' : '減 ') + T(String(Math.abs(k))) + '。原漸近線 $x=0$ 只跟著左右移。',
               p: { a: a, t: 0, h: h, k: k, ans: [h, k] } };
    }
    var names = ['$x$ 軸', '$y$ 軸', '直線 $y=x$'];
    var anss = ['y=-' + logT(a, 'x') + '=' + logT(F(1, a), 'x'), 'y=' + logT(a, '(-x)'), 'y=' + a + '^{x}'][t - 1];
    var hints = ['對 $x$ 軸對稱：$y$ 換成 $-y$，由 $-y=' + logT(a, 'x') + '$ 得 $y=-' + logT(a, 'x') + '$；再用 $-\\log_{' + a + '}x=\\log_{\\frac{1}{' + a + '}}x$ 把負號收進底數。',
                 '對 $y$ 軸對稱：$x$ 換成 $-x$，直接把 $y=' + logT(a, 'x') + '$ 裡的真數改成 $-x$（定義域也跟著變成 $x\\lt0$）。',
                 '對直線 $y=x$ 對稱就是求反函數：把 $y=' + logT(a, 'x') + '$ 的 $x,y$ 對調成 $x=' + logT(a, 'y') + '$，再用對數定義改寫成 $y$ 等於 $' + a + '$ 的次方。'][t - 1];
    return { q: '求 ' + T('y=' + logT(a, 'x')) + ' 的圖形對 ' + names[t - 1] + ' 對稱後的圖形方程式。',
             a: T(anss),
             h: hints,
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
    var band = names.map(function (nm, i) {
      var v = pick[i][1];
      if (Math.abs(v - Math.round(v)) < 1e-9) return '$' + nm + '=' + Math.round(v) + '$';
      var lo = Math.floor(v);
      return '$' + nm + '$ 介於 $' + lo + '$ 與 $' + (lo + 1) + '$ 之間';
    }).join('、');
    return { q: '設 ' + T('a=' + pick[0][0]) + '、' + T('b=' + pick[1][0]) + '、' + T('c=' + pick[2][0]) + '，由大到小排列三數。',
             a: T(idx.map(function (i) { return names[i]; }).join('\\gt ')),
             h: '先判斷正負（底與真數同在 $1$ 的同側為正），再和整數比：' + band + '；同一段裡的再用換底或估值細比。',
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
    return { q: '求 ' + T('\\log_{(x' + term(-p, '', false) + ')}' + (q === 0 ? 'x' : '(x' + term(-q, '', false) + ')')) + ' 有意義的 ' + T('x') + ' 範圍。',
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
    var ty = r.int(0, 2);
    if (ty === 0) {                       /* 地震：能量倍數 = 10^{1.5Δ M} */
      var d = r.int(1, 4), m1 = r.int(3, 8 - d), e = 1.5 * d;
      var mulV = Math.pow(10, e), kk = Math.floor(e), whole = (e === Math.floor(e));
      var mulT = whole ? '10^{' + e + '}=' + Math.round(mulV)
                       : '10^{' + e + '}\\approx' + (kk <= 1 ? String(Math.round(mulV * 10) / 10) : '3.16\\times10^{' + kk + '}');
      return { q: '地震規模 ' + T('M') + ' 與能量 ' + T('E') + ' 的關係為 ' + T('\\log E=4.8+1.5M') + '。規模 ' + T(String(m1 + d)) + ' 的地震釋放的能量是規模 ' + T(String(m1)) + ' 的幾倍？',
               a: T(mulT) + ' 倍',
               h: '兩式相減：$\\log E_1-\\log E_2=1.5\\left(' + (m1 + d) + '-' + m1 + '\\right)=1.5\\times' + d + '=' + e + '$，所以倍數 $=10^{' + e + '}$' + (whole ? '，直接算出來。' : '；$10^{0.5}=\\sqrt{10}\\approx3.16$，用它把半次方拆開。'),
               p: { type: 0, d: d, e: e, m1: m1, ans: mulV } };
    }
    if (ty === 1) {                       /* 分貝：強度變 n 倍 */
      var n = r.pick([10, 100, 1000, 10000]), d0 = r.pick([30, 40, 45, 50, 55, 60, 65, 70, 75, 80]);
      var kn = Math.round(Math.log10(n));
      return { q: '分貝 ' + T('d=10\\log\\dfrac{I}{I_0}') + '。一台機器的噪音是 ' + T(String(d0)) + ' 分貝，' + T(String(n)) + ' 台同型機器同時運轉（強度相加）約為幾分貝？',
               a: T(String(d0 + 10 * kn)) + ' 分貝',
               h: '強度變 $' + n + '$ 倍 ⟹ 分貝要加 $10\\log ' + n + '$；而 $' + n + '=10^{' + kn + '}$，所以加 $10\\times' + kn + '$ 分貝，原來的 $' + d0 + '$ 分貝再加上去。',
               p: { type: 1, n: n, d0: d0, ans: d0 + 10 * kn } };
    }
    /* 酸鹼值：pH 差 dd ⟹ 濃度差 10^{dd} 倍 */
    var p1 = r.int(1, 6), dd = r.int(1, 4);
    return { q: '溶液的酸鹼值定義為 ' + T('\\text{pH}=-\\log\\left[\\text{H}^{+}\\right]') + '（' + T('\\left[\\text{H}^{+}\\right]') + ' 是氫離子濃度）。甲溶液的 pH 值為 ' + T(String(p1)) + '、乙溶液的 pH 值為 ' + T(String(p1 + dd)) + '，甲的氫離子濃度是乙的幾倍？',
             a: T('10^{' + dd + '}=' + Math.pow(10, dd)) + ' 倍',
             h: '由定義 $\\left[\\text{H}^{+}\\right]=10^{-\\text{pH}}$：甲是 $10^{-' + p1 + '}$、乙是 $10^{-' + (p1 + dd) + '}$，相除時指數相減，差 $' + (p1 + dd) + '-' + p1 + '=' + dd + '$。',
             p: { type: 2, p1: p1, dd: dd, ans: dd } };
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
    var lhs = (c2 === 1 ? '' : c2 + '\\cdot ') + (a * a) + '^{x}' + term(c1, '\\cdot ' + a + '^{x}', false) + term(c0, '', false);
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
    var tab = { 2: 0.0086, 3: 0.0128, 4: 0.0170, 5: 0.0212, 6: 0.0253, 7: 0.0294, 8: 0.0334, 10: 0.0414, 20: 0.0792 };
    var rate, k, lg1, lgk, ratio, n, nExact, tries = 0;
    do {   /* 表值算出的年數必須等於精確值（(1+r)^n>k 的最小 n），否則換一組 */
      rate = r.pick([2, 3, 4, 5, 6, 7, 8, 10, 20]); k = r.pick([2, 3, 5, 10]);
      lg1 = tab[rate]; lgk = { 2: 0.3010, 3: 0.4771, 5: 0.6990, 10: 1 }[k]; ratio = lgk / lg1;
      n = Math.floor(ratio) + 1;
      nExact = 1; while (Math.pow(1 + rate / 100, nExact) <= k + 1e-12) nExact++;
    } while ((Math.abs(ratio - Math.round(ratio)) < 0.12 || n !== nExact) && tries++ < 80);
    var ctx = r.int(0, 2), P0 = r.pick([10, 20, 50, 100]);
    var rateT = rate < 10 ? '1.0' + rate : '1.' + rate;
    var given = '（' + T('\\log' + rateT + '\\approx' + lg1.toFixed(4)) + (k === 10 ? '' : '、' + T('\\log' + k + '\\approx' + lgk.toFixed(4))) + '）';
    var core = '$' + rateT + '^{n}\\gt' + k + '$ 兩邊取 $\\log$：$n\\times' + lg1.toFixed(4) + '\\gt' + lgk.toFixed(4) + '$ ⟹ $n\\gt\\dfrac{' + lgk.toFixed(4) + '}{' + lg1.toFixed(4) + '}\\approx' + ratio.toFixed(2) + '$，再取比它大的最小整數。';
    if (ctx === 1) {
      return { q: '小美存入 ' + T(String(P0)) + ' 萬元，年利率 ' + T(rate + '\\%') + '、每年複利一次。至少要幾年，本利和才會超過 ' + T(String(P0 * k)) + ' 萬元？' + given,
               a: T(String(n)) + ' 年',
               h: '先兩邊同除以 $' + P0 + '$，變成「本利和超過本金的 $' + k + '$ 倍」：' + core,
               p: { rate: rate, k: k, lg1: lg1, lgk: lgk, ctx: 1, P0: P0, ans: n } };
    }
    if (ctx === 2) {
      return { q: '培養皿中的細菌數每小時增加 ' + T(rate + '\\%') + '。至少要經過幾小時，細菌數才會超過原來的 ' + T(String(k)) + ' 倍？' + given,
               a: T(String(n)) + ' 小時',
               h: '每小時變成 $' + rateT + '$ 倍：' + core,
               p: { rate: rate, k: k, lg1: lg1, lgk: lgk, ctx: 2, P0: null, ans: n } };
    }
    return { q: '某城市人口每年成長 ' + T(rate + '\\%') + '。至少要經過幾年，人口才會超過現在的 ' + T(String(k)) + ' 倍？' + given,
             a: T(String(n)) + ' 年',
             h: '每年變成 $' + rateT + '$ 倍：' + core,
             p: { rate: rate, k: k, lg1: lg1, lgk: lgk, ctx: 0, P0: null, ans: n } };
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
    var a, c, N, pairs, tries = 0;
    do {
      a = r.pick([2, 3, 5, 6, 10]); c = r.pick([1, 2, 2, 3]); N = Math.pow(a, c); pairs = [];
      if (N <= 1000) for (var m = 1; m * m < N; m++) if (N % m === 0 && (N / m - m) <= 60) pairs.push([m, N / m]);
    } while (!pairs.length && tries++ < 60);
    if (!pairs.length) { a = 2; c = 3; N = 8; pairs = [[2, 4]]; }
    var pr = r.pick(pairs), lo = pr[0], hi = pr[1], K = hi - lo, neg = r() < 0.5;
    /* neg=false：x(x-K)=N，合格根 hi、另一根 -lo；neg=true：x(x+K)=N，合格根 lo、另一根 -hi */
    var k = neg ? -K : K, m0 = neg ? lo : hi, other = neg ? -hi : -lo;
    var inner = 'x' + term(-k, '', false);
    return { q: '解方程式 ' + T(logT(a, 'x') + '+' + logT(a, '(' + inner + ')') + '=' + c) + '。',
             a: T('x=' + m0) + '（另一根 ' + T('x=' + other) + ' 使真數為負，不合）',
             h: '相加變相乘：$' + logT(a, 'x(' + inner + ')') + '=' + c + '$ ⟹ $x\\left(' + inner + '\\right)=' + a + '^{' + c + '}=' + N + '$；展開成二次方程式解出兩根後，<b>一定要代回檢查兩個真數都 $\\gt0$</b>。',
             p: { a: a, c: c, k: k, ans: m0 } };
  };

  /* 2-4 底數大於或小於 1 的對數不等式 */
  L2.logIneqBase = function (r) {
    var up = r() < 0.5, a = up ? r.pick([2, 3, 10]) : r.pick([F(1, 2), F(1, 3), F(1, 5)]);
    var p = r.int(-3, 3), q = p + r.pick([2, 4, 6]), mid = (p + q) / 2;
    /* log_a(x-p) > log_a(q-x)，定義域 p<x<q */
    var ansL = up ? mid : p, ansR = up ? q : mid;
    return { q: '解不等式 ' + T(logT(a, '(x' + term(-p, '', false) + ')') + '\\gt' + logT(a, '(' + (q === 0 ? '' : q) + '-x)')) + '。',
             a: T(ansL + '\\lt x\\lt' + ansR),
             h: '定義域 $' + p + '\\lt x\\lt' + q + '$；' + (up ? '底數大於 $1$ ⟹ 真數保持方向：$x' + term(-p, '', false) + '\\gt' + (q === 0 ? '' : q) + '-x$。' : '底數小於 $1$ ⟹ 真數方向<b>反過來</b>：$x' + term(-p, '', false) + '\\lt' + (q === 0 ? '' : q) + '-x$。'),
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
    function lgT(x) { var s = [], c, PR = [2, 3, 5, 7], i, pr; for (i = 0; i < 4; i++) { pr = PR[i]; c = 0; while (x % pr === 0) { x /= pr; c++; } if (c) s.push((c === 1 ? '' : c) + '\\log ' + pr); } return s.join('+'); }
    var a = r.pick([2, 3, 6, 7, 12, 15, 18, 21]), n, v, mant, tries = 0, tab = [LG[2], LG[3], LG[4], LG[5], LG[6], LG[7], LG[8], LG[9]];
    do { n = r.int(10, 50); v = round4(n * lg(a)); mant = round4(v - Math.floor(v)); }
    while (tries++ < 40 && tab.some(function (t) { return Math.abs(mant - t) < 0.006; }));
    var d = Math.floor(v) + 1, ld = lead(mant);
    var dc = lgT(a), dec = (dc === '\\log ' + a) ? '' : '=' + dc;
    return { q: '已知 ' + T('\\log2\\approx0.3010') + '、' + T('\\log3\\approx0.4771') + '、' + T('\\log7\\approx0.8451') + '。求 ' + T(a + '^{' + n + '}') + ' 的位數與最高位數字。',
             a: T(String(d)) + ' 位數，最高位數字 ' + T(String(ld)) + '（' + T('\\log ' + a + '^{' + n + '}\\approx' + v.toFixed(4)) + '）',
             h: '$\\log ' + a + dec + '\\approx' + lg(a).toFixed(4) + '$' + (a % 5 === 0 ? '（$\\log5=1-\\log2=0.6990$）' : '') + ' ⟹ $\\log ' + a + '^{' + n + '}=' + n + '\\times' + lg(a).toFixed(4) + '=' + v.toFixed(4) + '$：首數 $' + Math.floor(v) + '$ 決定位數（$+1$），尾數 $' + mant.toFixed(4) + '$ 落在 $\\log k$ 與 $\\log(k+1)$ 之間決定最高位。',
             p: { a: a, n: n, ans: [d, ld] } };
  };

  /* 2-7 小數點後第幾位開始不為 0、該數字為何 */
  L2.decimalFirst = function (r) {
    function lgT(x) { var s = [], c, PR = [2, 3, 5, 7], i, pr; for (i = 0; i < 4; i++) { pr = PR[i]; c = 0; while (x % pr === 0) { x /= pr; c++; } if (c) s.push((c === 1 ? '' : c) + '\\log ' + pr); } return s.join('+'); }
    var base = r.pick([2, 3, 5, 6, 7, 8, 9, 12]), n, v, pos, mant, tries = 0, tab = [LG[2], LG[3], LG[4], LG[5], LG[6], LG[7], LG[8], LG[9]];
    do { n = r.int(8, 40); v = -round4(n * lg(base)); pos = -Math.floor(v); mant = round4(v - Math.floor(v)); }
    while (tries++ < 40 && (mant < 0.006 || tab.some(function (t) { return Math.abs(mant - t) < 0.006; })));
    var dg = lead(mant);
    var dc = lgT(base), dec = (dc === '\\log ' + base) ? '' : '=' + dc;
    return { q: '已知 ' + T('\\log2\\approx0.3010') + '、' + T('\\log3\\approx0.4771') + '、' + T('\\log7\\approx0.8451') + '。將 ' + T('\\left(\\dfrac{1}{' + base + '}\\right)^{' + n + '}') + ' 化為小數：(1) 從小數點後第幾位開始出現不為 ' + T('0') + ' 的數字？(2) 該數字為何？',
             a: '(1) 第 ' + T(String(pos)) + ' 位　(2) ' + T(String(dg)) + '（' + T('\\log=' + (-n * lg(base)).toFixed(4) + '=-' + pos + '+' + mant.toFixed(4)) + '）',
             h: '$\\log ' + base + dec + '\\approx' + lg(base).toFixed(4) + '$' + (base % 5 === 0 ? '（$\\log5=1-\\log2=0.6990$）' : '') + ' ⟹ $\\log\\left(\\dfrac{1}{' + base + '}\\right)^{' + n + '}=-' + n + '\\times' + lg(base).toFixed(4) + '=' + (-v).toFixed(4) + '$；把它寫成「負整數 $+$ 正小數」（例：$-2.3=-3+0.7$），負整數的絕對值是位置，正小數是尾數、決定數字。',
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
             h: '甲經過 $' + t + '\\div' + TA + '=' + (t / TA) + '$ 個半衰期、乙經過 $' + t + '\\div' + TB + '=' + (t / TB) + '$ 個半衰期，各自剩 $\\left(\\dfrac12\\right)^{' + (t / TA) + '}$ 與 $\\left(\\dfrac12\\right)^{' + (t / TB) + '}$；相除時指數相減，半衰期短的剩得少。',
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
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p 重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     ══════════════════════════════════════════════════════════ */
  function parT(n) { return n < 0 ? '(' + n + ')' : String(n); }                 /* 負數代入時加括號 */
  function frT(num, den, first) {                                               /* 帶正負號的分數項 */
    return (num < 0 ? '-' : (first ? '' : '+')) + '\\dfrac{' + Math.abs(num) + '}{' + den + '}';
  }
  var L1_H1 = {
    expLaw: '這是「指數律化簡」：同底相乘指數相加、同底相除指數相減，先把三個指數寫成一個加減式，再通分算出來。',
    radicalVal: '這是「根式與分數指數求值」：先把根號改寫成分數指數，再把底數寫成同一個數的次方，讓指數相乘時約掉。',
    expOrder: '這是「同底指數比大小」：先看底數比 $1$ 大還是小（決定遞增或遞減），再單純比三個指數。',
    expEqSame: '這是「同底指數方程式」：先把兩邊的底數統一成同一個數，同底之後讓兩邊的指數相等。',
    expIneqSame: '這是「同底指數不等式」：先判斷底數比 $1$ 大或小——大於 $1$ 比指數時不等號不變，小於 $1$ 要反向。',
    expShift: '這是「指數函數的平移」：左右移改指數裡的 $x$、上下移是整個式子加減；漸近線只跟著上下移。',
    expQuadEq: '這是「換元二次的指數方程式」：令 $t$ 等於那個指數式（記得 $t\\gt0$），把方程式變成 $t$ 的二次式再因式分解。',
    growthTimes: '這是「每期成長固定倍數」：先算經過了幾個完整的週期，倍數就是「每期倍數」自乘那麼多次。',
    logDef: '這是「用定義求對數值」：把底數與真數都改寫成同一個數的次方，再把兩個次方相除。',
    logLaw: '這是「對數運算律化簡」：相加變相乘、相減變相除、係數搬上去當次方，合併成一個對數之後再求值。',
    logExpress: '這是「用 $\\log2$、$\\log3$ 表示」：先把真數質因數分解，再把 $\\log5$ 換成 $1-\\log2$。',
    changeBase: '這是「換底公式」：把每個對數都換成常用對數的分式，相乘之後上下的 $\\log$ 會互相對消。',
    digits: '這是「求位數」：先取 $\\log$ 把次方拉下來變成乘法，再看它的整數部分（首數）。',
    charMant: '這是「首數與尾數的意義」：首數決定這個數夾在 $10$ 的哪兩個次方之間，也就決定了位數或小數點後第幾位。',
    leadDigit: '這是「求最高位數字」：先取 $\\log$ 算出值，再取它的小數部分（尾數），看尾數落在哪兩個 $\\log$ 之間。',
    logEqSimple: '這是「對數方程式（定義型）」：用 $\\log_a M=c\\iff M=a^{c}$ 把對數拆掉，解完一定要檢查真數。',
    logIneqSimple: '這是「對數不等式（定義域）」：先寫下真數 $\\gt0$ 的定義域，再依底數大小決定不等號方向，最後取交集。',
    logShift: '這是「對數函數的平移與對稱」：平移看真數裡的 $x$ 與整體的加減；對稱是把 $x$ 或 $y$ 換成相反數，對直線 $y=x$ 對稱則是取反函數。',
    logOrder: '這是「對數值比大小」：先判斷每個數的正負，再把它們各自夾在相鄰的兩個整數之間比較。',
    logDomain: '這是「對數的定義域」：把「真數 $\\gt0$」列出來（底數是變數時再加上「底 $\\gt0$ 且 $\\ne1$」），最後取交集。',
    logQuadMin: '這是「對數換元的二次最值」：令 $t$ 等於那個對數，化成 $t$ 的二次函數之後配方求頂點。',
    logScale: '這是「對數刻度」：把兩個情況各寫一次公式再相減，常數會消掉，差值就是 $10$ 的次方倍數。'
  };
  var L1_SOL = {};

  L1_SOL.expLaw = function (p) {
    var P = F(p.p[0], p.p[1]), Q = F(p.q[0], p.q[1]), S = F(p.s[0], p.s[1]), A = F(p.ans[0], p.ans[1]);
    var L = P.d * Q.d / gcd(P.d, Q.d); L = L * S.d / gcd(L, S.d);
    var nP = P.n * (L / P.d), nQ = Q.n * (L / Q.d), nS = S.n * (L / S.d), tot = nP + nQ - nS;
    return ['指數律：同底相乘指數相加、同底相除指數相減，所以 $T=\\left(' + Fr.tex(P, true) + '\\right)+\\left(' + Fr.tex(Q, true) + '\\right)-\\left(' + Fr.tex(S, true) + '\\right)$。',
      '三個分數通分成分母 $' + L + '$：$T=' + frT(nP, L, true) + frT(nQ, L, false) + frT(-nS, L, false) + '$。',
      '分子直接加減：$' + nP + (nQ < 0 ? '-' + (-nQ) : '+' + nQ) + (nS < 0 ? '+' + (-nS) : '-' + nS) + '=' + tot + '$，所以 $T=\\dfrac{' + tot + '}{' + L + '}' + (tot === A.n && L === A.d ? '' : '=' + Fr.tex(A)) + '$。'];
  };

  L1_SOL.radicalVal = function (p) {
    var k = Math.round(Math.pow(p.base, 1 / p.n)), A = F(p.ans[0], p.ans[1]);
    var st = ['先統一寫成分數指數（$\\sqrt[n]{a^{m}}=a^{\\frac{m}{n}}$，分母就是根指數）：原式 $=' + p.base + '^{\\frac{' + p.m + '}{' + p.n + '}}$。',
      '底數寫成同一個數的次方：$' + p.base + '=' + k + '^{' + p.n + '}$，所以原式 $=\\left(' + k + '^{' + p.n + '}\\right)^{\\frac{' + p.m + '}{' + p.n + '}}=' + k + '^{' + p.n + '\\times\\frac{' + p.m + '}{' + p.n + '}}=' + k + '^{' + p.m + '}$（$' + p.n + '$ 約掉了）。'];
    if (p.m < 0) st.push('負指數取倒數：$' + k + '^{' + p.m + '}=\\dfrac{1}{' + k + '^{' + (-p.m) + '}}=' + Fr.tex(A) + '$。');
    else st.push('直接算出來：$' + k + '^{' + p.m + '}=' + Fr.tex(A) + '$。');
    return st;
  };

  L1_SOL.expOrder = function (p) {
    var up = p.base[1] === 1, a = up ? p.base[0] : F(p.base[0], p.base[1]);
    var es = p.es.map(function (e) { return F(e[0], e[1]); }), nm = ['a', 'b', 'c'], idx = p.ans;
    var L = 1; es.forEach(function (e) { L = L * e.d / gcd(L, e.d); });
    var chain = idx.map(function (i) { return Fr.tex(es[i], true); }).join(up ? '\\gt ' : '\\lt ');
    return [(up ? '底數 $' + baseTex(a) + '\\gt1$，指數函數是<b>遞增</b>的：指數愈大，值就愈大。'
                : '底數 $' + baseTex(a) + '$ 介於 $0$ 與 $1$，指數函數是<b>遞減</b>的：指數愈大，值反而愈小。'),
      '三個指數通分成分母 $' + L + '$：' + es.map(function (e, i) { return '$' + nm[i] + '$ 的指數 $' + Fr.tex(e, true) + '=\\dfrac{' + (e.n * (L / e.d)) + '}{' + L + '}$'; }).join('、') + '，只要比分子就好。',
      (up ? '把指數由大到小排：$' + chain + '$，值也照這個順序。' : '要找值最大的，就找指數最小的：把指數由小到大排 $' + chain + '$。')
        + '所以 $' + idx.map(function (i) { return nm[i]; }).join('\\gt ') + '$。'];
  };

  L1_SOL.expEqSame = function (p) {
    var A = F(p.ans[0], p.ans[1]), R = Math.pow(p.a, p.k), rhs = term(p.m, 'x', true) + term(p.q, '', false);
    var km = p.k * p.m, kq = p.k * p.q, D = 1 - km, Nn = kq - p.p;
    var flip = D < 0; if (flip) { D = -D; Nn = -Nn; }
    return ['右邊的底數 $' + R + '=' + p.a + '^{' + p.k + '}$，先統一底數：$' + R + '^{' + rhs + '}=\\left(' + p.a + '^{' + p.k + '}\\right)^{' + rhs + '}=' + p.a + '^{' + p.k + '\\left(' + rhs + '\\right)}$。',
      '同底數的指數相等：$x' + term(p.p, '', false) + '=' + p.k + '\\left(' + rhs + '\\right)=' + (term(km, 'x', true) + term(kq, '', false)) + '$。',
      '把 $x$ 移到同一邊：$\\left(1' + term(-km, '', false) + '\\right)x=' + kq + '-' + parT(p.p) + '=' + (kq - p.p) + '$'
        + (flip ? '，分子分母同乘 $-1$ 後' : '') + '，得 $x=\\dfrac{' + Nn + '}{' + D + '}' + (Nn === A.n && D === A.d ? '' : '=' + Fr.tex(A)) + '$。'];
  };

  L1_SOL.expIneqSame = function (p) {
    var up = p.up === 1, bound = p.ans[1], op = up ? '\\gt ' : '\\lt ';
    return [(up ? '底數大於 $1$，指數函數<b>遞增</b>：比較兩邊的指數時，不等號方向<b>不變</b>。'
                : '底數介於 $0$ 與 $1$，指數函數<b>遞減</b>：比較兩邊的指數時，不等號方向<b>要反過來</b>。'),
      '去掉底數只留指數：$2x' + term(p.p, '', false) + op + 'x' + term(p.q, '', false) + '$。',
      '移項整理：$2x-x' + op + '\\left(' + p.q + '\\right)-\\left(' + p.p + '\\right)$，所以 $x' + op + bound + '$。'];
  };

  L1_SOL.expShift = function (p) {
    var a = p.a[1] === 1 ? p.a[0] : F(p.a[0], p.a[1]), sh = 'x' + term(-p.h, '', false);
    return ['左右平移：向' + (p.h > 0 ? '右' : '左') + '移 $' + Math.abs(p.h) + '$ 單位，就是把指數裡的 $x$ 換成 $' + sh + '$，得 $y=' + powT(a, sh) + '$。',
      '上下平移：向' + (p.k > 0 ? '上' : '下') + '移 $' + Math.abs(p.k) + '$ 單位，就是整個式子' + (p.k > 0 ? '加' : '減') + ' $' + Math.abs(p.k) + '$：$y=' + powT(a, sh) + term(p.k, '', false) + '$。',
      '漸近線：原來 $y=' + powT(a, 'x') + '$ 的漸近線是 $y=0$；左右移不影響它，上下移 $' + parT(p.k) + '$ 之後變成 $y=' + p.k + '$。'];
  };

  L1_SOL.expQuadEq = function (p) {
    var a = p.a, U = Math.pow(a, p.u), V = Math.pow(a, p.v), lo = p.ans[0], hi = p.ans[1];
    return ['令 $t=' + a + '^{x}$，注意 $t\\gt0$。' + (p.form === 0
        ? '首項 $' + (a * a) + '^{x}=\\left(' + a + '^{2}\\right)^{x}=\\left(' + a + '^{x}\\right)^{2}=t^{2}$。'
        : '首項 $' + a + '^{2x}=\\left(' + a + '^{x}\\right)^{2}=t^{2}$。'),
      '方程式變成 $t^{2}-' + (U + V) + 't+' + (U * V) + '=0$；因式分解 $\\left(t-' + U + '\\right)\\left(t-' + V + '\\right)=0$，得 $t=' + U + '$ 或 $t=' + V + '$（兩個都 $\\gt0$，都要留）。',
      '換回 $' + a + '^{x}$：$' + a + '^{x}=' + Math.pow(a, lo) + '=' + a + '^{' + lo + '}$ ⟹ $x=' + lo + '$；$' + a + '^{x}=' + Math.pow(a, hi) + '=' + a + '^{' + hi + '}$ ⟹ $x=' + hi + '$。'];
  };

  L1_SOL.growthTimes = function (p, it) {
    var unit = String(it.a).replace(/^\$[^$]*\$\s*/, '');
    if (p.type === 0) return ['先算經過幾個週期：總時間 $' + (p.n * p.T) + '$ 除以一個週期 $' + p.T + '$，$' + (p.n * p.T) + '\\div' + p.T + '=' + p.n + '$ 個週期。',
      '每過一個週期就乘一次 $' + p.k + '$，' + p.n + ' 個週期就是連乘 ' + p.n + ' 次：$' + p.k + '^{' + p.n + '}$。',
      '算出來 $' + p.k + '^{' + p.n + '}=' + Math.pow(p.k, p.n) + '$，所以是原來的 $' + Math.pow(p.k, p.n) + '$ 倍。'];
    return ['先看倍數是幾個週期：$' + Math.pow(p.k, p.n) + '=' + p.k + '^{' + p.n + '}$，所以恰好經過 $' + p.n + '$ 個週期。',
      '一個週期是 $' + p.T + '$ ' + unit + '，$' + p.n + '$ 個週期就是 $' + p.n + '\\times' + p.T + '=' + (p.n * p.T) + '$ ' + unit + '。',
      '所以需要 $' + (p.n * p.T) + '$ ' + unit + '。'];
  };

  L1_SOL.logDef = function (p) {
    var inv = p.base[0] === 1 && p.base[1] > 1, bk = inv ? p.base[1] : p.base[0], base = inv ? F(1, bk) : bk;
    var pw = Math.round(Math.log(bk) / Math.log(p.root)), s = inv ? -pw : pw;
    var tE = F(p.m, p.n), A = F(p.ans[0], p.ans[1]);
    return ['底數與真數都改寫成 $' + p.root + '$ 的次方。底數：$' + baseTex(base) + '=' + p.root + '^{' + s + '}$'
        + (inv ? '（倒數就是指數變號）' : '') + '。',
      '真數：它是 $' + p.root + '$ 的 $' + Fr.tex(tE, true) + '$ 次方'
        + (p.n === 1 ? '' : '（$' + p.n + '$ 次根號就是 $\\dfrac{1}{' + p.n + '}$ 次方）') + (p.m < 0 ? '（倒數再變號）' : '') + '。',
      '套 $\\log_{k^{s}}k^{t}=\\dfrac{t}{s}$：$' + Fr.tex(tE, true) + '\\div\\left(' + s + '\\right)=' + Fr.tex(A) + '$。'];
  };

  L1_SOL.logLaw = function (p) {
    var N = Math.pow(p.b, p.n), b = p.b;
    if (p.t === 0) return ['對數運算律：相加變相乘，$\\log_{' + b + '}u+\\log_{' + b + '}v=\\log_{' + b + '}\\left(uv\\right)$。',
      '代進去：$' + logT(b, String(p.u)) + '+' + logT(b, String(p.v)) + '=' + logT(b, p.u + '\\times' + p.v) + '=' + logT(b, String(N)) + '$。',
      '再問「$' + b + '$ 的幾次方是 $' + N + '$」：$' + N + '=' + b + '^{' + p.n + '}$，所以答案是 $' + p.n + '$。'];
    if (p.t === 1) return ['對數運算律：相減變相除，$\\log_{' + b + '}M-\\log_{' + b + '}w=\\log_{' + b + '}\\dfrac{M}{w}$。',
      '兩個真數相除，多出來的那個因數剛好約掉，只剩 $' + logT(b, String(N)) + '$。',
      '再問「$' + b + '$ 的幾次方是 $' + N + '$」：$' + N + '=' + b + '^{' + p.n + '}$，所以答案是 $' + p.n + '$。'];
    return ['係數先搬上去當次方：$2' + logT(b, String(p.u)) + '=' + logT(b, p.u + '^{2}') + '=' + logT(b, String(p.u * p.u)) + '$。',
      '再相加變相乘：$' + logT(b, String(p.u * p.u)) + '+' + logT(b, String(p.v * p.v)) + '=' + logT(b, (p.u * p.u) + '\\times' + (p.v * p.v)) + '$，而 $' + (p.u * p.u) + '\\times' + (p.v * p.v) + '=\\left(' + p.u + '\\times' + p.v + '\\right)^{2}=' + N + '^{2}$。',
      '$' + N + '^{2}=\\left(' + b + '^{' + p.n + '}\\right)^{2}=' + b + '^{' + (2 * p.n) + '}$，所以答案是 $' + (2 * p.n) + '$。'];
  };

  L1_SOL.logExpress = function (p) {
    var N = Math.pow(2, p.i) * Math.pow(3, p.j) * Math.pow(5, p.k);
    var e1 = term(p.i, '\\log2', true), e2 = term(p.j, '\\log3', e1 === ''), e3 = term(p.k, '\\log5', e1 + e2 === '');
    var c1 = p.i - p.k, cA = term(c1, 'a', true), cB = term(p.j, 'b', cA === ''), cC = term(p.k, '', cA + cB === '');
    var plain = cA + cB + cC; if (plain === '') plain = '0';
    var sT = term(p.ans[0], 'a', true); sT += term(p.ans[1], 'b', sT === ''); sT += term(p.ans[2], '', sT === ''); if (sT === '') sT = '0';
    var st = ['先把真數質因數分解：$' + N + '=2^{' + p.i + '}\\cdot3^{' + p.j + '}\\cdot5^{' + p.k + '}$。',
      '取對數，乘變加、次方拉下來：$\\log ' + N + '=' + (e1 + e2 + e3) + '$。',
      '題目只給 $a=\\log2$、$b=\\log3$，所以 $\\log5$ 要換掉：$\\log5=\\log\\dfrac{10}{2}=\\log10-\\log2=1-a$，代入整理成 $' + plain + '$。'];
    if (p.neg) st.push('題目問的是倒數：$\\log\\dfrac{1}{' + N + '}=-\\log ' + N + '$，整個式子變號，得 $' + sT + '$。');
    return st;
  };

  L1_SOL.changeBase = function (p) {
    var A = F(p.ans[0], p.ans[1]), Pi = Math.pow(p.p, p.i), Qj = Math.pow(p.q, p.j), Qk = Math.pow(p.q, p.k), Pl = Math.pow(p.p, p.l);
    return ['換底公式：$\\log_{M}N=\\dfrac{\\log N}{\\log M}$，把兩個對數都換成常用對數。',
      '$' + logT(Pi, String(Qj)) + '=\\dfrac{\\log ' + Qj + '}{\\log ' + Pi + '}=\\dfrac{' + p.j + '\\log ' + p.q + '}{' + p.i + '\\log ' + p.p + '}$（次方拉下來當係數）；同理 $' + logT(Qk, String(Pl)) + '=\\dfrac{' + p.l + '\\log ' + p.p + '}{' + p.k + '\\log ' + p.q + '}$。',
      '相乘時 $\\log ' + p.p + '$ 與 $\\log ' + p.q + '$ 上下對消，只剩係數：$\\dfrac{' + p.j + '\\times' + p.l + '}{' + p.i + '\\times' + p.k + '}=\\dfrac{' + (p.j * p.l) + '}{' + (p.i * p.k) + '}=' + Fr.tex(A) + '$。'];
  };

  L1_SOL.digits = function (p) {
    var v = round4(p.n * lg(p.a)), fl = Math.floor(v + 1e-9);
    return ['先湊出 $\\log ' + p.a + '\\approx' + lg(p.a).toFixed(4) + '$（把 $' + p.a + '$ 分解成 $2,3,5,7$ 的乘積，其中 $\\log5=1-\\log2=0.6990$）。',
      '取對數把次方拉下來：$\\log ' + p.a + '^{' + p.n + '}=' + p.n + '\\log ' + p.a + '\\approx' + p.n + '\\times' + lg(p.a).toFixed(4) + '=' + v.toFixed(4) + '$。',
      '$' + fl + '\\le ' + v.toFixed(4) + '\\lt ' + (fl + 1) + '$ ⟹ $10^{' + fl + '}\\le ' + p.a + '^{' + p.n + '}\\lt 10^{' + (fl + 1) + '}$；$10^{' + fl + '}$ 是最小的 $' + (fl + 1) + '$ 位數，所以它是 $' + (fl + 1) + '$ 位數（位數＝首數 $+1$）。'];
  };

  L1_SOL.charMant = function (p) {
    if (p.type === 0) return ['$\\log x=' + p.c + '.' + p.m + '$：整數部分（首數）是 $' + p.c + '$，小數部分（尾數）是 $0.' + p.m + '$。',
      '首數 $' + p.c + '$ 表示 $' + p.c + '\\le\\log x\\lt ' + (p.c + 1) + '$，也就是 $10^{' + p.c + '}\\le x\\lt 10^{' + (p.c + 1) + '}$。',
      '$10^{' + p.c + '}$ 是最小的 $' + (p.c + 1) + '$ 位數，所以 $x$ 的整數部分是 $' + (p.c + 1) + '$ 位數。'];
    return ['$\\log y$ 是負的，先寫成「負整數 $+$ 正小數」：$-' + p.k + '.' + p.mm + '=-' + (p.k + 1) + '+0.' + (10 - p.mm) + '$，首數是 $-' + (p.k + 1) + '$。',
      '首數 $-' + (p.k + 1) + '$ 表示 $10^{-' + (p.k + 1) + '}\\le y\\lt 10^{-' + p.k + '}$。',
      '$10^{-' + (p.k + 1) + '}$ 這個數要到小數點後第 $' + (p.k + 1) + '$ 位才出現 $1$，所以 $y$ 第一個不為 $0$ 的數字也在第 $' + (p.k + 1) + '$ 位。'];
  };

  L1_SOL.leadDigit = function (p) {
    var v = round4(p.n * lg(p.a)), mant = round4(v - Math.floor(v)), d = lead(mant);
    var tab = [0, 0, LG[2], LG[3], LG[4], LG[5], LG[6], LG[7], LG[8], LG[9]];
    var loT = d === 1 ? '\\log1=0' : '\\log ' + d + '\\approx' + tab[d].toFixed(4);
    var hiT = d === 9 ? '\\log10=1' : '\\log ' + (d + 1) + '\\approx' + tab[d + 1].toFixed(4);
    return ['先取對數：$\\log ' + p.a + '^{' + p.n + '}=' + p.n + '\\log ' + p.a + '\\approx' + p.n + '\\times' + lg(p.a).toFixed(4) + '=' + v.toFixed(4) + '$。',
      '拆成首數與尾數：$' + v.toFixed(4) + '=' + Math.floor(v) + '+' + mant.toFixed(4) + '$，尾數是 $' + mant.toFixed(4) + '$——最高位數字只看尾數。',
      '尾數 $' + mant.toFixed(4) + '$ 落在 $' + loT + '$ 與 $' + hiT + '$ 之間，所以最高位數字是 $' + d + '$。'];
  };

  L1_SOL.logEqSimple = function (p) {
    var R = Math.pow(p.a, p.c);
    return ['對數的定義：$\\log_{' + p.a + '}M=' + p.c + '$ 就是 $M=' + p.a + '^{' + p.c + '}=' + R + '$。',
      '所以真數 $x' + term(p.p, '', false) + '=' + R + '$，移項得 $x=' + R + '-' + parT(p.p) + '=' + p.ans + '$。',
      '代回檢查真數：$' + p.ans + term(p.p, '', false) + '=' + R + '\\gt0$，合格。'];
  };

  L1_SOL.logIneqSimple = function (p) {
    var B = Math.pow(p.ak, p.c), inner = 'x' + term(-p.p, '', false);
    if (p.up === 1) return ['先寫定義域：真數 $' + inner + '\\gt0$ ⟹ $x\\gt' + p.p + '$。',
      '底數 $' + p.ak + '\\gt1$ 是遞增：把 $' + p.c + '$ 寫成 $\\log_{' + p.ak + '}' + B + '$，比真數時方向不變 ⟹ $' + inner + '\\lt ' + B + '$ ⟹ $x\\lt ' + (p.p + B) + '$。',
      '兩個條件取交集：$' + p.p + '\\lt x\\lt ' + (p.p + B) + '$。'];
    return ['先寫定義域：真數 $' + inner + '\\gt0$ ⟹ $x\\gt' + p.p + '$。',
      '底數 $\\dfrac{1}{' + p.ak + '}$ 小於 $1$ 是遞減：把 $-' + p.c + '$ 寫成 $\\log_{\\frac{1}{' + p.ak + '}}' + B + '$，比真數時<b>不等號反向</b> ⟹ $' + inner + '\\gt ' + B + '$ ⟹ $x\\gt ' + (p.p + B) + '$。',
      '$x\\gt ' + (p.p + B) + '$ 已經在定義域 $x\\gt' + p.p + '$ 裡面，所以答案就是 $x\\gt' + (p.p + B) + '$。'];
  };

  L1_SOL.logShift = function (p) {
    if (p.t === 0) {
      var sh = '(x' + term(-p.h, '', false) + ')';
      return ['左右平移：向' + (p.h > 0 ? '右' : '左') + '移 $' + Math.abs(p.h) + '$ 單位 ⟹ 真數的 $x$ 換成 $x' + term(-p.h, '', false) + '$，得 $y=' + logT(p.a, sh) + '$。',
        '上下平移：向' + (p.k > 0 ? '上' : '下') + '移 $' + Math.abs(p.k) + '$ 單位 ⟹ 整個式子' + (p.k > 0 ? '加' : '減') + ' $' + Math.abs(p.k) + '$：$y=' + logT(p.a, sh) + term(p.k, '', false) + '$。',
        '漸近線：原來 $y=' + logT(p.a, 'x') + '$ 在真數為 $0$ 的地方，即 $x=0$；左右移 $' + parT(p.h) + '$ 後變成 $x=' + p.h + '$，上下移不影響它。'];
    }
    if (p.t === 1) return ['對 $x$ 軸對稱：把 $y$ 換成 $-y$，原式變成 $-y=' + logT(p.a, 'x') + '$。',
      '兩邊乘 $-1$：$y=-' + logT(p.a, 'x') + '$。',
      '再把負號收進底數（$-\\log_{a}x=\\log_{a^{-1}}x$）：$y=' + logT(F(1, p.a), 'x') + '$。'];
    if (p.t === 2) return ['對 $y$ 軸對稱：把 $x$ 換成 $-x$。',
      '原式 $y=' + logT(p.a, 'x') + '$ 變成 $y=' + logT(p.a, '(-x)') + '$。',
      '定義域也跟著翻過去：原來要 $x\\gt0$，現在是 $-x\\gt0$，即 $x\\lt0$。'];
    return ['對直線 $y=x$ 對稱就是求<b>反函數</b>：把 $x$ 與 $y$ 對調。',
      '$y=' + logT(p.a, 'x') + '$ 對調成 $x=' + logT(p.a, 'y') + '$。',
      '再用對數的定義改寫：$x=' + logT(p.a, 'y') + '\\iff y=' + p.a + '^{x}$——指數函數與對數函數互為反函數。'];
  };

  L1_SOL.logOrder = function (p) {
    var nm = ['a', 'b', 'c'], vals = p.vals, idx = p.ans;
    var sign = nm.map(function (n2, i) { return '$' + n2 + '$ ' + (vals[i] > 0 ? '是正的' : (vals[i] < 0 ? '是負的' : '剛好是 $0$')); }).join('、');
    var band = nm.map(function (n2, i) {
      var v = vals[i];
      if (Math.abs(v - Math.round(v)) < 1e-9) return '$' + n2 + '=' + Math.round(v) + '$';
      return '$' + Math.floor(v) + '\\lt ' + n2 + '\\lt ' + (Math.floor(v) + 1) + '$';
    }).join('、');
    return ['先看正負：底數與真數同在 $1$ 的同側 ⟹ 對數為正；一個 $\\gt1$、一個 $\\lt1$ ⟹ 對數為負。這一題 ' + sign + '。',
      '再把每個數夾在相鄰的整數之間（想「底數的幾次方剛好是真數」，或換底估值）：' + band + '。',
      '照這個範圍由大到小排：$' + idx.map(function (i) { return nm[i]; }).join('\\gt ') + '$。'];
  };

  L1_SOL.logDomain = function (p) {
    if (p.type === 0) return ['對數有意義的條件是<b>真數 $\\gt0$</b>：要解 $x^{2}' + term(-(p.p + p.q), 'x', false) + term(p.p * p.q, '', false) + '\\gt0$。',
      '因式分解：$\\left(x' + term(-p.p, '', false) + '\\right)\\left(x' + term(-p.q, '', false) + '\\right)\\gt0$，兩根是 $' + p.p + '$ 與 $' + p.q + '$。',
      '開口向上且要 $\\gt0$ ⟹ 取<b>兩根之外</b>：$x\\lt ' + p.p + '$ 或 $x\\gt ' + p.q + '$。'];
    var excl = (p.p + 1 > p.q);
    return ['底數也含 $x$ 時有三個條件：底 $\\gt0$、底 $\\ne1$、真數 $\\gt0$，缺一不可。',
      '底 $x' + term(-p.p, '', false) + '\\gt0$ ⟹ $x\\gt' + p.p + '$；底 $\\ne1$ ⟹ $x\\ne' + (p.p + 1) + '$；真數 $x' + term(-p.q, '', false) + '\\gt0$ ⟹ $x\\gt' + p.q + '$。',
      '因為 $' + p.p + '\\lt ' + p.q + '$，交集是 $x\\gt' + p.q + '$；' + (excl
        ? '又 $' + (p.p + 1) + '\\gt' + p.q + '$ 落在這個範圍裡，要把 $x=' + (p.p + 1) + '$ 挖掉。'
        : '而 $' + (p.p + 1) + '\\le ' + p.q + '$ 本來就不在範圍內，不必另外排除。')];
  };

  L1_SOL.logQuadMin = function (p) {
    var c = p.h * p.h + p.k, xm = p.h >= 0 ? String(Math.pow(p.a, p.h)) : '\\dfrac{1}{' + Math.pow(p.a, -p.h) + '}';
    return ['令 $t=' + logT(p.a, 'x') + '$。因為 $x\\gt0$，$t$ 可以是<b>任意實數</b>，沒有額外的範圍限制。',
      '原式變成 $y=t^{2}' + term(-2 * p.h, 't', false) + term(c, '', false) + '$，配方：$y=\\left(t' + term(-p.h, '', false) + '\\right)^{2}' + term(p.k, '', false) + '$。',
      '平方項 $\\ge0$，所以最小值是 $' + p.k + '$，發生在 $t=' + p.h + '$。',
      '換回 $x$：$' + logT(p.a, 'x') + '=' + p.h + '$ ⟹ $x=' + p.a + '^{' + p.h + '}=' + xm + '$。'];
  };

  L1_SOL.logScale = function (p) {
    if (p.type === 0) {
      var e = p.e, whole = (e === Math.floor(e)), mulV = Math.pow(10, e), kk = Math.floor(e);
      var st = ['兩個地震各代一次公式：$\\log E_1=4.8+1.5\\times' + (p.m1 + p.d) + '$、$\\log E_2=4.8+1.5\\times' + p.m1 + '$。',
        '相減，常數 $4.8$ 消掉：$\\log\\dfrac{E_1}{E_2}=1.5\\left(' + (p.m1 + p.d) + '-' + p.m1 + '\\right)=1.5\\times' + p.d + '=' + e + '$。',
        '由對數定義 $\\dfrac{E_1}{E_2}=10^{' + e + '}' + (whole ? '=' + Math.round(mulV) : '') + '$' + (whole ? '，能量是 $' + Math.round(mulV) + '$ 倍。' : '。')];
      if (!whole) st.push('$10^{' + e + '}$ 不是整數：$10^{' + e + '}=10^{' + kk + '}\\times10^{0.5}=10^{' + kk + '}\\sqrt{10}\\approx'
        + (kk <= 1 ? String(Math.round(mulV * 10) / 10) : '3.16\\times10^{' + kk + '}') + '$ 倍。');
      return st;
    }
    if (p.type === 1) {
      var kn = Math.round(Math.log10(p.n));
      return ['設一台的強度是 $I$，$' + p.n + '$ 台同時運轉時強度相加變成 $' + p.n + 'I$。',
        '代進公式並把乘法拆開：$10\\log\\dfrac{' + p.n + 'I}{I_0}=10\\log ' + p.n + '+10\\log\\dfrac{I}{I_0}=10\\log ' + p.n + '+' + p.d0 + '$。',
        '$' + p.n + '=10^{' + kn + '}$ ⟹ $10\\log ' + p.n + '=10\\times' + kn + '=' + (10 * kn) + '$，所以是 $' + p.d0 + '+' + (10 * kn) + '=' + (p.d0 + 10 * kn) + '$ 分貝。'];
    }
    return ['由定義 $\\text{pH}=-\\log\\left[\\text{H}^{+}\\right]$ 反解濃度：$\\left[\\text{H}^{+}\\right]=10^{-\\text{pH}}$。',
      '甲的濃度 $=10^{-' + p.p1 + '}$、乙的濃度 $=10^{-' + (p.p1 + p.dd) + '}$。',
      '相除時指數相減：$\\dfrac{10^{-' + p.p1 + '}}{10^{-' + (p.p1 + p.dd) + '}}=10^{' + (p.p1 + p.dd) + '-' + p.p1 + '}=10^{' + p.dd + '}=' + Math.pow(10, p.dd) + '$，所以甲是乙的 $' + Math.pow(10, p.dd) + '$ 倍。'];
  };

  var META_L1 = [
      ['expLaw', '§1 指數律化簡'], ['radicalVal', '§1 根式與分數指數求值'], ['expOrder', '§1 同底指數比大小'], ['expEqSame', '§1 同底指數方程式'],
      ['expIneqSame', '§1 同底指數不等式'], ['expShift', '§1 指數函數的平移'], ['expQuadEq', '§1 換元二次的指數方程式'], ['growthTimes', '§1 每期成長 k 倍'],
      ['logDef', '§2 對數的定義求值'], ['logLaw', '§2 運算律化簡'], ['logExpress', '§2 用 log2、log3 表示'], ['changeBase', '§2 換底公式'],
      ['digits', '§2 位數'], ['charMant', '§2 首數與尾數的意義'], ['leadDigit', '§2 最高位數字'], ['logEqSimple', '§2 對數方程式（定義）'], ['logIneqSimple', '§2 對數不等式（定義域）'],
      ['logShift', '§3 對數函數的平移與對稱'], ['logOrder', '§3 對數值比大小'], ['logDomain', '§3 對數的定義域'], ['logQuadMin', '§3 換元二次的最小值'], ['logScale', '§3 對數刻度：地震與分貝']
  ];
  var META_L2 = [
      ['expSymmMin', '§1 對稱式換元的最值'], ['expIneqQuad', '§1 換元二次的指數不等式'], ['expAMGM', '§1 乘積定值的算幾'], ['expIntervalMax', '§1 指數在區間上的最值'],
      ['halfLife', '§1 半衰期'], ['compoundYears', '§1 成長率：至少幾年'],
      ['logQuadRange', '§2 對數換元的區間最值'], ['logEqQuad', '§2 對數換元的二次方程式'], ['logEqProduct', '§2 真數相乘的對數方程式'], ['logIneqBase', '§2 底數決定方向的對數不等式'],
      ['logSumTele', '§2 對數連加（望遠鏡）'], ['digitsLead', '§2 位數與最高位數字'], ['decimalFirst', '§2 小數點後第幾位非零'],
      ['logPointSym', '§3 對數函數上的點（多選）'], ['decayRatio', '§3 兩種半衰期的比'], ['dbMulti', '§3 分貝的疊加與倍數']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     答案全部精確；p 給 Python 獨立驗算。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};
  function parF(x) { return x.n < 0 ? '\\left(' + Fr.tex(x, true) + '\\right)' : Fr.tex(x, true); }
  function logV(b, arg) { return (b === 10 && arg.length === 1) ? '\\log ' + arg : logT(b, arg); }   /* 避免 \logx 黏字 */
  function powF(a, e) { return e >= 0 ? F(Math.pow(a, e), 1) : F(1, Math.pow(a, -e)); }

  /* L3-1　兩個指數的聯立：令 u=a^x、v=a^y */
  L3.expSystem = function (r) {
    var a = r.pick([2, 3]), y = r.int(1, a === 2 ? 5 : 3), d = r.int(1, a === 2 ? 3 : 2), x = y + d, v = r.int(0, 1);
    var ax = Math.pow(a, x), ay = Math.pow(a, y), D = v === 0 ? ax - ay : ax + ay, ad = Math.pow(a, d);
    var first = a + '^x' + (v === 0 ? '-' : '+') + a + '^y=' + D;
    return { q: '解聯立方程式 ' + T('\\begin{cases}' + first + '\\\\ ' + a + '^{x-y}=' + ad + '\\end{cases}') + '，求 ' + T('(x,y)') + '。',
      a: T('(x,y)=(' + x + ',' + y + ')'),
      h: '令 $u=' + a + '^x$、$v=' + a + '^y$：第二式是 $\\dfrac uv=' + ad + '$，即 $u=' + ad + 'v$；代入第一式得 $' + ((v === 0 ? ad - 1 : ad + 1) === 1 ? '' : (v === 0 ? ad - 1 : ad + 1)) + 'v=' + D + '$，先解出 $v$ 再換回 $y$。',
      p: { a: a, x: x, y: y, d: d, v: v, D: D } };
  };

  /* L3-2　a^{2x+1}＝a·(a^x)²：換元二次不等式（一個因式恆正） */
  L3.expIneqHalf = function (r) {
    var a = r.pick([2, 3]), k = r.pick(a === 2 ? [3, 5, 6, 7, 10, 12, 2, 4, 8] : [2, 4, 5, 6, 7, 10, 3, 9]), m = r.pick([1, 3, 5]);
    var op = r.pick(['\\le ', '\\lt ', '\\ge ', '\\gt ']), c1 = m - a * k, c0 = -m * k;
    var e = Math.round(Math.log(k) / Math.log(a)), isPow = Math.pow(a, e) === k;
    var lhs = (a * a) + '^{x+\\frac12}' + (Math.abs(c1) === 1 ? (c1 < 0 ? '-' : '+') + a + '^x' : term(c1, '\\cdot ' + a + '^x', false)) + term(c0, '', false);
    return { q: '解不等式 ' + T(lhs + op + '0') + '。', a: T('x' + op + (isPow ? e : '\\log_{' + a + '}' + k)),
      h: '$' + (a * a) + '^{x+\\frac12}=' + a + '\\cdot(' + a + '^x)^2$。令 $t=' + a + '^x\\gt 0$：$' + a + 't^2' + term(c1, 't', false) + term(c0, '', false) + '=(' + a + 't+' + m + ')(t-' + k + ')$，其中 $' + a + 't+' + m + '$ 恆正，只要看 $t-' + k + '$ 的正負，再取 $\\log_{' + a + '}$。',
      p: { a: a, k: k, m: m, op: op.trim(), c1: c1, c0: c0 } };
  };

  /* L3-3　區間最值：t=2^x 的範圍要一起換，再看頂點 */
  L3.expRangeSum = function (r) {
    var l = r.pick([-1, 0, 0, 1]), rr = r.pick([2, 3]), c = r.int(1, 3), e = r.int(-3, 9), v = r.int(0, 1);
    var f = function (t) { return Fr.add(Fr.sub(Fr.mul(t, t), Fr.mul(F(Math.pow(2, c)), t)), F(e)); };
    var cands = [powF(2, l), powF(2, rr)], vt = powF(2, c - 1);
    if (!Fr.lt(vt, cands[0]) && !Fr.lt(cands[1], vt)) cands.push(vt);
    var vals = cands.map(f), M = vals[0], mn = vals[0];
    vals.forEach(function (x) { if (Fr.lt(M, x)) M = x; if (Fr.lt(x, mn)) mn = x; });
    var S = Fr.add(M, mn), fx = '4^x-2^{x+' + c + '}' + term(e, '', false);
    return { q: '若 ' + T(l + '\\le x\\le ' + rr) + '，函數 ' + T('f(x)=' + fx) + ' 的最大值為 ' + T('M') + '、最小值為 ' + T('m') + '，求 ' + (v === 0 ? T('M+m') : T('M') + ' 與 ' + T('m')) + '。',
      a: v === 0 ? T(Fr.tex(S)) : T('M=' + Fr.tex(M) + ',\\ m=' + Fr.tex(mn)),
      h: '令 $t=2^x$，$x$ 在 $[' + l + ',' + rr + ']$ ⟹ $t$ 在 $\\left[' + Fr.tex(cands[0], true) + ',' + Fr.tex(cands[1], true) + '\\right]$；$f=t^2-' + Math.pow(2, c) + 't' + term(e, '', false) + '$ 的頂點在 $t=' + Fr.tex(vt, true) + '$，先看它在不在區間內，再比兩個端點。',
      p: { l: l, r: rr, c: c, e: e, v: v, M: [M.n, M.d], m: [mn.n, mn.d] } };
  };

  /* L3-4　指數塔 a^{10^x}=10^N：取兩次對數 */
  L3.expTower = function (r) {
    var a, N, val, x, tries = 0;
    do { a = r.pick([2, 3, 7]); N = r.int(2, 60); val = N / LG[a]; x = Math.log10(val); var xt = Math.log10(N / Math.log10(a)); }
    while ((x <= 0.04 || x >= 2.46 || Math.abs(x * 2 - Math.round(x * 2)) < 0.08 || Math.floor(x * 2) !== Math.floor(xt * 2)) && tries++ < 200);
    var idx = Math.floor(x * 2) + 1;
    return { q: '方程式 ' + T(a + '^{10^x}=10^{' + N + '}') + ' 的實數解 ' + T('x') + ' 落在哪個範圍？（' + T('\\log' + a + '\\approx' + LG[a].toFixed(4)) + '）<br>(1) ' + T('0\\lt x\\lt 0.5') + '　(2) ' + T('0.5\\lt x\\lt 1') + '　(3) ' + T('1\\lt x\\lt 1.5') + '　(4) ' + T('1.5\\lt x\\lt 2') + '　(5) ' + T('2\\lt x\\lt 2.5'),
      a: '(' + idx + ')　（' + T('10^x\\approx' + val.toFixed(2)) + '）',
      h: '兩邊取 $\\log$：$10^x\\cdot\\log' + a + '=' + N + '$ ⟹ $10^x=\\dfrac{' + N + '}{' + LG[a].toFixed(4) + '}\\approx' + val.toFixed(2) + '$。再跟 $10^{0.5}\\approx3.16$、$10^1=10$、$10^{1.5}\\approx31.6$、$10^2=100$、$10^{2.5}\\approx316$ 比。',
      p: { a: a, N: N, idx: idx } };
  };

  /* L3-5　鉛直線截兩條指數曲線：函數值相減，出現 t=2^h 的二次式 */
  L3.vertGap = function (r) {
    var a = r.pick([2, 2, 3]), fam = r.int(0, 2) === 0 ? 1 : 0, c2, h2, v = r.int(0, 1);      /* c2 = 2c、h2 = 2h（整數化） */
    if (fam === 0) { var c = r.int(0, a === 2 ? 3 : 1); c2 = 2 * c; h2 = 2 * Math.min(c + r.int(1, a === 2 ? 3 : 2), a === 2 ? 5 : 3); }      /* 數字上限：4^5=1024、9^3=729 */
    else { c2 = a === 2 ? r.pick([1, 3]) : 1; h2 = c2 + 2 * r.int(1, a === 2 ? 3 : 2); }
    var A2 = a * a, L = Math.round(Math.pow(a, h2) - Math.pow(a, (c2 + h2) / 2)), hF = F(h2, 2), cT = c2 === 0 ? '' : '+' + Fr.tex(F(c2, 2), true);
    var coef = c2 % 2 ? sqrtTex(Math.pow(a, c2)) : String(Math.pow(a, c2 / 2)), cf = coef === '1' ? '' : coef;
    return { q: '直線 ' + T('x=h') + ' 分別與 ' + T('y=' + a + '^{x' + cT + '}') + '、' + T('y=' + A2 + '^x') + ' 的圖形交於 ' + T('A') + '、' + T('B') + ' 兩點，且 ' + T('\\overline{AB}=' + L) + '，求 ' + (v === 0 ? T('h') : T('B') + ' 點的坐標') + '。',
      a: v === 0 ? T('h=' + Fr.tex(hF)) : T('B\\left(' + Fr.tex(hF, true) + ',' + Math.pow(a, h2) + '\\right)'),
      h: '$\\overline{AB}=\\left|' + A2 + '^h-' + a + '^{h' + cT + '}\\right|$。令 $t=' + a + '^h\\gt 0$：$t^2-' + cf + 't=' + L + '$（反過來 $' + cf + 't-t^2$ 的最大值太小，到不了 $' + L + '$），解出 $t$ 再寫成 $' + a + '$ 的次方。',
      p: { a: a, fam: fam, c2: c2, h2: h2, L: L, v: v } };
  };

  /* L3-6　x 藏在對數等式裡：log_p(pq) = (x−c−1)/(x−c) ⟹ q^x = q^c / p */
  L3.logEqSolveX = function (r) {
    var p = r.pick([2, 3, 5, 7]), q = r.pick([2, 3, 5, 7]); while (q === p) q = r.pick([2, 3, 5, 7]);
    var c = r.pick([-1, 0, 1, 2]), ans = c >= 0 ? F(Math.pow(q, c), p) : F(1, p * q);
    var num = 'x' + term(-(c + 1), '', false), den = 'x' + term(-c, '', false);
    return { q: '設 ' + T('\\log_{' + p + '}' + (p * q) + '=\\dfrac{' + num + '}{' + den + '}') + '，求 ' + T(q + '^x') + ' 的值。（化為最簡分數或整數）', a: T(q + '^x=' + Fr.tex(ans)),
      h: '右邊 $=1-\\dfrac{1}{' + den + '}$，左邊 $=1+\\log_{' + p + '}' + q + '$ ⟹ $' + den + '=-\\dfrac{1}{\\log_{' + p + '}' + q + '}=-\\log_{' + q + '}' + p + '$。所以 $x=' + (c === 0 ? '' : c) + '-\\log_{' + q + '}' + p + '$，再代進 $' + q + '^x$ 用指數律拆開。',
      p: { p: p, q: q, c: c, ans: [ans.n, ans.d] } };
  };

  /* L3-7　三個不同底的對數：乘積 ＝ 兩兩乘積之和 ⟹ x = abc 或 1 */
  L3.logTripleProduct = function (r) {
    var bs = r.shuffle([2, 3, 4, 5, 6, 7, 8, 10]).slice(0, 3).sort(function (u, v) { return u - v; }), prod = bs[0] * bs[1] * bs[2];
    var A = logV(bs[0], 'x'), B = logV(bs[1], 'x'), C = logV(bs[2], 'x');
    return { q: '若 ' + T(A + '\\cdot ' + B + '\\cdot ' + C + '=' + A + '\\cdot ' + B + '+' + B + '\\cdot ' + C + '+' + C + '\\cdot ' + A) + '，求所有滿足的 ' + T('x') + '。',
      a: T('x=' + prod + '\\ \\text{或}\\ x=1'),
      h: '全部換成 $t=\\log x$：$' + A + '=\\dfrac{t}{\\log' + bs[0] + '}$……兩邊都有 $t^2$。<b>先別急著約掉</b>：$t=0$（即 $x=1$）本身就是解；$t\\ne 0$ 時約掉 $t^2$ 得 $t=\\log' + bs[0] + '+\\log' + bs[1] + '+\\log' + bs[2] + '$。',
      p: { bs: bs, ans: prod } };
  };

  /* L3-8　位數與小數位 → 翻譯成 log 的不等式，再相加相減 */
  L3.digitsAB = function (r) {
    var m = r.int(6, 14), k = r.int(2, 5);
    var lo = m - 1 - k, da = lo % 2 === 0 ? [lo / 2 + 1] : [(lo - 1) / 2 + 1, (lo - 1) / 2 + 2];
    var s = m + k, db = s % 2 === 0 ? [s / 2] : [(s - 1) / 2, (s - 1) / 2 + 1];
    var say = function (arr) { return arr.map(function (d) { return T(String(d)); }).join(' 或 ') + ' 位數'; };
    return { q: '兩正整數 ' + T('a,b') + ' 的乘積 ' + T('ab') + ' 為 ' + T(String(m)) + ' 位數，且 ' + T('\\dfrac ab') + ' 化為小數後，從小數點後第 ' + T(String(k)) + ' 位開始出現不為 ' + T('0') + ' 的數字。問 ' + T('a') + ' 可能是幾位數？' + T('b') + ' 可能是幾位數？',
      a: T('a') + '：' + say(da) + '；' + T('b') + '：' + say(db),
      h: '翻成不等式：$' + (m - 1) + '\\le\\log a+\\log b\\lt ' + m + '$，$-' + k + '\\le\\log a-\\log b\\lt ' + (-k + 1) + '$。兩式相加得 $\\log a$ 的範圍、相減（注意方向）得 $\\log b$ 的範圍，再用「位數 $=$ 首數 $+1$」。',
      p: { m: m, k: k, da: da, db: db } };
  };

  /* L3-9　用兩個奇怪的 log 表示 log t：展開成 log2、log3、log7 的線性組合再消元（候選在載入時以分數精確求解） */
  var LINCOMBO = (function () {
    var NS = [2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 20, 24, 27, 35, 48, 49, 63, 80], out = [];
    function vec(n) {           /* log((n+1)/n) = c2·log2 + c3·log3 + c7·log7 + c0（log5 = 1 − log2） */
      var e = { 2: 0, 3: 0, 5: 0, 7: 0 };
      [[n + 1, 1], [n, -1]].forEach(function (pr) { var x = pr[0]; [2, 3, 5, 7].forEach(function (q) { while (x % q === 0) { e[q] += pr[1]; x /= q; } }); if (x !== 1) e.bad = 1; });
      return e.bad ? null : [e[2] - e[5], e[3], e[7], e[5]];
    }
    function solve(v1, v2, tg) {
      for (var i = 0; i < 3; i++) for (var j = i + 1; j < 3; j++) {
        var det = v1[i] * v2[j] - v1[j] * v2[i]; if (det === 0) continue;
        var al = F(tg[i] * v2[j] - tg[j] * v2[i], det), be = F(v1[i] * tg[j] - v1[j] * tg[i], det), k = 3 - i - j;
        if (!Fr.eq(Fr.add(Fr.mul(al, F(v1[k])), Fr.mul(be, F(v2[k]))), F(tg[k]))) return null;
        var ga = Fr.sub(F(0), Fr.add(Fr.mul(al, F(v1[3])), Fr.mul(be, F(v2[3]))));
        return [al, be, ga];
      }
      return null;
    }
    for (var i1 = 0; i1 < NS.length; i1++) for (var i2 = i1 + 1; i2 < NS.length; i2++) {
      var v1 = vec(NS[i1]), v2 = vec(NS[i2]); if (!v1 || !v2) continue;
      [[2, [1, 0, 0]], [3, [0, 1, 0]], [7, [0, 0, 1]]].forEach(function (tt) {
        var s = solve(v1, v2, tt[1]); if (!s || s[0].n === 0 || s[1].n === 0) return;
        var D = s[0].d * s[1].d / gcd(s[0].d, s[1].d); D = D * s[2].d / gcd(D, s[2].d);
        if (D <= 30 && Math.abs(s[0].n) <= 12 && Math.abs(s[1].n) <= 12) out.push({ n1: NS[i1], n2: NS[i2], t: tt[0], s: s, D: D });
      });
    }
    return out;
  })();
  L3.logLinearCombo = function (r) {
    var it = r.pick(LINCOMBO), s = it.s, D = it.D, ca = s[0].n * (D / s[0].d), cb = s[1].n * (D / s[1].d), cc = s[2].n * (D / s[2].d);
    var num = term(ca, 'a', true) + term(cb, 'b', false) + term(cc, '', false), ansT = D === 1 ? num : '\\dfrac{' + num + '}{' + D + '}';
    var lt = function (n) { return '\\log\\left(1+\\dfrac{1}{' + n + '}\\right)'; };
    return { q: '設 ' + T('a=' + lt(it.n1)) + '、' + T('b=' + lt(it.n2)) + '，試以 ' + T('a,b') + ' 表示 ' + T('\\log' + it.t) + '。', a: T('\\log' + it.t + '=' + ansT),
      h: '$1+\\dfrac1{' + it.n1 + '}=\\dfrac{' + (it.n1 + 1) + '}{' + it.n1 + '}$、$1+\\dfrac1{' + it.n2 + '}=\\dfrac{' + (it.n2 + 1) + '}{' + it.n2 + '}$：把分子分母質因數分解，$a,b$ 都寫成 $\\log2,\\log3,\\log7$ 的一次式（$\\log5=1-\\log2$），再消去不要的那個。',
      p: { n1: it.n1, n2: it.n2, t: it.t, al: [s[0].n, s[0].d], be: [s[1].n, s[1].d], ga: [s[2].n, s[2].d] } };
  };

  /* L3-10　(log px)(log qx)=c 兩根之積：令 s=log x，用根與係數 */
  L3.logProductRoots = function (r) {
    var b = r.pick([10, 10, 2, 3]), p = r.int(2, 9), q = r.int(2, 9); while (q === p) q = r.int(2, 9);
    var c = r.int(1, 3), lp = function (n) { return '\\left(' + logV(b, n + 'x') + '\\right)'; };
    return { q: '若方程式 ' + T(lp(p) + lp(q) + '=' + c) + ' 的兩根為 ' + T('\\alpha,\\beta') + '，求 ' + T('\\alpha\\beta') + '。', a: T('\\alpha\\beta=' + Fr.tex(F(1, p * q))),
      h: '令 $s=' + logV(b, 'x') + '$：$(s+' + logV(b, String(p)) + ')(s+' + logV(b, String(q)) + ')=' + c + '$ 是 $s$ 的二次方程式，兩根之和 $s_1+s_2=-(' + logV(b, String(p)) + '+' + logV(b, String(q)) + ')=-' + logV(b, String(p * q)) + '$；而 $' + logV(b, '(\\alpha\\beta)') + '=s_1+s_2$。',
      p: { b: b, p: p, q: q, c: c, ans: [1, p * q] } };
  };

  /* L3-11　大數的個位、位數、最高位：個位看週期，其餘靠首數與尾數（表值結果須與 BigInt 精確值一致） */
  L3.bigNumMulti = function (r) {
    var P, m, Q, n, u, Dg, ld, tries = 0, tab = [LG[2], LG[3], LG[4], LG[5], LG[6], LG[7], LG[8], LG[9]];
    while (tries++ < 80) {
      P = r.pick([2, 3, 6, 7, 8, 9, 12]); Q = r.pick([2, 3, 6, 7, 8, 9, 12]); if (P === Q) continue;
      m = r.int(8, 20); n = r.int(8, 20);
      var A = BigInt(P) ** BigInt(m), B = BigInt(Q) ** BigInt(n), AB = (A * B).toString();
      var v = round4(m * lg(P) + n * lg(Q)), mant = round4(v - Math.floor(v));
      if (tab.some(function (t) { return Math.abs(mant - t) < 0.006; }) || mant < 0.006) continue;
      u = Number((A + B) % 10n); Dg = AB.length; ld = Number(AB[0]);
      if (Math.floor(v) + 1 === Dg && lead(mant) === ld) break;
    }
    return { q: '設 ' + T('a=' + P + '^{' + m + '}') + '、' + T('b=' + Q + '^{' + n + '}') + '。（' + T('\\log2\\approx0.3010') + '、' + T('\\log3\\approx0.4771') + '、' + T('\\log7\\approx0.8451') + '）求：(1) ' + T('a+b') + ' 的個位數字　(2) ' + T('ab') + ' 是幾位數　(3) ' + T('ab') + ' 的最高位數字。',
      a: '(1) ' + T(String(u)) + '　(2) ' + T(String(Dg)) + ' 位數　(3) ' + T(String(ld)),
      h: '(1) 個位數字有週期：把 $' + P + '^n$、$' + Q + '^n$ 的個位各列幾項找週期，再看指數除以週期的餘數。(2)(3) $\\log ab=' + m + '\\log' + P + '+' + n + '\\log' + Q + '$，首數 $+1$ 是位數，尾數落在 $\\log k$ 與 $\\log(k+1)$ 之間則最高位是 $k$。',
      p: { P: P, m: m, Q: Q, n: n, ans: [u, Dg, ld] } };
  };

  /* L3-12　平移後與已知圖形重合 → 用運算律把平移後的式子整理成 log_a(x−c) */
  L3.logShiftMatch = function (r) {
    var a = r.pick([2, 3]), dh = r.nz(-4, 4), dv = r.pick([-1, -2, -3, -1, -2, 1]), c = r.int(-3, 5);
    var A = dv < 0 ? F(Math.pow(a, -dv)) : F(1, Math.pow(a, dv)), B = Fr.mul(A, F(dh - c));
    return { q: '將 ' + T('y=' + logV(a, '(Ax+B)')) + ' 的圖形向' + (dh > 0 ? '右' : '左') + '平移 ' + T(String(Math.abs(dh))) + ' 單位、再向' + (dv > 0 ? '上' : '下') + '平移 ' + T(String(Math.abs(dv))) + ' 單位後，得到 ' + T('y=' + logV(a, '(x' + term(-c, '', false) + ')')) + ' 的圖形，求 ' + T('(A,B)') + '。',
      a: T('(A,B)=\\left(' + Fr.tex(A, true) + ',' + Fr.tex(B, true) + '\\right)'),
      h: '平移後是 $y=' + logV(a, '\\big(A(x' + term(-dh, '', false) + ')+B\\big)') + term(dv, '', false) + '$；把 $' + dv + '$ 寫成 $' + logV(a, dv < 0 ? '\\frac{1}{' + Math.pow(a, -dv) + '}' : String(Math.pow(a, dv))) + '$ 併進真數，再與 $x' + term(-c, '', false) + '$ 比較 $x$ 的係數與常數項。',
      p: { a: a, dh: dh, dv: dv, c: c, A: [A.n, A.d], B: [B.n, B.d] } };
  };

  /* L3-13　log_a(二次式) 的區間最值：外層遞增，只要管裡面的二次式 */
  L3.logQuadInterval = function (r) {
    var a = r.pick([2, 3]), h = r.int(1, 3), mv = r.int(1, 4), C = h * h + mv, dl = r.int(1, 3), dr = r.int(1, 3), v = r.int(0, 1);
    if (dl === dr) dr = dl === 3 ? 2 : dl + 1;
    var l = h - dl, rr = h + dr, al = v === 0 ? (dl > dr ? l : rr) : h, be = (al - h) * (al - h) + mv;
    return { q: '若 ' + T(l + '\\le x\\le ' + rr) + '，函數 ' + T('g(x)=' + logV(a, '\\left(x^2' + term(-2 * h, 'x', false) + '+' + C + '\\right)')) + ' 在 ' + T('x=\\alpha') + ' 時有最' + (v === 0 ? '大' : '小') + '值 ' + T(logV(a, '\\beta')) + '，求 ' + T('(\\alpha,\\beta)') + '。',
      a: T('(\\alpha,\\beta)=(' + al + ',' + be + ')'),
      h: '底數 $' + a + '\\gt 1$，$\\log$ 遞增：裡面的二次式最' + (v === 0 ? '大' : '小') + '，$g$ 就最' + (v === 0 ? '大' : '小') + '。$x^2' + term(-2 * h, 'x', false) + '+' + C + '=(x-' + h + ')^2+' + mv + '$，頂點 $x=' + h + '$ 在區間內；' + (v === 0 ? '最大值在離 $' + h + '$ 較遠的端點。' : '最小值就在頂點。'),
      p: { a: a, h: h, C: C, l: l, r: rr, v: v, ans: [al, be] } };
  };

  /* L3-14　對 y 軸對稱與平移後求交點：兩個新函數先寫對，再用「真數相等」 */
  L3.logReflectShiftMeet = function (r) {
    var a = r.pick([2, 3]), s = r.int(1, 6), k = r.pick([1, 2, 3, -1, -2]), ak = powF(a, k);
    var x = Fr.div(Fr.mul(F(-s), ak), Fr.add(F(1), ak));
    return { q: '將 ' + T('f(x)=' + logV(a, 'x')) + ' 的圖形對 ' + T('y') + ' 軸對稱得 ' + T('y=g(x)') + '；將 ' + T('f(x)') + ' 的圖形向左平移 ' + T(String(s)) + ' 單位、向' + (k > 0 ? '上' : '下') + '平移 ' + T(String(Math.abs(k))) + ' 單位得 ' + T('y=h(x)') + '。求 ' + T('y=g(x)') + ' 與 ' + T('y=h(x)') + ' 交點的 ' + T('x') + ' 坐標。',
      a: T('x=' + Fr.tex(x)),
      h: '$g(x)=' + logV(a, '(-x)') + '$、$h(x)=' + logV(a, '(x+' + s + ')') + term(k, '', false) + '=' + logV(a, '\\big(' + Fr.tex(ak, true) + '(x+' + s + ')\\big)') + '$。令真數相等：$-x=' + Fr.tex(ak, true) + '(x+' + s + ')$；解完檢查 $-' + s + '\\lt x\\lt 0$。',
      p: { a: a, s: s, k: k, ans: [x.n, x.d] } };
  };

  /* L3-15　反函數圖形過 (m,n) ⟺ 原函數過 (n,m) */
  L3.inverseThroughPoint = function (r) {
    var a = r.pick([2, 3, 5]), e = r.int(1, a === 5 ? 2 : 3), b = r.int(-2, 4), v = r.int(0, 1), N = Math.pow(a, e);
    while (b + e === N) b = r.int(-2, 4);      /* 避免給的點剛好在 y=x 上 */
    return { q: '設 ' + T('y=b+\\log_a x') + '（' + T('a\\gt 0,\\ a\\ne 1') + '）的圖形通過 ' + T('(1,' + b + ')') + '，且它對直線 ' + T('y=x') + ' 對稱的圖形通過 ' + T('(' + (b + e) + ',' + N + ')') + '，求 ' + (v === 0 ? T('a+b') : T('(a,b)')) + '。',
      a: v === 0 ? T('a+b=' + (a + b)) : T('(a,b)=(' + a + ',' + b + ')'),
      h: '代 $(1,' + b + ')$：$\\log_a1=0$ ⟹ $b=' + b + '$。對 $y=x$ 對稱的圖形過 $(' + (b + e) + ',' + N + ')$ ⟺ 原圖形過 $(' + N + ',' + (b + e) + ')$：$' + (b + e) + '=' + b + '+\\log_a' + N + '$ ⟹ $\\log_a' + N + '=' + e + '$。',
      p: { a: a, e: e, b: b, v: v, N: N } };
  };

  var META_L3 = [['expSystem', '兩個指數的聯立'], ['expIneqHalf', '4^{x+½} 型換元二次不等式'], ['expRangeSum', '換元後的區間最值'], ['expTower', '指數塔：取兩次對數'], ['vertGap', '鉛直線截兩條指數曲線'], ['logEqSolveX', 'x 藏在對數等式裡'], ['logTripleProduct', '三種底的對數相乘'], ['digitsAB', '位數與小數位翻成 log 不等式'], ['logLinearCombo', '用兩個 log 表示 log t'], ['logProductRoots', '(log px)(log qx)=c 的兩根之積'], ['bigNumMulti', '大數的個位、位數、最高位'], ['logShiftMatch', '平移後與已知圖形重合'], ['logQuadInterval', 'log(二次式) 的區間最值'], ['logReflectShiftMeet', '對稱與平移後求交點'], ['inverseThroughPoint', '反函數圖形過定點']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'expSystem', 'L3-2': 'expIneqHalf', 'L3-3': 'expRangeSum', 'L3-4': 'expTower', 'L3-5': 'vertGap', 'L3-6': 'logEqSolveX', 'L3-7': 'logTripleProduct', 'L3-8': 'digitsAB', 'L3-9': 'logLinearCombo', 'L3-10': 'logProductRoots', 'L3-11': 'bigNumMulti', 'L3-12': 'logShiftMatch', 'L3-13': 'logQuadInterval', 'L3-14': 'logReflectShiftMeet', 'L3-15': 'inverseThroughPoint' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：整數指數律、常用對數基本值（高一上 ch1）、二次不等式與配方極值（高一上 ch3）、等比數列（高一下 ch1）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  function intExpLaw0(r) {
    var a = r.pick([2, 3, 5]), m = r.nz(-4, 5), n = r.nz(-4, 5), k = r.nz(-3, 4), v = r.int(0, 1), e, expr;
    if (m === 1) m = 2; if (n === 1) n = 3; if (k === 1) k = 2;      /* 不寫 a^{1} */
    if (v === 0) { e = m + n - k; expr = a + '^{' + m + '}\\times ' + a + '^{' + n + '}\\div ' + a + '^{' + k + '}'; }
    else { n = r.pick([2, 3, -1, -2]); m = r.pick([-3, -2, 2, 3]); e = m * n - k; expr = '\\left(' + a + '^{' + m + '}\\right)^{' + n + '}\\div ' + a + '^{' + k + '}'; }
    if (Math.abs(e) > 5 || e === 0) return intExpLaw0(r);
    var val = e >= 0 ? F(Math.pow(a, e), 1) : F(1, Math.pow(a, -e));
    return { q: '求 ' + T(expr) + ' 的值。', a: T(Fr.tex(val)),
      h: (v === 0 ? '同底數相乘，指數相加：$' + a + '^{' + m + '}\\times ' + a + '^{' + n + '}=' + a + '^{' + (m + n) + '}$；' : '次方的次方，指數相乘：$\\left(' + a + '^{' + m + '}\\right)^{' + n + '}=' + a + '^{' + (m * n) + '}$；') + '再除以 $' + a + '^{' + k + '}$，指數要減 $' + (k < 0 ? '(' + k + ')' : k) + '$' + (k < 0 ? '（減負數等於加）' : '') + '。最後若是負指數，記得它是倒數：$' + a + '^{-n}=\\dfrac{1}{' + a + '^n}$。',
      p: { a: a, m: m, n: n, k: k, v: v, e: e, ans: [val.n, val.d] } };
  }
  L0.intExpLaw = intExpLaw0;
  L0.logBasic = function (r) {
    var v = r.int(0, 2), k, ans, expr;
    if (v === 0) { k = r.nz(-4, 6); ans = F(k); expr = k > 0 ? '\\log ' + Math.pow(10, k) : '\\log ' + (1 / Math.pow(10, -k)).toFixed(-k); }
    else if (v === 1) { k = r.pick([2, 3, 4, 5]); var j = r.nz(-3, 3); ans = F(j, k); expr = '\\log\\sqrt[' + k + ']{10^{' + j + '}}'; if (k === 2) expr = '\\log\\sqrt{10^{' + j + '}}'; }
    else { var s = r.int(1, 5), t = r.nz(-4, 4); k = s; ans = F(s + t); expr = '\\log\\left(10^{' + s + '}\\times 10^{' + t + '}\\right)'; var j2 = t; }
    return { q: '求 ' + T(expr) + ' 的值。', a: T(Fr.tex(ans)),
      h: '$\\log$ 問的是「$10$ 的幾次方」。' + (v === 0 ? (k > 0 ? '數一數 $1$ 後面有幾個 $0$：' + k + ' 個 $0$ 就是 $10^{' + k + '}$。' : '小數點後第 $' + (-k) + '$ 位才出現 $1$，就是 $10^{' + k + '}$（負指數是倒數）。') : v === 1 ? '根號是分數指數：$\\sqrt' + (k === 2 ? '' : '[' + k + ']') + '{10^{' + j + '}}=10^{\\frac{' + j + '}{' + k + '}}$，指數就是答案（記得約分）。' : '先用指數律合併：$10^{' + s + '}\\times 10^{' + t + '}=10^{' + s + '+(' + t + ')}$，$\\log$ 把指數「取下來」。'),
      p: { v: v, k: k, j: v === 1 ? j : (v === 2 ? j2 : 0), ans: [ans.n, ans.d] } };
  };
  L0.quadIneq = function (r) {
    var p = r.int(-6, 4), q = p + r.int(1, 7), op = r.pick(['\\lt ', '\\le ', '\\gt ', '\\ge ']), b = -(p + q), c = p * q;
    var lhs = 'x^2' + term(b, 'x', false) + term(c, '', false), inside = op === '\\lt ' || op === '\\le ', o = op;
    var ans = inside ? p + o + 'x' + o + q : 'x' + (op === '\\gt ' ? '\\lt ' : '\\le ') + p + '\\ \\text{或}\\ x' + o + q;
    return { q: '解不等式 ' + T(lhs + op + '0') + '。', a: T(ans),
      h: '先因式分解：$' + lhs + '=(x' + term(-p, '', false) + ')(x' + term(-q, '', false) + ')$。開口向上的拋物線，「小於 $0$」取兩根之間、「大於 $0$」取兩根之外。',
      p: { p: p, q: q, op: op.trim() } };
  };
  L0.quadVertex = function (r) {
    var h = r.nz(-5, 5), k = r.int(-9, 9), s = r.pick([1, 1, -1, 2]), b = -2 * s * h, c = s * h * h + k;
    var fx = term(s, 'x^2', true) + term(b, 'x', false) + term(c, '', false);
    return { q: '求二次函數 ' + T('y=' + fx) + ' 的最' + (s > 0 ? '小' : '大') + '值，以及此時的 ' + T('x') + '。', a: T('x=' + h) + ' 時，最' + (s > 0 ? '小' : '大') + '值 ' + T(String(k)),
      h: '配方：$y=' + (s === 1 ? '' : s === -1 ? '-' : s) + '(x' + term(-h, '', false) + ')^2' + term(k, '', false) + '$。平方項最小是 $0$，所以頂點就是答案。',
      p: { s: s, h: h, k: k, b: b, c: c } };
  };
  L0.geoSeq = function (r) {
    var a1 = r.pick([1, 2, 3, 4, 5, 6, 8]), v = r.int(0, 2), q, n, ans;
    if (v === 0) { q = r.pick([2, 3, -2]); n = r.int(4, 7); ans = F(a1 * Math.pow(q, n - 1)); }
    else if (v === 1) { q = 2; a1 = Math.pow(2, r.int(4, 8)); n = r.int(4, 8); ans = F(a1, Math.pow(2, n - 1)); }
    else { q = r.pick([2, 3]); n = r.int(3, 6); ans = F(q); }
    var qT = v === 1 ? '\\dfrac12' : String(q);
    if (v === 2) return { q: '等比數列首項為 ' + T(String(a1)) + '、第 ' + T(String(n)) + ' 項為 ' + T(String(a1 * Math.pow(q, n - 1))) + '，且公比為正數，求公比。', a: T(String(q)),
      h: '$a_n=a_1r^{n-1}$：$' + a1 + '\\cdot r^{' + (n - 1) + '}=' + (a1 * Math.pow(q, n - 1)) + '$，先除掉首項，再想「誰的 $' + (n - 1) + '$ 次方」。', p: { v: v, a1: a1, q: [q, 1], n: n, ans: [q, 1] } };
    return { q: '等比數列首項為 ' + T(String(a1)) + '、公比為 ' + T(qT) + '，求第 ' + T(String(n)) + ' 項。', a: T(Fr.tex(ans)),
      h: '$a_n=a_1r^{n-1}$：從第 $1$ 項走到第 $' + n + '$ 項只乘了 $' + (n - 1) + '$ 次公比（不是 $' + n + '$ 次）。', p: { v: v, a1: a1, q: v === 1 ? [1, 2] : [q, 1], n: n, ans: [ans.n, ans.d] } };
  };
  var META_L0 = [['intExpLaw', '整數指數律'], ['logBasic', '常用對數的基本值'], ['quadIneq', '二次不等式'], ['quadVertex', '配方求極值'], ['geoSeq', '等比數列的一般項']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    intExpLaw: { txt: '整數指數律與負指數（高一上第一章 數與式）——本章把指數推廣到分數與實數，規則完全一樣', link: '../g10a-ch01/practice.html#L1' },
    logBasic: { txt: '常用對數 log 的意義（高一上第一章 數與式）——本章的對數律全部從「log 是 10 的幾次方」出發', link: '../g10a-ch01/practice.html#L1' },
    quadIneq: { txt: '二次不等式（高一上第三章 多項式函數）——令 t=2^x 換元之後，解的就是它', link: '../g10a-ch03/practice.html#L1' },
    quadVertex: { txt: '二次函數配方求極值（高一上第三章 多項式函數）——換元後的最大最小值都靠配方', link: '../g10a-ch03/practice.html#L1' },
    geoSeq: { txt: '等比數列（高一下第一章 數列與級數）——複利、半衰期、每期成長 k 倍都是等比數列', link: '../g10b-ch01/practice.html#L1' }
  };

  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  var CONTRAST = {
    'L1.expLaw': { f: function (p) { return p.s[0] < 0; }, why: '除以 $a^{s}$ 是指數「減 $s$」：$s$ 是負數時，減負等於加——最常錯的就是這個負號。' },
    'L1.radicalVal': { f: function (p) { return p.m < 0; }, why: '指數的正負只決定「要不要取倒數」：先當成正的算出來，負指數再整個翻到分母。' },
    'L1.expOrder': { f: function (p) { return p.base[1] > 1; }, why: '底數大於 $1$：指數大的數就大；底數介於 $0$ 與 $1$：指數大的數反而小。先看底數，再比指數。' },
    'L1.expEqSame': { f: function (p) { return p.k; }, why: '右邊的底是 $a^k$：化同底時整個指數要乘 $k$（括號別忘了），$k$ 不同，解就不同。' },
    'L1.expIneqSame': { f: function (p) { return p.up; }, why: '同底比指數：底數大於 $1$ 不等號方向不變，底數介於 $0$ 與 $1$ 方向要反過來。' },
    'L1.expShift': { f: function (p) { return p.h > 0; }, keep: ['k'], why: '向右平移 $h$ 是把 $x$ 換成 $x-h$、向左是 $x+h$；漸近線只跟上下平移有關，左右怎麼移都不變。' },
    'L1.expQuadEq': { f: function (p) { return p.form; }, why: '$4^x$ 與 $2^{2x}$ 是同一個東西，都是 $(2^x)^2$：看穿這一點，兩題都是 $t$ 的二次方程式。' },
    'L1.growthTimes': { f: function (p) { return p.type; }, why: '同一個模型 $N\\cdot k^{t/T}$：一題給時間求倍數，一題給倍數反求時間——先數「過了幾期」。' },
    'L1.logDef': { f: function (p) { return p.m < 0; }, why: '真數小於 $1$ 時對數是負的：$\\log_a\\frac1{a^n}=-n$。先把真數寫成底數的次方，指數就是答案。' },
    'L1.logLaw': { f: function (p) { return p.t; }, why: '加 → 真數相乘、減 → 真數相除、前面的係數 → 真數的次方：三條運算律各管一種式子。' },
    'L1.logExpress': { f: function (p) { return p.k > 0; }, why: '真數有因數 $5$ 時要用 $\\log5=1-\\log2=1-a$ 換掉；只有 $2$ 與 $3$ 時直接拆開就好。' },
    'L1.digits': { f: function (p) { return p.a; }, keep: ['n'], why: '同樣的指數、不同的底：$\\log a^n=n\\log a$，位數由「首數 $+1$」決定，底數大一點位數就差很多。' },
    'L1.charMant': { f: function (p) { return p.type; }, why: '$\\log$ 是正的：整數部分的位數 $=$ 首數 $+1$；$\\log$ 是負的：要先寫成「負整數 $+$ 正的尾數」，才看得出小數點後第幾位。' },
    'L1.logIneqSimple': { f: function (p) { return p.up; }, why: '底數大於 $1$ 方向不變、介於 $0$ 與 $1$ 方向相反；不管哪一種，都別忘了真數要大於 $0$。' },
    'L1.logShift': { f: function (p) { return p.t === 0; }, why: '平移是把 $x$ 換成 $x-h$、整個式子再加 $k$；對稱則是把 $x$ 換成 $-x$（對 $y$ 軸）或整個式子變號（對 $x$ 軸）。' },
    'L1.logDomain': { f: function (p) { return p.type; }, why: '真數含 $x$：只要真數 $\\gt0$；連底數也含 $x$：還要再加上底數 $\\gt0$ 且 $\\ne1$ 兩個條件。' },
    'L1.logScale': { f: function (p) { return p.type; }, why: '對數刻度的共同讀法：刻度「相差」多少，原來的量就「相乘」多少倍——差變倍數。' },
    'L2.expSymmMin': { f: function (p) { return p.ans[2] === 2 * p.ans[3]; }, why: '$t=a^x+a^{-x}\\ge2$：頂點落在 $t\\ge2$ 時最小值在頂點；頂點落在 $t\\lt2$ 時取不到，最小值發生在 $t=2$。' },
    'L2.expIneqQuad': { f: function (p) { return p.strict; }, why: '兩題只差等號：$\\lt$ 的解不含端點、$\\le$ 的解含端點；換元解出 $t$ 的範圍後，端點跟著帶回來。' },
    'L2.expIntervalMax': { f: function (p) { return p.a[1] > 1; }, why: '底數大於 $1$：指數最大時函數值最大；底數介於 $0$ 與 $1$：指數最大時函數值反而最小。' },
    'L2.halfLife': { f: function (p) { return p.type; }, why: '剩下 $\\left(\\frac12\\right)^n$ 就是過了 $n$ 個半衰期：一題由半衰期求時間，一題由時間反求半衰期。' },
    'L2.compoundYears': { f: function (p) { return p.k; }, why: '同一條式子 $n\\gt\\dfrac{\\log k}{\\log(1+r)}$：目標倍數 $k$ 越大要越久，成長率 $r$ 越大就越快；情境（人口、存款、細菌）只是換個說法。' },
    'L2.logQuadRange': { f: function (p) { return p.ans[1] === p.l; }, why: '令 $t=\\log_a x$ 後 $t$ 的範圍跟著換；最小值在頂點，最大值在「離頂點較遠」的那個端點——一題在左端、一題在右端。' },
    'L2.logIneqBase': { f: function (p) { return p.up; }, why: '兩邊同底：底數大於 $1$ 真數保持方向，底數小於 $1$ 真數方向相反；兩個真數都要大於 $0$。' },
    'L2.decayRatio': { f: function (p) { return p.TA > p.TB; }, why: '半衰期短的衰變得快、剩得少：題目問的一定是「剩得多的是剩得少的幾倍」，先判斷誰的半衰期長。' },
    'L2.dbMulti': { f: function (p) { return p.type; }, why: '強度變 $n$ 倍 ⟹ 分貝「加」$10\\log n$；分貝差 $d$ ⟹ 強度是 $10^{d/10}$「倍」。一個由倍數求差，一個由差求倍數。' },
    'L3.expSystem': { f: function (p) { return p.v; }, why: '令 $u=a^x$、$v=a^y$ 後第二式都是 $u=a^d\\cdot v$；第一式是差就得 $(a^d-1)v$，是和就得 $(a^d+1)v$。' },
    'L3.expIneqHalf': { f: function (p) { return p.op.indexOf('l') >= 0; }, why: '恆正的因式不影響正負，只要看 $t-k$：小於 $0$ 得 $x$ 小於 $\\log_a k$，大於 $0$ 得 $x$ 大於 $\\log_a k$。' },
    'L3.expRangeSum': { f: function (p) { return p.c - 1 >= p.l && p.c - 1 <= p.r; }, why: '頂點 $t=2^{c-1}$ 在 $t$ 的範圍內，最小值在頂點；不在範圍內，最大最小都在端點。' },
    'L3.vertGap': { f: function (p) { return p.fam; }, why: '平移量是整數時 $t$ 的係數是整數；平移量是 $\\frac12$ 的奇數倍時係數帶 $\\sqrt{\\ }$，解出的 $t$ 也帶根號，$h$ 就是分數。' },
    'L3.digitsAB': { f: function (p) { return (p.m + p.k) % 2; }, why: '兩式相加、相減後要除以 $2$：範圍的端點是整數還是半整數，決定位數只有一種還是兩種可能。' },
    'L3.logProductRoots': { f: function (p) { return p.b === 10; }, why: '不管底數是多少，令 $s=\\log_b x$ 後兩根之和都是 $-\\log_b(pq)$，所以 $\\alpha\\beta=\\dfrac{1}{pq}$——答案與底數、右邊的常數無關。' },
    'L3.logShiftMatch': { f: function (p) { return p.dv > 0; }, why: '上下平移 $k$ 併進真數：向上是乘 $a^{k}$、向下是除以 $a^{k}$，所以 $A$ 一個是分數、一個是整數。' },
    'L3.logQuadInterval': { f: function (p) { return p.v; }, keep: ['a'], why: '底數大於 $1$ 時外層的 $\\log$ 遞增：最小值在二次式的頂點，最大值在離頂點較遠的端點。' },
    'L3.logReflectShiftMeet': { f: function (p) { return p.k > 0; }, why: '向上平移 $k$ 是把真數乘 $a^{k}$、向下是除以 $a^{k}$：令真數相等時，係數一個大於 $1$、一個小於 $1$。' }
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, lg: lg, lead: lead, LG: LG } };
}));
