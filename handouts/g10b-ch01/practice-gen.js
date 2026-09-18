/* ══════════════════════════════════════════════════════════════
   g10b-ch01 數列與級數・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示                         p：參數與結構化答案（給 verify_gen10b1.py 獨立重算）
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
  function fr2(f) { return [f.n, f.d]; }
  function T(s) { return '$' + s + '$'; }
  function term(coef, v, first) {          /* 整數係數 × 變數字串 */
    if (coef === 0) return '';
    var sgn = coef < 0 ? '-' : (first ? '' : '+');
    var ab = Math.abs(coef);
    return sgn + (ab === 1 && v ? '' : ab) + v;
  }
  function termF(f, v, first) {             /* 分數係數 × 變數字串 */
    if (f.n === 0) return '';
    var sgn = f.n < 0 ? '-' : (first ? '' : '+'), ab = F(Math.abs(f.n), f.d);
    return sgn + (Fr.eq(ab, F(1)) && v ? '' : Fr.tex(ab, true)) + v;
  }
  function lin(a, b, v) {                    /* a v + b，v 預設 n */
    v = v || 'n'; var s = term(a, v, true) + term(b, '', false); return s === '' ? '0' : s;
  }
  function quad(a, b, c, v) { v = v || 'n'; var s = term(a, v + '^2', true) + term(b, v, s === '' ? true : false); s = term(a, v + '^2', true); s += term(b, v, s === ''); s += term(c, '', s === ''); return s === '' ? '0' : s; }
  function pw(base, e) { return base + '^{' + e + '}'; }
  function sq(s) { return '\\langle ' + s + '\\rangle'; }
  function ipow(b, e) { var v = 1; for (var i = 0; i < e; i++) v *= b; return v; }
  function fpow(f, e) { var v = F(1); for (var i = 0; i < e; i++) v = Fr.mul(v, f); return v; }
  var SUM = function (lo, hi, f) { var s = 0; for (var k = lo; k <= hi; k++) s += f(k); return s; };
  var SUMF = function (lo, hi, f) { var s = F(0); for (var k = lo; k <= hi; k++) s = Fr.add(s, f(k)); return s; };
  function sigma(lo, hi, body) { return '\\displaystyle\\sum_{k=' + lo + '}^{' + hi + '}' + body; }
  function signedNum(x) { return x < 0 ? '(' + x + ')' : String(x); }   /* 放在乘號後面的數 */
  var AN = 'a_n', AN1 = 'a_{n+1}', ANM = 'a_{n-1}';

  /* ────────── 提示專用：把本題的數字代進式子 ────────── */
  function hpz(x) { return x < 0 ? '(' + x + ')' : String(x); }                /* 負數代入時加括號 */
  function hinv(x) { return x === 1 ? '1' : '\\dfrac1{' + x + '}'; }             /* 1/x，x=1 時不寫分數 */
  function hlin(co, x, cst) { return (co === 1 ? String(x) : co + '\\times' + x) + term(cst, '', false); }  /* 把 n=x 代進 co·n+cst */
  function hpar(s) { return /^\d*[a-z]$/.test(s) ? s : '(' + s + ')'; }          /* 單項不加括號：n(2n-1) 不是 (n)(2n-1) */
  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* 1-1 等差：由兩項決定整個數列 */
  L1.arTerm = function (r) {
    var p = r.int(2, 6), q = p + r.int(3, 8), d = r.nz(-5, 6), a1 = r.int(-10, 15), m = r.int(15, 40);
    var ap = a1 + (p - 1) * d, aq = a1 + (q - 1) * d, am = a1 + (m - 1) * d;
    return { q: '設 ' + T(sq(AN)) + ' 為等差數列，已知 ' + T('a_{' + p + '}=' + ap) + '、' + T('a_{' + q + '}=' + aq) + '。求公差 ' + T('d') + '、首項 ' + T('a_1') + '、一般項 ' + T(AN) + ' 與 ' + T('a_{' + m + '}') + '。',
             a: T('d=' + d) + '、' + T('a_1=' + a1) + '、' + T(AN + '=' + lin(d, a1 - d)) + '、' + T('a_{' + m + '}=' + am),
             h: '兩項相減把公差逼出來：$a_{' + q + '}-a_{' + p + '}=' + aq + term(-ap, '', false) + '$，而這個差就是 $' + (q - p) + 'd$；有了 $d$ 再用 $a_1=a_{' + p + '}-' + (p === 2 ? '' : (p - 1)) + 'd$ 回推首項，最後套 $a_n=a_1+(n-1)d$ 並代 $n=' + m + '$。',
             p: { p: p, q: q, ap: ap, aq: aq, m: m, ans: { d: d, a1: a1, am: am } } };
  };

  /* 1-2 等差的變號位置 */
  L1.arSign = function (r) {
    var pos = r() < 0.5, k = r.int(3, 9), a1, d;
    do { a1 = r.int(40, 120); } while (a1 % k === 0);
    if (pos) { d = -k; } else { a1 = -a1; d = k; }
    var n = Math.floor(Math.abs(a1) / k) + 1;            /* a_n 是最後一個同號項 */
    var an = a1 + (n - 1) * d, nx = a1 + n * d;
    var qtxt = pos ? '最後一個正的項是第幾項？其值為何？' : '第一個正的項是第幾項？其值為何？';
    var ansN = pos ? n : n + 1, ansV = pos ? an : nx;
    return { q: '等差數列 ' + T(sq(AN)) + ' 中 ' + T('a_1=' + a1) + '、公差 ' + T('d=' + d) + '。' + qtxt,
             a: '第 ' + T(String(ansN)) + ' 項，' + T('a_{' + ansN + '}=' + ansV),
             h: '先寫 $a_n=' + lin(d, a1 - d) + '$，解不等式 $a_n' + (pos ? '\\gt' : '\\gt') + '0$，注意 $n$ 要取整數。',
             p: { a1: a1, d: d, pos: pos, ans: { n: ansN, v: ansV } } };
  };

  /* 1-3 三數成等差：對稱設法 */
  L1.arMiddle = function (r) {
    var m = r.int(3, 12), d = r.int(1, Math.min(4, m - 1)), sgn = r() < 0.75 ? 1 : -1;
    var x = [sgn * (m - d), sgn * m, sgn * (m + d)]; x.sort(function (u, v) { return u - v; });
    var S = x[0] + x[1] + x[2], useSq = r() < 0.5;
    var other = useSq ? x[0] * x[0] + x[1] * x[1] + x[2] * x[2] : x[0] * x[1] * x[2];
    return { q: '三個數成等差數列，其和為 ' + T(String(S)) + '、' + (useSq ? '平方和' : '乘積') + '為 ' + T(String(other)) + '，求此三數。',
             a: T(x.join(',\\ ')) + '（或逆序）',
             h: '設三數為 $m-d,\\ m,\\ m+d$：由和得 $m=' + (S / 3) + '$，再代入' + (useSq ? '平方和' : '乘積') + '解 $d^2$。',
             p: { S: S, other: other, useSq: useSq, ans: x } };
  };

  /* 1-4 等比：由兩項求公比 */
  L1.gpTerm = function (r) {
    var a1 = r.pick([1, 2, 3, 5]) * r.sign(), rr = r.pick([2, 3, -2, -3]), p = r.int(2, 4), q = p + 3, m = q + r.int(1, 3);
    var ap = a1 * ipow(rr, p - 1), aq = a1 * ipow(rr, q - 1), am = a1 * ipow(rr, m - 1);
    return { q: '設 ' + T(sq(AN)) + ' 為等比數列，' + T('a_{' + p + '}=' + ap) + '、' + T('a_{' + q + '}=' + aq) + '。求公比 ' + T('r') + '、首項 ' + T('a_1') + ' 與 ' + T('a_{' + m + '}') + '。',
             a: T('r=' + rr) + '、' + T('a_1=' + a1) + '、' + T('a_{' + m + '}=' + am),
             h: '兩項相除：$a_{' + q + '}\\div a_{' + p + '}=' + aq + '\\div ' + hpz(ap) + '=r^{3}$，立方根唯一（不會有正負兩解）；求出 $r$ 後用 $a_1=a_{' + p + '}\\div ' + (p === 2 ? 'r' : 'r^{' + (p - 1) + '}') + '$，最後 $a_{' + m + '}=a_1r^{' + (m - 1) + '}$。',
             p: { p: p, q: q, ap: ap, aq: aq, m: m, ans: { r: rr, a1: a1, am: am } } };
  };

  /* 1-5 三數成等比：乘法版對稱設法 */
  L1.gpMiddle = function (r) {
    var rho = r.pick([2, 3, 4, 5, 6]), k = r.int(1, 6), a = rho * k * (r() < 0.75 ? 1 : -1), kind = r.int(0, 1);
    var x = [a / rho, a, a * rho]; x.sort(function (u, v) { return u - v; });
    var P = x[0] * x[1] * x[2], S = x[0] + x[1] + x[2], E = x[0] + x[2];
    return { q: '三個數成等比數列，其乘積為 ' + T(String(P)) + '、' + (kind === 0 ? '和' : '頭尾兩數之和') + '為 ' + T(String(kind === 0 ? S : E)) + '，求此三數。',
             a: T(x.join(',\\ ')) + '（或逆序）',
             h: '設三數為 $\\dfrac ar,\\ a,\\ ar$：乘積 $=a^3=' + P + '$ 先定出中間項 $a$；再由' + (kind === 0 ? '和 $a\\left(\\dfrac1r+1+r\\right)=' + S + '$' : '頭尾之和 $a\\left(\\dfrac1r+r\\right)=' + E + '$') + ' 解出 $r+\\dfrac1r$，$r$ 與 $\\dfrac1r$ 兩個根給的是同一組數（只是順序相反）。',
             p: { P: P, S: S, E: E, kind: kind, ans: x } };
  };

  /* 1-6 平均成長率（幾何平均） */
  var GPAIR = [      /* [r, a, b]：(1+a%)(1+b%) = (1+r%)^2，平均成長率恰為 r% */
    [0, -60, 150], [0, -50, 100], [0, -20, 25], [10, -56, 175], [10, -50, 142],
    [10, -45, 120], [20, -52, 200], [20, -50, 188], [20, -40, 140], [20, -36, 125],
    [20, -28, 100], [20, -25, 92], [20, -20, 80], [20, -10, 60], [20, -4, 50],
    [30, -35, 160], [40, -30, 180], [40, -20, 145], [40, -2, 100], [40, 12, 75],
    [50, -25, 200], [50, -10, 150], [50, 25, 80]
  ];
  L1.growth = function (r) {
    var g = r.pick(GPAIR), ans = g[0], aa = g[1], bb = g[2], kind = r.int(0, 3);
    if (ans === 0) kind = kind % 2;                 /* 平均成長率 0% 時不再多插一年 0%（(1+0) 不好看） */
    var rates = kind === 0 ? [aa, bb] : kind === 1 ? [bb, aa] : kind === 2 ? [aa, bb, ans] : [ans, aa, bb];
    var txt = rates.map(function (x) { return '$' + x + '\\%$'; }).join('、');
    var prod = rates.map(function (x) { return '\\left(1' + (x < 0 ? '-' : '+') + Math.abs(x) / 100 + '\\right)'; }).join('');
    return { q: '某公司連續 ' + T(String(rates.length)) + ' 年的營收成長率依序為 ' + txt + '。若這 ' + T(String(rates.length)) + ' 年的平均成長率為 ' + T('r\\%') + '，求 ' + T('r') + '。',
             a: T('r=' + ans),
             h: '「平均成長率」是幾何平均，不是把成長率平均：$\\left(1+\\dfrac{r}{100}\\right)^{' + rates.length + '}=' + prod + '$。右邊先乘出來，再開 $' + rates.length + '$ 次方。',
             p: { rates: rates, kind: kind, ans: ans } };
  };

  /* 1-7 一階線性遞迴：不動點法 */
  L1.recurLinear = function (r) {
    var pp = r.pick([2, 3, -2, 4, -3]), qq = r.nz(-6, 6), a1 = r.int(-3, 6), k = r.int(4, 6);
    var xs = F(qq, 1 - pp), c = Fr.sub(F(a1), xs);
    if (c.n === 0) a1 += 1, c = Fr.sub(F(a1), xs);
    var ak = Fr.add(Fr.mul(c, F(ipow(pp, k - 1))), xs);
    var pwT = signedNum(pp), gen = '';
    for (var tt = 0; tt <= 4 && gen === ''; tt++) {   /* c=±p^t 就把係數併進指數：-2·2^{n-1} 寫成 -2^{n} */
      var pt = ipow(pp, tt), ex = tt === 0 ? 'n-1' : (tt === 1 ? 'n' : 'n+' + (tt - 1));
      if (c.d === 1 && c.n === pt) gen = pwT + '^{\\,' + ex + '}';
      else if (c.d === 1 && c.n === -pt) gen = '-' + pwT + '^{\\,' + ex + '}';
    }
    if (gen === '') gen = termF(c, '\\cdot' + pwT + '^{\\,n-1}', true);
    gen += termF(xs, '', false);
    return { q: '設數列 ' + T(sq(AN)) + ' 滿足 ' + T('a_1=' + a1) + '、' + T(AN1 + '=' + term(pp, 'a_n', true) + term(qq, '', false)) + '。求一般項 ' + T(AN) + ' 與 ' + T('a_{' + k + '}') + '。',
             a: T(AN + '=' + gen) + '，' + T('a_{' + k + '}=' + Fr.tex(ak)),
             h: '不動點 $x^\\ast=' + Fr.tex(xs) + '$（解 $x=' + term(pp, 'x', true) + term(qq, '', false) + '$）；$\\langle a_n-x^\\ast\\rangle$ 是公比 $' + pp + '$ 的等比數列。',
             p: { p: pp, q: qq, a1: a1, k: k, ans: { c: fr2(c), x: fr2(xs), ak: fr2(ak) } } };
  };

  /* 1-8 連加型遞迴（疊縮相加） */
  L1.recurSum = function (r) {
    var al = r.pick([2, 4, 6, 1, 3]), be = r.int(-4, 5), a1 = r.int(-3, 6), m = r.int(8, 20);
    /* a_n = a1 + Σ_{k=1}^{n-1}(al k + be) = (al/2) n^2 + (be - al/2) n + (a1 - be) */
    var c2 = F(al, 2), c1 = F(2 * be - al, 2), c0 = F(a1 - be);
    var am = a1 + SUM(1, m - 1, function (k) { return al * k + be; });
    var gen = termF(c2, 'n^2', true) + termF(c1, 'n', false) + termF(c0, '', false);
    return { q: '設 ' + T('a_1=' + a1) + '，且對所有正整數 ' + T('n') + ' 滿足 ' + T(AN1 + '=a_n+' + (be < 0 || al === 0 ? '(' + lin(al, be) + ')' : lin(al, be))) + '。求一般項 ' + T(AN) + ' 與 ' + T('a_{' + m + '}') + '。',
             a: T(AN + '=' + gen) + '，' + T('a_{' + m + '}=' + am),
             h: '$a_n=a_1+\\sum_{k=1}^{n-1}(' + lin(al, be, 'k') + ')$，用 $\\sum k=\\frac{(n-1)n}2$ 與 $\\sum 1=n-1$。',
             p: { al: al, be: be, a1: a1, m: m, ans: { c2: fr2(c2), c1: fr2(c1), c0: fr2(c0), am: am } } };
  };

  /* 1-9 連乘型遞迴（疊縮相乘） */
  L1.recurProd = function (r) {
    var kind = r.int(0, 3), m = r.int(6, 12), a1 = r.pick([1, 2, 3, 6]);
    var ratio = ['\\dfrac{n+1}{n}', '\\dfrac{n+2}{n}', '\\dfrac{n}{n+1}', '\\dfrac{n}{n+2}'][kind];
    var genTex = [a1 === 1 ? 'n' : a1 + 'n', a1 % 2 === 0 ? (a1 / 2 === 1 ? 'n(n+1)' : (a1 / 2) + 'n(n+1)') : '\\dfrac{' + (a1 === 1 ? '' : a1) + 'n(n+1)}{2}', a1 === 1 ? '\\dfrac1n' : '\\dfrac{' + a1 + '}{n}', '\\dfrac{' + (2 * a1) + '}{n(n+1)}'][kind];
    var am = [F(a1 * m), F(a1 * m * (m + 1), 2), F(a1, m), F(2 * a1, m * (m + 1))][kind];
    var rat = function (n) { return [F(n + 1, n), F(n + 2, n), F(n, n + 1), F(n, n + 2)][kind]; };
    return { q: '設 ' + T('a_1=' + a1) + '，且 ' + T(AN1 + '=' + ratio + '\\,a_n') + '（' + T('n\\ge1') + '）。求一般項 ' + T(AN) + ' 與 ' + T('a_{' + m + '}') + '。',
             a: T(AN + '=' + genTex) + '，' + T('a_{' + m + '}=' + Fr.tex(am)),
             h: '連乘：$a_n=a_1\\cdot\\dfrac{a_2}{a_1}\\cdot\\dfrac{a_3}{a_2}\\cdots\\dfrac{a_n}{a_{n-1}}$。本題每一格是 $' + ratio + '$，代 $n=1,2,3,\\dots$ 依序是 $' + Fr.tex(rat(1)) + ',\\ ' + Fr.tex(rat(2)) + ',\\ ' + Fr.tex(rat(3)) + ',\\dots$，分子分母交錯相消只留頭尾；最後乘上 $a_1=' + a1 + '$，再代 $n=' + m + '$。',
             p: { kind: kind, a1: a1, m: m, ans: fr2(am) } };
  };

  /* 1-10 分式型遞迴：取倒數 */
  L1.recurRecip = function (r) {
    var s = r.int(1, 3), k = r.int(1, 4), m = r.int(10, 100);
    /* a1 = 1/s, a_{n+1} = a_n/(k a_n + 1) ⟹ 1/a_n = s + k(n-1) */
    var a2 = F(1, s + k), a3 = F(1, s + 2 * k), am = F(1, s + k * (m - 1));
    return { q: '設 ' + T('a_1=' + Fr.tex(F(1, s))) + '、' + T(AN1 + '=\\dfrac{a_n}{' + (k === 1 ? '' : k) + 'a_n+1}') + '。(1) 求 ' + T('a_2,a_3') + '。(2) 求一般項 ' + T(AN) + '。(3) 求 ' + T('a_{' + m + '}') + '。',
             a: '(1) ' + T(Fr.tex(a2) + ',\\ ' + Fr.tex(a3)) + '　(2) ' + T(AN + '=\\dfrac{1}{' + lin(k, s - k) + '}') + '　(3) ' + T(Fr.tex(am)),
             h: '兩邊取倒數：$\\dfrac1{a_{n+1}}=\\dfrac{' + (k === 1 ? '' : k) + 'a_n+1}{a_n}=\\dfrac1{a_n}+' + k + '$。本題 $\\dfrac1{a_1}=' + s + '$，所以 $\\left\\langle\\dfrac1{a_n}\\right\\rangle$ 是首項 $' + s + '$、公差 $' + k + '$ 的等差數列；先寫出 $\\dfrac1{a_n}$ 再倒回去，第 (3) 小題代 $n=' + m + '$。',
             p: { s: s, k: k, m: m, ans: { a2: fr2(a2), a3: fr2(a3), am: fr2(am) } } };
  };

  /* 1-11 週期數列 */
  L1.periodic = function (r) {
    var kind = r.int(0, 2), a1 = r.pick([2, 3, 4, 5, -2, -3]), N = r.pick([100, 101, 200, 2025, 2026]);
    var rule = ['\\dfrac{1}{1-a_n}', '1-\\dfrac{1}{a_n}', '\\dfrac{a_n-1}{a_n+1}'][kind];
    var sub = ['\\dfrac{1}{1-' + hpz(a1) + '}', '1-\\dfrac{1}{' + hpz(a1) + '}', '\\dfrac{' + hpz(a1) + '-1}{' + hpz(a1) + '+1}'][kind];
    var step = function (x) { return kind === 0 ? Fr.div(F(1), Fr.sub(F(1), x)) : kind === 1 ? Fr.sub(F(1), Fr.div(F(1), x)) : Fr.div(Fr.sub(x, F(1)), Fr.add(x, F(1))); };
    var seq = [F(a1)]; for (var i = 0; i < 5; i++) seq.push(step(seq[i]));
    var per = Fr.eq(seq[3], seq[0]) ? 3 : 4;
    var cyc = seq.slice(0, per), cs = SUMF(0, per - 1, function (i) { return cyc[i]; });
    var aN = cyc[(N - 1) % per], full = Math.floor(N / per), rem = N % per;
    var SN = Fr.add(Fr.mul(F(full), cs), SUMF(0, rem - 1, function (i) { return cyc[i]; }));
    return { q: '設 ' + T('a_1=' + a1) + '、' + T(AN1 + '=' + rule) + '。(1) 求 ' + T('a_2,a_3,a_4') + ' 並說明此數列的週期。(2) 求 ' + T('a_{' + N + '}') + '。(3) 求 ' + T('a_1+a_2+\\cdots+a_{' + N + '}') + '。',
             a: '(1) ' + T(Fr.tex(seq[1]) + ',\\ ' + Fr.tex(seq[2]) + ',\\ ' + Fr.tex(seq[3])) + '，週期 ' + T(String(per)) + '　(2) ' + T(Fr.tex(aN)) + '　(3) ' + T(Fr.tex(SN)),
             h: '先把 $a_1=' + a1 + '$ 代進遞迴式：$a_2=' + sub + '$，再一路算下去，算到某一項與 $a_1$ 相同就找到週期。' + (rem === 0 ? '本題 $' + N + '=' + per + '\\times' + full + '$ 整除，剛好是 $' + full + '$ 個完整週期，零頭 $0$ 項。' : '本題 $' + N + '=' + per + '\\times' + full + '+' + rem + '$，用「$' + full + '$ 個完整週期＋零頭 $' + rem + '$ 項」。'),
             p: { kind: kind, a1: a1, N: N, ans: { per: per, aN: fr2(aN), SN: fr2(SN) } } };
  };

  /* 2-1 Σ 的基本計算 */
  L1.sigmaCalc = function (r) {
    var N = r.int(8, 20), al = r.int(0, 3), be = r.nz(-4, 5), ga = r.int(-5, 5);
    if (al === 0 && be === 0) be = 2;
    var body = '(' + quad(al, be, ga, 'k') + ')';
    var val = SUM(1, N, function (k) { return al * k * k + be * k + ga; });
    return { q: '計算 ' + T(sigma(1, N, body)) + '。',
             a: T(String(val)),
             h: '拆成 $' + (al ? (al === 1 ? '' : al) + '\\sum k^2' : '') + (al && be ? (be > 0 ? '+' : '') : '') + (be ? (Math.abs(be) === 1 ? (be < 0 ? '-' : '') : be) + '\\sum k' : '') + (ga ? (ga > 0 ? '+' : '-') + (Math.abs(ga) === 1 ? '' : Math.abs(ga) + '\\cdot') + N : '') + '$，套 $\\sum k=\\frac{n(n+1)}2$、$\\sum k^2=\\frac{n(n+1)(2n+1)}6$。',
             p: { N: N, al: al, be: be, ga: ga, ans: val } };
  };

  /* 2-2 Σ 公式：以 n 表示 */
  L1.sigmaFormula = function (r) {
    var a = r.int(1, 6), b = r.nz(-6, 6);
    /* Σ k(ak+b) = n(n+1)(2an + a + 3b)/6 */
    var c3 = F(2 * a, 6), c2 = F(3 * a + 3 * b, 6), c1 = F(a + 3 * b, 6);
    var g = gcd(gcd(2 * a, Math.abs(a + 3 * b)), 6);
    var innerR = lin(2 * a / g, (a + 3 * b) / g), den = 6 / g;
    var tex = den === 1 ? 'n(n+1)(' + innerR + ')' : '\\dfrac{n(n+1)(' + innerR + ')}{' + den + '}';
    if ((a + 3 * b) === 0) tex = (2 * a / g === 1 ? '' : (2 * a / g)) + (den === 1 ? 'n^2(n+1)' : '\\dfrac{n^2(n+1)}{' + den + '}');
    return { q: '求 ' + T(sigma(1, 'n', 'k(' + lin(a, b, 'k') + ')')) + '（以 ' + T('n') + ' 表示，化到最簡）。',
             a: T(tex),
             h: '先乘開：$\\displaystyle\\sum k(' + lin(a, b, 'k') + ')=' + (a === 1 ? '' : a) + '\\sum k^2' + (b > 0 ? '+' : '-') + (Math.abs(b) === 1 ? '' : Math.abs(b)) + '\\sum k$，套 $\\sum k^2=\\dfrac{n(n+1)(2n+1)}{6}$、$\\sum k=\\dfrac{n(n+1)}{2}$，再提出公因式 $\\dfrac{n(n+1)}{6}$。代 $n=1$ 驗算：左式 $=' + (a + b) + '$。',
             p: { a: a, b: b, ans: { c3: fr2(c3), c2: fr2(c2), c1: fr2(c1) } } };
  };

  /* 2-3 等差級數：S_N 與中段和 */
  L1.arSum = function (r) {
    var a1 = r.int(-15, 20), d = r.nz(-6, 8), p = r.int(2, 5), q = p + r.int(3, 7), N = r.int(15, 30), lo = r.int(6, 10), hi = lo + r.int(5, 12);
    var ap = a1 + (p - 1) * d, aq = a1 + (q - 1) * d;
    var SN = SUM(1, N, function (k) { return a1 + (k - 1) * d; }), mid = SUM(lo, hi, function (k) { return a1 + (k - 1) * d; });
    return { q: '等差數列 ' + T(sq(AN)) + ' 中 ' + T('a_{' + p + '}=' + ap) + '、' + T('a_{' + q + '}=' + aq) + '。(1) 求 ' + T('S_{' + N + '}=a_1+a_2+\\cdots+a_{' + N + '}') + '。(2) 求 ' + T('a_{' + lo + '}+a_{' + (lo + 1) + '}+\\cdots+a_{' + hi + '}') + '。',
             a: '(1) ' + T('S_{' + N + '}=' + SN) + '　(2) ' + T(String(mid)),
             h: '先求 $d=' + d + '$、$a_1=' + a1 + '$；(2) 用「項數 $\\times$（首＋末）$\\div2$」或 $S_{' + hi + '}-S_{' + (lo - 1) + '}$。',
             p: { p: p, q: q, ap: ap, aq: aq, N: N, lo: lo, hi: hi, ans: { SN: SN, mid: mid } } };
  };

  /* 2-4 S_n 何時最大 */
  L1.arSumMax = function (r) {
    var k = r.int(3, 9), a1; do { a1 = r.int(30, 100); } while (a1 % k === 0);
    var d = -k, n = Math.floor(a1 / k) + 1, Smax = SUM(1, n, function (i) { return a1 + (i - 1) * d; });
    return { q: '等差數列 ' + T(sq(AN)) + ' 中 ' + T('a_1=' + a1) + '、' + T('d=' + d) + '。求使 ' + T('S_n') + ' 最大的 ' + T('n') + ' 與該最大值。',
             a: T('n=' + n) + ' 時最大，' + T('S_{' + n + '}=' + Smax),
             h: '$S_n$ 最大 ⟺ 加到最後一個正項為止：$a_n=' + lin(d, a1 - d) + '\\gt0$ ⟹ $n\\lt' + Fr.tex(F(a1 + k, k)) + '$。',
             p: { a1: a1, d: d, ans: { n: n, Smax: Smax } } };
  };

  /* 2-5 等比級數基本題（含負公比與分數公比） */
  L1.gpSum = function (r) {
    var kind = r.int(0, 2), a1, rr, N = r.int(5, 8);
    if (kind === 0) { a1 = r.pick([1, 2, 3, 5]); rr = r.pick([2, 3, -2, -3]); }
    else if (kind === 1) { a1 = r.pick([1, 2, 3, 4]) * r.sign(); rr = F(1, 2); }
    else { a1 = r.pick([8, 16, 32, 64]); rr = F(-1, 2); }
    var rf = typeof rr === 'number' ? F(rr) : rr;
    var S = SUMF(0, N - 1, function (i) { return Fr.mul(F(a1), fpow(rf, i)); });
    var rP = (rf.d !== 1 || rf.n < 0) ? '\\left(' + Fr.tex(rf) + '\\right)' : Fr.tex(rf);
    var rD = rf.n < 0 ? '\\left(' + Fr.tex(rf) + '\\right)' : Fr.tex(rf);
    var body = '1-' + rP + '^{' + N + '}';
    var numer = a1 === 1 ? body : (a1 === -1 ? '-\\left(' + body + '\\right)' : a1 + '\\left(' + body + '\\right)');
    return { q: '等比數列首項 ' + T(String(a1)) + '、公比 ' + T(Fr.tex(rf)) + '，求前 ' + T(String(N)) + ' 項的和 ' + T('S_{' + N + '}') + '。',
             a: T('S_{' + N + '}=' + Fr.tex(S)),
             h: '套 $S_n=\\dfrac{a_1(1-r^{n})}{1-r}$，本題 $a_1=' + a1 + '$、$r=' + Fr.tex(rf) + '$、$n=' + N + '$：$S_{' + N + '}=\\dfrac{' + numer + '}{1-' + rD + '}$' + (rf.n < 0 ? '；公比是負的，$r^{' + N + '}$ 的正負號要看 $' + N + '$ 是奇是偶。' : '。'),
             p: { a1: a1, r: fr2(rf), N: N, ans: fr2(S) } };
  };

  /* 2-6 等比級數的分段和 */
  L1.gpBlocks = function (r) {
    var A = r.pick([3, 5, 6, 10, 12]) * r.pick([1, 2]), t = r.pick([2, 3, 4, 5]), n = r.pick(['n', 5, 10]);
    var B = A * t, S3 = A + B + B * t;
    var nn = n === 'n' ? 'n' : String(n), n2 = n === 'n' ? '2n' : String(2 * n), n3 = n === 'n' ? '3n' : String(3 * n);
    return { q: '設等比數列的前 ' + T(nn) + ' 項和 ' + T('S_{' + nn + '}=' + A) + '、前 ' + T(n2) + ' 項和 ' + T('S_{' + n2 + '}=' + (A + B)) + '。求前 ' + T(n3) + ' 項和 ' + T('S_{' + n3 + '}') + '。',
             a: T('S_{' + n3 + '}=' + S3),
             h: '三段和 $S_{' + nn + '}$、$S_{' + n2 + '}-S_{' + nn + '}$、$S_{' + n3 + '}-S_{' + n2 + '}$ 自己也成等比。本題前兩段是 $' + A + '$ 與 $' + (A + B) + '-' + A + '$，兩者相除就是這個新等比數列的公比 $r^{' + nn + '}$；第三段再乘一次公比，最後把三段加起來才是 $S_{' + n3 + '}$。',
             p: { A: A, S2: A + B, ans: S3 } };
  };

  /* 2-7 裂項相消 */
  L1.telescope = function (r) {
    var a = r.pick([1, 2, 3]), b = r.int(0, 2); if (a + b === 0) b = 1;
    var N = r.int(8, 30);
    var S = SUMF(1, N, function (k) { return F(1, (a * k + b) * (a * k + a + b)); });
    var t = function (k) { return '\\dfrac{1}{' + (a * k + b) + '\\times' + (a * k + a + b) + '}'; };
    var co = a === 1 ? '' : '\\dfrac1{' + a + '}';
    return { q: '求 ' + T(t(1) + '+' + t(2) + '+' + t(3) + '+\\cdots+' + t(N)) + '（化為最簡分數）。',
             a: T(Fr.tex(S)),
             h: '$\\dfrac{1}{(' + lin(a, b, 'k') + ')(' + lin(a, a + b, 'k') + ')}=' + co + '\\left(\\dfrac1{' + lin(a, b, 'k') + '}-\\dfrac1{' + lin(a, a + b, 'k') + '}\\right)$：本題第一項 $' + t(1) + '=' + co + '\\left(' + hinv(a + b) + '-' + hinv(2 * a + b) + '\\right)$，最後一項的兩個分母是 $' + (a * N + b) + '$ 與 $' + (a * N + a + b) + '$，中間全部相消只剩頭尾。',
             p: { a: a, b: b, N: N, ans: fr2(S) } };
  };

  /* 2-8 錯位相減 */
  L1.staggered = function (r) {
    var STG = [[2, 5], [2, 6], [2, 7], [2, 8], [2, 9], [2, 10], [3, 5], [3, 6], [3, 7], [3, 8], [4, 4], [4, 5], [4, 6]];
    var STGC = [[1, 0], [1, 1], [2, -1], [2, 1], [3, -2], [3, -1]];
    var g = r.pick(STG), rr = g[0], N = g[1], cc = r.pick(STGC), c1 = cc[0], c0 = cc[1];
    var f = function (k) { return c1 * k + c0; };
    var S = SUM(1, N, function (k) { return f(k) * ipow(rr, k - 1); });
    var terms = [String(f(1)), f(2) + '\\times' + rr, f(3) + '\\times' + rr + '^2'];
    return { q: '求 ' + T(terms.join('+') + '+\\cdots+' + f(N) + '\\times' + rr + '^{' + (N - 1) + '}') + '（第 ' + T('k') + ' 項是 ' + T(hpar(lin(c1, c0, 'k')) + '\\times' + rr + '^{\\,k-1}') + '）。',
             a: T(String(S)),
             h: '設 $S$ 為所求，兩邊乘 $' + rr + '$ 後錯一位相減：$(1-' + rr + ')S=' + f(1) + '+' + (c1 === 1 ? '' : c1) + '\\left(' + rr + '+' + rr + '^2+\\cdots+' + rr + '^{' + (N - 1) + '}\\right)-' + f(N) + '\\cdot' + rr + '^{' + N + '}$，中間那一串是等比級數。',
             p: { r: rr, N: N, c1: c1, c0: c0, ans: S } };
  };

  /* 2-9 由 S_n 反求 a_n */
  L1.sumToTerm = function (r) {
    var a = r.nz(-3, 4), b = r.nz(-5, 6), c = r() < 0.5 ? 0 : r.nz(-4, 4);
    var Sn = quad(a, b, c), a1 = a + b + c, coef = [2 * a, b - a];
    var Sm1 = term(a, '(n-1)^2', true) + term(b, '(n-1)', false) + term(c, '', false);
    return { q: '已知數列 ' + T(sq(AN)) + ' 的前 ' + T('n') + ' 項和為 ' + T('S_n=' + Sn) + '。求 ' + T('a_1') + '、' + T('a_n') + '（' + T('n\\ge2') + '），並判斷 ' + T(sq(AN)) + ' 是否為等差數列。',
             a: T('a_1=' + a1) + '、' + T('n\\ge2' + '\\text{ 時 }a_n=' + lin(coef[0], coef[1])) + '；' + (c === 0 ? '是等差數列（' + T('a_1') + ' 也符合該式）' : '不是等差數列（' + T('a_1=' + a1) + ' 不符合 ' + T(lin(coef[0], coef[1])) + '，第一項脫隊）'),
             h: '$a_1=S_1$：把 $n=1$ 代進 $S_n$ 就好；$n\\ge2$ 時 $a_n=S_n-S_{n-1}=\\left(' + Sn + '\\right)-\\left(' + Sm1 + '\\right)$，乘開化簡後是 $n$ 的一次式。' + (c === 0 ? '$S_n$ 沒有常數項，第一項會合得起來。' : '$S_n$ 有常數項 $' + c + '$，第一項就會脫隊。'),
             p: { a: a, b: b, c: c, ans: { a1: a1, coef: coef, isAP: c === 0 } } };
  };

  /* 2-10 等差數列的絕對值和 */
  L1.absSum = function (r) {
    var k = r.int(3, 7), a1; do { a1 = -r.int(20, 45); } while (a1 % k === 0);
    var d = k, N = r.int(15, 22), S = SUM(1, N, function (i) { return Math.abs(a1 + (i - 1) * d); });
    return { q: '設等差數列 ' + T(sq(AN)) + ' 中 ' + T('a_1=' + a1) + '、' + T('d=' + d) + '，求 ' + T('|a_1|+|a_2|+\\cdots+|a_{' + N + '}|') + '。',
             a: T(String(S)),
             h: '先找變號位置：$a_n=' + lin(d, a1 - d) + '$；負的那段整段變號，等於「後段和 $-$ 前段和」。',
             p: { a1: a1, d: d, N: N, ans: S } };
  };

  var COMP = [       /* [本金, 年利率%, 年數]：只收「複利本利和與單利本利和都剛好是整數元」的組合 */
    [10000, 1, 2], [20000, 1, 2], [30000, 1, 2], [50000, 1, 2], [80000, 1, 2],
    [100000, 1, 2], [200000, 1, 2], [500000, 1, 2], [1000000, 1, 2], [1000000, 1, 3],
    [10000, 2, 2], [20000, 2, 2], [30000, 2, 2], [50000, 2, 2], [80000, 2, 2],
    [100000, 2, 2], [200000, 2, 2], [500000, 2, 2], [1000000, 2, 2], [500000, 2, 3],
    [1000000, 2, 3], [10000, 3, 2], [20000, 3, 2], [30000, 3, 2], [50000, 3, 2],
    [80000, 3, 2], [100000, 3, 2], [200000, 3, 2], [500000, 3, 2], [1000000, 3, 2],
    [1000000, 3, 3], [10000, 4, 2], [20000, 4, 2], [30000, 4, 2], [50000, 4, 2],
    [80000, 4, 2], [100000, 4, 2], [200000, 4, 2], [500000, 4, 2], [1000000, 4, 2],
    [500000, 4, 3], [1000000, 4, 3], [10000, 5, 2], [20000, 5, 2], [30000, 5, 2],
    [50000, 5, 2], [80000, 5, 2], [100000, 5, 2], [200000, 5, 2], [500000, 5, 2],
    [1000000, 5, 2], [80000, 5, 3], [200000, 5, 3], [1000000, 5, 3], [10000, 6, 2],
    [20000, 6, 2], [30000, 6, 2], [50000, 6, 2], [80000, 6, 2], [100000, 6, 2],
    [200000, 6, 2], [500000, 6, 2], [1000000, 6, 2], [500000, 6, 3], [1000000, 6, 3],
    [10000, 8, 2], [20000, 8, 2], [30000, 8, 2], [50000, 8, 2], [80000, 8, 2],
    [100000, 8, 2], [200000, 8, 2], [500000, 8, 2], [1000000, 8, 2], [500000, 8, 3],
    [1000000, 8, 3], [10000, 10, 2], [20000, 10, 2], [30000, 10, 2], [50000, 10, 2],
    [80000, 10, 2], [100000, 10, 2], [200000, 10, 2], [500000, 10, 2], [1000000, 10, 2],
    [10000, 10, 3], [20000, 10, 3], [30000, 10, 3], [50000, 10, 3], [80000, 10, 3],
    [100000, 10, 3], [200000, 10, 3], [500000, 10, 3], [1000000, 10, 3]
  ];
  /* 2-11 複利與單利 */
  L1.compound = function (r) {
    var g = r.pick(COMP), P = g[0], i = g[1], n = g[2];
    var comp = P; for (var j = 0; j < n; j++) comp = comp * (100 + i) / 100;
    comp = Math.round(comp);
    var simple = P + P * i * n / 100;
    return { q: '將 ' + T(String(P)) + ' 元存入銀行，年利率 ' + T(i + '\\%') + '。(1) 若每年複利一次，' + T(String(n)) + ' 年後的本利和為多少元？(2) 若改用單利，' + T(String(n)) + ' 年後的本利和為多少元？兩者相差多少？',
             a: '(1) ' + T(String(comp)) + ' 元　(2) ' + T(String(simple)) + ' 元，相差 ' + T(String(comp - simple)) + ' 元',
             h: '複利是「本利和再生利息」：$' + P + '\\times\\left(1+' + (i / 100) + '\\right)^{' + n + '}$，也就是連乘 $' + n + '$ 次 $' + ((100 + i) / 100) + '$；單利只有本金生利息：$' + P + '\\times\\left(1+' + (i / 100) + '\\times' + n + '\\right)$。',
             p: { P: P, i: i, n: n, ans: { comp: comp, simple: simple } } };
  };

  /* 3-1 歸納法的遞推步驟：要加的那一項 */
  var IDENT = [
    { id: 0, lhs: '1+3+5+\\cdots+(2n-1)', f: function (k) { return 2 * k - 1; }, fT: '2k+1', g: function (n) { return n * n; }, gT: 'n^2', gk1: '(k+1)^2' },
    { id: 1, lhs: '1+2+3+\\cdots+n', f: function (k) { return k; }, fT: 'k+1', g: function (n) { return n * (n + 1) / 2; }, gT: '\\dfrac{n(n+1)}{2}', gk1: '\\dfrac{(k+1)(k+2)}{2}' },
    { id: 2, lhs: '1^2+2^2+\\cdots+n^2', f: function (k) { return k * k; }, fT: '(k+1)^2', g: function (n) { return n * (n + 1) * (2 * n + 1) / 6; }, gT: '\\dfrac{n(n+1)(2n+1)}{6}', gk1: '\\dfrac{(k+1)(k+2)(2k+3)}{6}' },
    { id: 3, lhs: '1^3+2^3+\\cdots+n^3', f: function (k) { return k * k * k; }, fT: '(k+1)^3', g: function (n) { return n * n * (n + 1) * (n + 1) / 4; }, gT: '\\left[\\dfrac{n(n+1)}{2}\\right]^2', gk1: '\\left[\\dfrac{(k+1)(k+2)}{2}\\right]^2' },
    { id: 4, lhs: '1\\cdot2+2\\cdot3+\\cdots+n(n+1)', f: function (k) { return k * (k + 1); }, fT: '(k+1)(k+2)', g: function (n) { return n * (n + 1) * (n + 2) / 3; }, gT: '\\dfrac{n(n+1)(n+2)}{3}', gk1: '\\dfrac{(k+1)(k+2)(k+3)}{3}' },
    { id: 5, lhs: '\\dfrac{1}{1\\cdot2}+\\dfrac{1}{2\\cdot3}+\\cdots+\\dfrac{1}{n(n+1)}', f: function (k) { return 1 / (k * (k + 1)); }, fT: '\\dfrac{1}{(k+1)(k+2)}', g: function (n) { return n / (n + 1); }, gT: '\\dfrac{n}{n+1}', gk1: '\\dfrac{k+1}{k+2}' },
    { id: 6, lhs: '2+4+6+\\cdots+2n', f: function (k) { return 2 * k; }, fT: '2(k+1)', g: function (n) { return n * (n + 1); }, gT: 'n(n+1)', gk1: '(k+1)(k+2)' },
    { id: 7, lhs: '1+2+2^2+\\cdots+2^{n-1}', f: function (k) { return ipow(2, k - 1); }, fT: '2^{k}', g: function (n) { return ipow(2, n) - 1; }, gT: '2^{n}-1', gk1: '2^{k+1}-1' }
  ];
  L1.inductionStep = function (r) {
    var I = r.pick(IDENT), m = r.int(3, 8);
    var gm = I.g(m), gmF = I.id === 5 ? F(m, m + 1) : F(gm);
    return { q: '要用數學歸納法證明「對所有正整數 ' + T('n') + '，' + T(I.lhs + '=' + I.gT) + '」。(1) 驗證 ' + T('n=' + m) + ' 時等式成立：兩邊的值各為多少？(2) 在遞推步驟中，假設 ' + T('n=k') + ' 時成立，左式要「再加上哪一項」才變成 ' + T('n=k+1') + ' 的左式？此時右式應化簡成什麼？',
             a: '(1) 兩邊皆為 ' + T(Fr.tex(gmF)) + '　(2) 加上 ' + T(I.fT) + '，右式須化成 ' + T(I.gk1),
             h: '(1) 左式從第一項一路加到第 $' + m + '$ 項，右式把 $n=' + m + '$ 代進 $' + I.gT + '$，兩邊各算一次。(2) 遞推步驟的目標永遠是：$\\big(n=k\\text{ 的右式}\\big)+\\big(\\text{第 }k+1\\text{ 項}\\big)=\\big(n=k+1\\text{ 的右式}\\big)$——「第 $k+1$ 項」就是把左式一般項的 $n$ 換成 $k+1$，右式也把 $' + I.gT + '$ 的 $n$ 換成 $k+1$ 再化簡。',
             p: { id: I.id, m: m, ans: { gm: fr2(gmF) } } };
  };

  /* 3-2 歸納法證整除：f(k+1) 用 f(k) 表示 */
  var DIV = [  /* f(n) = a·b^n + c n + d 恆為 m 的倍數（離線窮舉，已排除「每一項都是 m 的倍數」的假題） */
    [1, 4, -9, 8, 3], [1, 4, -6, 5, 3], [1, 4, -3, 2, 3], [1, 4, 0, 2, 3],
    [2, 4, 0, 1, 3], [1, 7, -6, 2, 3], [1, 7, -3, -1, 3], [1, 7, -3, 2, 3],
    [1, 10, -3, -4, 3], [1, 10, -3, -1, 3], [1, 10, -3, 2, 3], [1, 3, -6, 7, 4],
    [1, 3, -2, 3, 4], [1, 3, -2, 7, 4], [1, 3, 2, -1, 4], [1, 5, -8, 7, 4],
    [1, 5, -4, 3, 4], [1, 5, 0, 3, 4], [1, 5, 0, -1, 4], [1, 5, 4, 3, 4],
    [1, 7, -6, 3, 4], [1, 7, -6, 7, 4], [1, 7, -2, -1, 4], [1, 9, -4, -1, 4],
    [1, 9, -4, 3, 4], [1, 9, 0, -5, 4], [1, 6, -10, 9, 5], [1, 6, -5, 4, 5],
    [1, 6, -5, 9, 5], [1, 3, -6, 9, 6], [1, 3, 0, 3, 6], [1, 3, 0, 9, 6],
    [1, 4, -6, 8, 6], [1, 4, 6, -4, 6], [3, 5, -18, 9, 6], [3, 5, -12, 3, 6],
    [3, 5, -6, -3, 6], [1, 7, -6, 5, 6], [1, 7, 0, -1, 6], [1, 7, 0, 5, 6],
    [1, 9, -6, 3, 6], [1, 9, 0, -3, 6], [1, 8, -7, 6, 7], [1, 8, 0, -1, 7],
    [1, 8, 0, 6, 7], [1, 8, 7, -1, 7], [2, 3, -4, 6, 8], [2, 3, 4, -2, 8],
    [2, 3, 4, 6, 8], [1, 5, -4, 7, 8], [1, 5, 4, -1, 8], [1, 5, 4, 7, 8],
    [2, 7, -12, 6, 8], [2, 7, -4, -2, 8], [2, 7, -4, 6, 8], [1, 9, -8, 7, 8],
    [1, 9, 0, -1, 8], [1, 9, 0, 7, 8], [1, 4, -3, 8, 9], [1, 4, 6, -1, 9],
    [1, 4, 6, 8, 9], [1, 4, 15, -1, 9], [1, 7, -6, 8, 9], [1, 7, 3, -1, 9],
    [1, 7, 3, 8, 9], [1, 10, -9, 8, 9], [1, 10, 0, -1, 9], [1, 10, 0, 8, 9],
    [1, 10, 9, -1, 9], [1, 5, 0, 5, 10], [1, 5, 10, -5, 10], [1, 5, 10, 5, 10],
    [1, 6, 0, 4, 10], [1, 6, 10, -6, 10], [1, 6, 10, 4, 10], [1, 3, 6, 3, 12],
    [1, 3, 18, -9, 12], [1, 3, 18, 3, 12], [1, 4, 0, 8, 12], [1, 4, 12, -4, 12],
    [1, 4, 12, 8, 12], [3, 5, -12, 9, 12], [3, 5, 0, -3, 12], [3, 5, 0, 9, 12],
    [1, 7, 6, -1, 12], [1, 7, 18, -1, 12], [2, 7, -12, 10, 12], [1, 9, 0, 3, 12],
    [1, 9, 12, -9, 12]
  ];
  L1.divisible = function (r) {
    var D = r.pick(DIV), a = D[0], b = D[1], c = D[2], d = D[3], m = D[4];
    var fT = (a === 1 ? '' : a + '\\cdot') + b + '^{\\,n}' + term(c, 'n', false) + term(d, '', false);
    var f1 = a * b + c + d;
    /* f(k+1) = b f(k) + c(1-b)k + (c + d(1-b)) ；f(k)=m t */
    var ck = c * (1 - b) / m, c0 = (c + d * (1 - b)) / m;
    var inner = term(b, 't', true) + term(ck, 'k', false) + term(c0, '', false);
    var diff = term(c * (1 - b), 'k', false) + term(c + d * (1 - b), '', false);
    return { q: '已知對所有正整數 ' + T('n') + '，' + T('f(n)=' + fT) + ' 恆為 ' + T(String(m)) + ' 的倍數。(1) 求 ' + T('f(1)') + '。(2) 用歸納法證明時，設 ' + T('f(k)=' + m + 't') + '（' + T('t') + ' 為整數），把 ' + T('f(k+1)') + ' 整理成 ' + T(m + '\\times(\\ \\ \\ )') + '，求括號內的式子（以 ' + T('t,k') + ' 表示）。',
             a: '(1) ' + T('f(1)=' + f1) + '　(2) ' + T(inner),
             h: '(1) 把 $n=1$ 代進 $f(n)$ 即可。(2) 先寫出 $' + b + '\\,f(k)$，再看 $f(k+1)$ 比它多了多少：$f(k+1)=' + b + '\\,f(k)' + diff + '$；把 $f(k)=' + m + 't$ 代進去，整條式子就提得出 $' + m + '$。',
             p: { a: a, b: b, c: c, d: d, m: m, ans: { f1: f1, coef: [b, ck, c0] } } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 2-1 S_m = S_n 的對稱性 */
  L2.arSymm = function (r) {
    var m = r.int(3, 9), n = m + 2 * r.int(2, 6), j = r.int(1, 4), A = j * (m + n - 1), d = -2 * j;
    /* S_m=S_n ⟹ a_{(m+n+1)/2}=0 ⟹ a1 = -d·((m+n+1)/2 - 1) = j(m+n-1) */
    var kmax = (m + n) / 2, zero = (m + n + 1) / 2;
    var Smax = SUM(1, kmax, function (i) { return A + (i - 1) * d; });
    var p = r.int(1, zero - 1), q = m + n + 1 - p;
    return { q: '設等差數列 ' + T(sq(AN)) + ' 的公差 ' + T('d\\lt0') + '，且 ' + T('S_{' + m + '}=S_{' + n + '}') + '。(1) 求 ' + T('a_{' + p + '}+a_{' + q + '}') + ' 與 ' + T('S_{' + (m + n) + '}') + '。(2) 求使 ' + T('S_k') + ' 最大的 ' + T('k') + '。(3) 若又知 ' + T('a_1=' + A) + '，求 ' + T('d') + ' 與 ' + T('S_k') + ' 的最大值。',
             a: '(1) 皆為 ' + T('0') + '　(2) ' + T('k=' + kmax) + '　(3) ' + T('d=' + d) + '，最大值 ' + T(String(Smax)),
             h: '$S_{' + m + '}=S_{' + n + '}$ ⟹ $a_{' + (m + 1) + '}+\\cdots+a_{' + n + '}=0$，這 $' + (n - m) + '$ 項首尾兩兩配對、每一對的和都是 $0$，正中間那一對是 $a_{' + kmax + '}+a_{' + (kmax + 1) + '}=0$（$d\\lt0$ ⟹ $a_{' + kmax + '}\\gt0\\gt a_{' + (kmax + 1) + '}$）；對稱軸在 $' + zero + '$，故 $a_p+a_q=0$ 只要 $p+q=' + (m + n + 1) + '$。',
             p: { m: m, n: n, p: p, q: q, A: A, ans: { kmax: kmax, d: d, Smax: Smax } } };
  };

  /* 2-2 前 n 項和之比 ⟹ 第 k 項之比 */
  L2.sumRatio = function (r) {
    var a = r.int(1, 5), b = r.int(-3, 7), c = r.int(1, 5), d = r.int(-3, 9), k = r.int(4, 15);
    while (a * d === b * c || (d < 0 && (-d) % c === 0)) d += 1;   /* 比值不能是常數；cn+d 不能在某個正整數 n 為 0（否則 T_n=0） */
    var num = a * (2 * k - 1) + b, den = c * (2 * k - 1) + d; if (den <= 0) den = c * (2 * k - 1) + (d = Math.abs(d) + 1);
    var g = gcd(num, den) || 1, n0 = 2 * k - 1;
    return { q: '兩等差數列 ' + T(sq(AN)) + '、' + T(sq('b_n')) + ' 的前 ' + T('n') + ' 項和分別為 ' + T('S_n,T_n') + '，且 ' + T('\\dfrac{S_n}{T_n}=\\dfrac{' + lin(a, b) + '}{' + lin(c, d) + '}') + '。求 ' + T('\\dfrac{a_{' + k + '}}{b_{' + k + '}}') + '。',
             a: T(den / g === 1 ? String(num / g) : '\\dfrac{' + (num / g) + '}{' + (den / g) + '}'),
             h: '$a_k=\\dfrac{S_{2k-1}}{2k-1}$（奇數項的和＝項數 $\\times$ 中間項），所以 $\\dfrac{a_{' + k + '}}{b_{' + k + '}}=\\dfrac{S_{' + n0 + '}}{T_{' + n0 + '}}$：把 $n=' + n0 + '$ 代進題目給的比，得 $\\dfrac{' + hlin(a, n0, b) + '}{' + hlin(c, n0, d) + '}$，算出來再約分。',
             p: { a: a, b: b, c: c, d: d, k: k, ans: [num / g, den / g] } };
  };

  /* 2-3 奇數項和與偶數項和 */
  L2.oddEvenGP = function (r) {
    var rr = r.pick([2, 3, -2, -3]), m = r.int(3, 5), a1 = r.int(1, 5) * r.sign(), N = 2 * m;
    var O = SUM(0, m - 1, function (i) { return a1 * ipow(rr, 2 * i); }), E = O * rr;
    return { q: '一等比數列共有 ' + T(String(N)) + ' 項，其奇數項的和為 ' + T(String(O)) + '、偶數項的和為 ' + T(String(E)) + '。求公比 ' + T('r') + ' 與首項 ' + T('a_1') + '。',
             a: T('r=' + rr) + '、' + T('a_1=' + a1),
             h: '偶數項恰是奇數項各乘 $r$ ⟹ $r=\\dfrac{' + E + '}{' + O + '}$；再把奇數項看成公比 $r^2$、共 $' + m + '$ 項的等比級數解 $a_1$。',
             p: { N: N, O: O, E: E, ans: { r: rr, a1: a1 } } };
  };

  /* 2-4 平方後仍是等比 */
  L2.gpSquares = function (r) {
    var s = r.pick([2, 3, 4]), t = r.pick([1, 4, 9]), p = r.pick([3, 5]), q = p + 4, N = r.int(8, 15);
    var ap2 = t * ipow(s, p - 1), aq2 = t * ipow(s, q - 1);
    var sg = r.sign(), ap = Math.round(Math.sqrt(ap2)) * sg, aq = Math.round(Math.sqrt(aq2)) * sg;   /* a_q/a_p = r^4 > 0，兩項同號 */
    var S = SUM(0, N - 1, function (i) { return t * ipow(s, i); });
    return { q: '已知 ' + T(sq(AN)) + ' 為等比數列，' + T('a_{' + p + '}=' + ap) + '、' + T('a_{' + q + '}=' + aq) + '，求 ' + T('a_1^{\\,2}+a_2^{\\,2}+\\cdots+a_{' + N + '}^{\\,2}') + '。',
             a: T(String(S)),
             h: '$\\langle a_n^{\\,2}\\rangle$ 也是等比，公比 $r^{2}$：$\\dfrac{a_{' + q + '}^{\\,2}}{a_{' + p + '}^{\\,2}}=\\dfrac{' + hpz(aq) + '^{2}}{' + hpz(ap) + '^{2}}=r^{8}$，開四次方就得到 $r^{2}$（全程不必決定 $r$ 的正負）；再用 $a_1^{\\,2}=a_{' + p + '}^{\\,2}\\div (r^{2})^{' + (p - 1) + '}$ 當首項，算 $' + N + '$ 項的等比級數和。',
             p: { p: p, q: q, ap: ap, aq: aq, N: N, ans: S } };
  };

  /* 2-5 S_n 含指數：第一項脫隊 */
  L2.sumFromSn = function (r) {
    var A = r.pick([1, 2, 3]), b = r.pick([2, 3]), C = r() < 0.7 ? r.nz(-4, 4) : 0, m = r.int(4, 7);
    if (A * b + C === 0) C += 1;                 /* 避免 a_1 = 0 */
    if (r() < 0.35) C = -A;                      /* 恰好合得起來的那型 */
    var a1 = A * b + C, am = A * (b - 1) * ipow(b, m - 1), isGP = (a1 === A * (b - 1));
    var Sn = (A === 1 ? '' : A + '\\cdot') + b + '^{\\,n}' + term(C, '', false);
    var gen = ((A * (b - 1)) === 1 ? '' : (A * (b - 1)) + '\\cdot') + b + '^{\\,n-1}';
    var s1 = (A === 1 ? String(b) : A + '\\times' + b) + term(C, '', false);
    return { q: '已知數列 ' + T(sq(AN)) + ' 的前 ' + T('n') + ' 項和為 ' + T('S_n=' + Sn) + '。求 ' + T('a_1') + '、' + T('a_{' + m + '}') + '，並判斷 ' + T(sq(AN)) + ' 是否為等比數列。',
             a: T('a_1=' + a1) + '、' + T('a_{' + m + '}=' + am) + '；' + (isGP ? '是等比數列（' + T('a_n=' + gen) + ' 對所有 ' + T('n') + ' 成立）' : '不是（' + T('n\\ge2') + ' 時 ' + T('a_n=' + gen) + '，但 ' + T('a_1=' + a1 + '\\ne' + (A * (b - 1))) + '）'),
             h: '$a_n=S_n-S_{n-1}$ 只對 $n\\ge2$ 成立，$a_1=S_1=' + s1 + '$ 要另外算；$a_{' + m + '}$ 用 $n\\ge2$ 的那一條。$S_n=A\\cdot b^{\\,n}+C$ 型只有 $C=-A$ 時第一項才合得起來；這裡 $A=' + A + '$、$C=' + C + '$，' + (isGP ? '恰好 $C=-A$，第一項合得起來。' : '$C\\ne-A$，第一項脫隊。'),
             p: { A: A, b: b, C: C, m: m, ans: { a1: a1, am: am, isGP: isGP } } };
  };

  /* 2-6 由 a1+2a2+…+n an 反求單項 */
  L2.weightedRecur = function (r) {
    var p = r.int(-2, 6), q = r.nz(-4, 5), m = r.int(5, 10);
    var Tn = quad(1, p, q), a1 = 1 + p + q;
    var am = F(2 * m - 1 + p, m), a2 = F(3 + p, 2);
    return { q: '已知數列 ' + T(sq(AN)) + ' 對所有正整數 ' + T('n') + ' 滿足 ' + T('a_1+2a_2+3a_3+\\cdots+na_n=' + Tn) + '。求 ' + T('a_1') + '、' + T('a_2') + ' 與 ' + T('a_{' + m + '}') + '。',
             a: T('a_1=' + a1) + '、' + T('a_2=' + Fr.tex(a2)) + '、' + T('a_{' + m + '}=' + Fr.tex(am)),
             h: '令 $T_n=' + Tn + '$，則 $n\\ge2$ 時 $na_n=T_n-T_{n-1}=' + lin(2, p - 1) + '$；$a_1=T_1$ 要單獨算。',
             p: { p: p, q: q, m: m, ans: { a1: a1, a2: fr2(a2), am: fr2(am) } } };
  };

  /* 2-7 等差 × 等差的級數 */
  L2.prodAP = function (r) {
    var al = r.int(1, 3), be = r.int(-3, 4), ga = r.nz(-3, 3), de = r.int(-4, 5), N = r.int(10, 25);
    var c = function (k) { return al * k + be; }, d = function (k) { return ga * k + de; };
    var S = SUM(1, N, function (k) { return c(k) * d(k); });
    var show = function (f) { return [1, 2, 3, 4].map(f).join(',') + ',\\dots'; };
    return { q: '已知兩等差數列 ' + T(sq('c_n') + ':' + show(c)) + ' 與 ' + T(sq('d_n') + ':' + show(d)) + '，求 ' + T('c_1d_1+c_2d_2+\\cdots+c_{' + N + '}d_{' + N + '}') + '。',
             a: T(String(S)),
             h: '$c_nd_n=' + hpar(lin(al, be)) + hpar(lin(ga, de)) + '$ 是 $n$ 的二次式，乘開後套 $\\sum n^2,\\sum n,\\sum1$；不要用錯位相減（那是給等差 $\\times$ 等比用的）。',
             p: { al: al, be: be, ga: ga, de: de, N: N, ans: S } };
  };

  /* 2-8 二次數列的絕對值和 */
  L2.absQuad = function (r) {
    var al = r.int(1, 5), be = al + r.int(3, 8), N = r.int(be + 4, be + 10);
    var b = -(al + be), c = al * be;
    var S = SUM(1, N, function (n) { return Math.abs(n * n + b * n + c); });
    return { q: '設數列 ' + T(sq(AN)) + ' 的一般項為 ' + T('a_n=' + quad(1, b, c)) + '，求 ' + T('|a_1|+|a_2|+\\cdots+|a_{' + N + '}|') + '。',
             a: T(String(S)),
             h: '因式分解 $a_n=(n-' + al + ')(n-' + be + ')$：$' + (al + 1) + '\\le n\\le' + (be - 1) + '$ 時為負，其餘非負；$\\sum|a_n|=\\sum a_n-2\\sum_{\\text{負段}}a_n$。',
             p: { al: al, be: be, N: N, ans: S } };
  };

  /* 2-9 高斯符號分群求和 */
  L2.floorSum = function (r) {
    var m = r.pick([3, 4, 5, 6, 7]), N = r.int(50, 100);
    var S = SUM(1, N, function (k) { return Math.floor(k / m); });
    var v = Math.floor(N / m), last = N - m * v + 1;
    return { q: '將等差數列 ' + T('\\dfrac1{' + m + '},\\dfrac2{' + m + '},\\dfrac3{' + m + '},\\dots,\\dfrac{' + N + '}{' + m + '}') + ' 的每一項用無條件捨去法取到整數，依序排成 ' + T(sq('b_n')) + '，求 ' + T('b_1+b_2+\\cdots+b_{' + N + '}') + '。',
             a: T(String(S)),
             h: '$b_k=\\left\\lfloor\\dfrac k{' + m + '}\\right\\rfloor$ 每 $' + m + '$ 個一群：$k=1\\sim' + (m - 1) + '$ 這幾項是 $0$（不影響總和），值 $1$ 有 $' + m + '$ 個、值 $2$ 有 $' + m + '$ 個……' + (last === m ? '最後一群（值 $' + v + '$）剛好也是 $' + m + '$ 個。' : '最後一群（值 $' + v + '$）只有 $' + last + '$ 個。'),
             p: { m: m, N: N, ans: S } };
  };

  /* 2-10 分群數列 */
  L2.groupSeq = function (r) {
    var kind = r.int(0, 1), N = r.int(50, 120), K = 1; while (K * (K + 1) / 2 < N) K++;
    var pos = N - (K - 1) * K / 2;               /* 第 K 群的第 pos 項 */
    if (kind === 0) {
      var S = SUM(1, K - 1, function (k) { return k * k; }) + pos * K;
      return { q: '有一規則數列 ' + T('1,\\ 2,2,\\ 3,3,3,\\ 4,4,4,4,\\ \\dots') + '（' + T('k') + ' 個 ' + T('k') + '）。(1) 求第 ' + T(String(N)) + ' 項。(2) 求前 ' + T(String(N)) + ' 項的和。',
               a: '(1) ' + T(String(K)) + '　(2) ' + T(String(S)),
               h: '前 $k$ 群共 $\\dfrac{k(k+1)}2$ 項；$\\dfrac{' + (K - 1) + '\\cdot' + K + '}2=' + ((K - 1) * K / 2) + '\\lt' + N + '\\le' + (K * (K + 1) / 2) + '$ ⟹ 第 $' + N + '$ 項在第 $' + K + '$ 群。和 $=\\sum_{k=1}^{' + (K - 1) + '}k^2+' + pos + '\\times' + K + '$。',
               p: { kind: 0, N: N, ans: { term: K, S: S } } };
    }
    var num = K + 1 - pos, den = pos;
    return { q: '將分數依「分子與分母之和」由小到大排列，和相同時再依分母由小到大：' + T('\\dfrac11,\\ \\dfrac21,\\dfrac12,\\ \\dfrac31,\\dfrac22,\\dfrac13,\\ \\dfrac41,\\dfrac32,\\dfrac23,\\dfrac14,\\ \\dots') + '（不約分）。求第 ' + T(String(N)) + ' 項。',
             a: T('\\dfrac{' + num + '}{' + den + '}'),
             h: '第 $k$ 群（分子＋分母 $=k+1$）有 $k$ 項；前 $' + (K - 1) + '$ 群共 $' + ((K - 1) * K / 2) + '$ 項，故第 $' + N + '$ 項是第 $' + K + '$ 群的第 $' + pos + '$ 項，分母為 $' + pos + '$。',
             p: { kind: 1, N: N, ans: [num, den] } };
  };

  /* 2-11 等差 ÷ 等比：k/2^k */
  L2.kOver2k = function (r) {
    var KOV = [[1, 0], [1, 1], [2, -1], [2, 1], [3, -2], [3, -1]];
    var cc = r.pick(KOV), c1 = cc[0], c0 = cc[1], base = r.pick([2, 2, 3]), N = base === 2 ? r.int(5, 12) : r.int(4, 8);
    var S = SUMF(1, N, function (k) { return F(c1 * k + c0, ipow(base, k)); });
    var body = '\\dfrac{' + lin(c1, c0, 'k') + '}{' + base + '^{k}}';
    var pk = function (k) { return '\\dfrac{' + (c1 * k + c0) + '}{' + base + (k === 1 ? '' : '^{' + k + '}') + '}'; };
    return { q: '求 ' + T(sigma(1, N, body)) + '（化為最簡分數）。',
             a: T(Fr.tex(S)),
             h: '分子是等差、分母是等比 ⟹ 等差 $\\times$ 等比（公比 $\\dfrac1{' + base + '}$），用錯位相減：設 $S=' + pk(1) + '+' + pk(2) + '+' + pk(3) + '+\\cdots+' + pk(N) + '$，兩邊乘 $\\dfrac1{' + base + '}$ 後錯一位相減，中間會變成一串等比級數。',
             p: { c1: c1, c0: c0, base: base, N: N, ans: fr2(S) } };
  };

  /* 2-12 裂項反求項數 */
  L2.telescopeN = function (r) {
    var kind = r.int(0, 1), n = r.int(20, 1200);
    var val = kind === 0 ? F(n, 2 * n + 1) : F(n, n + 1);
    var lhs = kind === 0 ? '\\dfrac13+\\dfrac1{15}+\\dfrac1{35}+\\cdots+\\dfrac1{(2n-1)(2n+1)}' : '\\dfrac1{1\\cdot2}+\\dfrac1{2\\cdot3}+\\dfrac1{3\\cdot4}+\\cdots+\\dfrac1{n(n+1)}';
    var split = kind === 0 ? '\\dfrac12\\left(\\dfrac1{2k-1}-\\dfrac1{2k+1}\\right)' : '\\dfrac1k-\\dfrac1{k+1}';
    var closed = kind === 0 ? '\\dfrac{n}{2n+1}' : '\\dfrac{n}{n+1}';
    return { q: '已知 ' + T(lhs + '=' + Fr.tex(val)) + '，求正整數 ' + T('n') + '。',
             a: T('n=' + n),
             h: '第 $k$ 項裂成 $' + split + '$，中間相消後總和是 $' + closed + '$；本題要解的就是 $' + closed + '=' + Fr.tex(val) + '$，右邊已經是最簡分數，交叉相乘即可。',
             p: { kind: kind, val: fr2(val), ans: n } };
  };

  /* 2-13 混合型遞迴：a_{n+1} = p a_n + q^n */
  L2.recurMixed = function (r) {
    var p = r.pick([2, 3]), q = r.pick([2, 3, 4, 5]); if (q === p) q = p + 1;
    var a1 = r.int(1, 6), m = r.int(4, 6);
    var a = [a1]; for (var i = 1; i < m; i++) a.push(p * a[i - 1] + ipow(q, i));
    /* a_n = (a1 - q/(q-p)) p^{n-1} + q^n/(q-p) */
    var c = Fr.sub(F(a1), F(q, q - p)), e = F(1, q - p);
    var cf = function (f, pwTex, first) {        /* 係數 0 ⟹ 整項不寫；±1 ⟹ 不寫「1·」 */
      if (f.n === 0) return '';
      var sgn = f.n < 0 ? '-' : (first ? '' : '+'), ab = F(Math.abs(f.n), f.d);
      return sgn + (Fr.eq(ab, F(1)) ? '' : Fr.tex(ab, true) + '\\cdot') + pwTex;
    };
    var g1 = cf(c, p + '^{\\,n-1}', true), gen = g1 + cf(e, q + '^{\\,n}', g1 === '');
    return { q: '設 ' + T('a_1=' + a1) + '，且 ' + T(AN1 + '=' + p + 'a_n+' + q + '^{\\,n}') + '。(1) 求 ' + T('a_2,a_3') + '。(2) 求 ' + T('a_{' + m + '}') + '。(3) 求一般項 ' + T(AN) + '。',
             a: '(1) ' + T(a[1] + ',\\ ' + a[2]) + '　(2) ' + T(String(a[m - 1])) + '　(3) ' + T(AN + '=' + gen),
             h: '(1)(2) 直接往下代：$a_2=' + p + '\\times' + a1 + '+' + q + '$、$a_3=' + p + 'a_2+' + q + '^{2}$，一路推到 $a_{' + m + '}$。(3) 兩邊除以 $' + q + '^{\\,n+1}$，令 $b_n=\\dfrac{a_n}{' + q + '^{\\,n}}$ 得 $b_{n+1}=\\dfrac{' + p + '}{' + q + '}b_n+\\dfrac1{' + q + '}$，回到一階線性遞迴（不動點 $' + Fr.tex(F(1, q - p)) + '$）。',
             p: { p: p, q: q, a1: a1, m: m, ans: { a2: a[1], a3: a[2], am: a[m - 1], c: fr2(c), e: fr2(e) } } };
  };

  /* 2-14 零存整付（年金） */
  L2.annuity = function (r) {
    var D = r.pick([10000, 20000, 50000]), i = r.pick([2, 3, 5]), n = r.pick([4, 5, 6]), begin = r() < 0.5;
    var DEC = 6, UNIT = 100;                                        /* 近似值給 6 位小數，答案取到百元（不做假精確） */
    var g = Math.round(Math.pow((100 + i) / 100, n) * ipow(10, DEC)) / ipow(10, DEC);
    var val = D * (Math.pow((100 + i) / 100, n) - 1) / (i / 100) * (begin ? (100 + i) / 100 : 1);   /* 用精確值算，再取到百元 */
    var ans = Math.round(val / UNIT) * UNIT;
    return { q: '某人自今年起每年 ' + (begin ? '1 月 1 日' : '12 月 31 日') + ' 存入銀行 ' + T(String(D)) + ' 元，年利率 ' + T(i + '\\%') + '、每年複利一次。連續存 ' + T(String(n)) + ' 年，求第 ' + T(String(n)) + ' 年 12 月 31 日結算時的本利和（四捨五入取到百元；已知 ' + T('(' + ((100 + i) / 100) + ')^{' + n + '}\\approx' + g) + '）。',
             a: '約 ' + T(String(ans)) + ' 元',
             h: (begin ? '各筆分別滾 $' + n + ',' + (n - 1) + ',\\dots,1$ 年' : '各筆分別滾 $' + (n - 1) + ',' + (n - 2) + ',\\dots,0$ 年') + '，本利和是公比 $' + ((100 + i) / 100) + '$ 的等比級數：$' + D + '\\cdot\\dfrac{' + (begin ? ((100 + i) / 100) + '\\left[' : '\\left[') + ((100 + i) / 100) + '^{' + n + '}-1\\right]}{' + (i / 100) + '}$；算完再四捨五入到百元。',
             p: { D: D, i: i, n: n, begin: begin, g: g, unit: UNIT, dec: DEC, ans: ans } };
  };

  /* 2-15 由 S_n 與 a_n 的關係求一般項 */
  L2.snRecur = function (r) {
    var SNR = [[-1, 2, 1, 2], [-2, 3, 2, 3], [-3, 4, 3, 4], [-4, 5, 4, 5], [2, 1, 2, 1], [3, 2, 3, 2], [4, 3, 4, 3], [5, 4, 5, 4]];
    /* [α, D, 公比分子, 公比分母]：S_n = α·a_n + β ⟹ a_1 = β/(1-α)、公比 = α/(α-1)；取 β=±c 使 a_1 = c/D 為正整數 */
    var g = r.pick(SNR), al = g[0], D = g[1], j = r.int(1, 10), c = D * j;
    var a1 = F(j), ratio = F(g[2], g[3]);
    var rel = al < 0 ? 'S_n=' + c + term(al, 'a_n', false) : 'S_n=' + term(al, 'a_n', true) + '-' + c;
    var eq1 = al < 0 ? 'a_1=' + c + term(al, 'a_1', false) : 'a_1=' + term(al, 'a_1', true) + '-' + c;
    var alT = al === -1 ? '-' : String(al);
    var a2 = Fr.mul(a1, ratio), a3 = Fr.mul(a2, ratio);
    var gen = (Fr.eq(a1, F(1)) ? '' : Fr.tex(a1) + '\\cdot') + (ratio.d === 1 ? ratio.n + '^{\\,n-1}' : '\\left(' + Fr.tex(ratio) + '\\right)^{n-1}');
    return { q: '設數列 ' + T(sq(AN)) + ' 的前 ' + T('n') + ' 項和為 ' + T('S_n') + '，且對所有正整數 ' + T('n') + '，' + T(rel) + ' 恆成立。求 ' + T('a_1,a_2,a_3') + ' 與一般項 ' + T(AN) + '。',
             a: T('a_1=' + Fr.tex(a1) + ',\\ a_2=' + Fr.tex(a2) + ',\\ a_3=' + Fr.tex(a3)) + '，' + T(AN + '=' + gen),
             h: '$n=1$ 時 $S_1=a_1$，代進關係式得 $' + eq1 + '$，先解出 $a_1$；$n\\ge2$ 時把 $n$ 與 $n-1$ 兩式相減，因為 $a_n=S_n-S_{n-1}$，會得到 $a_n=' + alT + '(a_n-a_{n-1})$，整理成 $a_n$ 與 $a_{n-1}$ 的定比——那就是公比。',
             p: { al: al, c: c, j: j, ans: { a1: fr2(a1), ratio: fr2(ratio), a3: fr2(a3) } } };
  };

  /* 2-16 等比取對數變等差（跨章：對數） */
  L2.logGP = function (r) {
    var u = r.int(1, 2), v = r.pick([1, 2, 3]), N = r.int(5, 12), half = r() < 0.4;
    var vv = half ? F(2 * v + 1, 2) : F(v);      /* 公比 3^{vv} */
    var rTex = ['', '3', '9', '27'][v] + (half ? '\\sqrt3' : '');
    var a1Tex = u === 1 ? '3' : '9';
    var S = Fr.add(F(N * u), Fr.mul(vv, F(N * (N - 1), 2)));
    var dT = Fr.tex(vv, true);
    return { q: '設 ' + T('a_1,a_2,\\dots,a_{' + N + '}') + ' 是首項為 ' + T(a1Tex) + '、公比為 ' + T(rTex) + ' 的等比數列，求 ' + T('\\log_3a_1+\\log_3a_2+\\cdots+\\log_3a_{' + N + '}') + '。',
             a: T(Fr.tex(S)),
             h: '等比取 $\\log$ 變等差：$\\log_3a_k=\\log_3' + a1Tex + '+(k-1)\\log_3' + rTex + '=' + u + '+' + (Fr.eq(vv, F(1)) ? '(k-1)' : dT + '(k-1)') + '$，是首項 $' + u + '$、公差 $' + dT + '$ 的等差數列，共 $' + N + '$ 項；再套等差級數 $S_n=\\dfrac{n(a_1+a_n)}{2}$。',
             p: { u: u, v: fr2(vv), N: N, ans: fr2(S) } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p（與 o.a）重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     用法：用 splice 腳本插在 META（var META = {）之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     ══════════════════════════════════════════════════════════ */
  function fF(t) { return F(t[0], t[1]); }                        /* p 裡的 [n,d] 還原成分數 */
  function parT(s) { return '\\left(' + s + '\\right)'; }
  function mseg(s) { var out = [], re = /\$([^$]*)\$/g, m; while ((m = re.exec(s))) out.push(m[1]); return out; }
  function aft(s) { var i = s.indexOf('='); return i < 0 ? s : s.slice(i + 1); }
  function sumT(vals) {                                           /* [12,-5,7] → '12-5+7'（0 略過，第一項不帶 +） */
    var s = '';
    for (var i = 0; i < vals.length; i++) s += term(vals[i], '', s === '');
    return s === '' ? '0' : s;
  }
  function addF(f) { return f.n === 0 ? '' : (f.n < 0 ? '-' : '+') + Fr.tex(F(Math.abs(f.n), f.d)); }   /* 分數當加項 */
  function parF(f) { return f.n < 0 ? parT(Fr.tex(f)) : Fr.tex(f); }                                   /* 負分數放在乘號後要加括號 */
  function cdotT(f, v) {                                          /* 分數係數 × v：係數 ±1 時不寫「1·」 */
    var ab = F(Math.abs(f.n), f.d);
    return (f.n < 0 ? '-' : '') + (Fr.eq(ab, F(1)) ? '' : Fr.tex(ab, true) + '\\cdot') + v;
  }
  function fin(o) { return '答案：' + o.a + '。'; }

  var L1_H1 = {
    arTerm: '這是「由兩項定等差數列」：先把兩項相減，公差就跑出來了，再回推首項，最後才寫一般項。',
    arSign: '這是「等差的變號位置」：先寫出一般項，再解一個一次不等式；除以負數要換方向，而且 $n$ 只能取整數。',
    arMiddle: '這是「三數成等差」：把三數設成 $m-d,\\ m,\\ m+d$，和的條件會直接把中間項解出來。',
    gpTerm: '這是「由兩項定等比數列」：兩項相除就得到公比的某次方，指數是奇數時開方的結果唯一。',
    gpMiddle: '這是「三數成等比」：把三數設成 $\\dfrac ar,\\ a,\\ ar$，乘積會直接把中間項解出來。',
    growth: '這是「平均成長率」：成長率要先各自加 $1$ 變成倍率再取幾何平均，不能把百分比直接平均。',
    recurLinear: '這是「一階線性遞迴」：先解不動點，把整個數列平移成等比數列，再寫一般項。',
    recurSum: '這是「連加型遞迴」：把每一步的差全部累加起來（疊縮相加），再套 $\\sum k$ 的公式。',
    recurProd: '這是「連乘型遞迴」：把每一步的比值連乘起來（疊縮相乘），分子分母會交錯相消。',
    recurRecip: '這是「分式型遞迴」：兩邊取倒數，倒數所成的數列就變成等差數列。',
    periodic: '這是「週期數列」：先逐項算到某一項回到首項，找出週期，再用「幾個完整週期＋零頭」去湊。',
    sigmaCalc: '這是「$\\sum$ 的計算」：先把一般項拆成 $k^2$、$k$、常數三塊，再各自套公式。',
    sigmaFormula: '這是「$\\sum$ 化成 $n$ 的式子」：乘開後拆成 $\\sum k^2$ 與 $\\sum k$，最後一定要提公因式化到最簡。',
    arSum: '這是「等差級數」：先把公差與首項解出來，中段和用「項數 $\\times$（首＋末）$\\div2$」。',
    arSumMax: '這是「$S_n$ 何時最大」：加到最後一個正項為止最大，所以先解 $a_n\\gt0$。',
    gpSum: '這是「等比級數求和」：直接套 $S_n=\\dfrac{a_1(1-r^{n})}{1-r}$，公比是負數時要小心次方的正負號。',
    gpBlocks: '這是「等比級數的分段和」：等長的每一段和自己也成等比，公比是原公比的那麼多次方。',
    telescope: '這是「裂項相消」：先把一項拆成兩個分數的差，加起來中間會整串消掉，只剩頭尾。',
    staggered: '這是「錯位相減」：兩邊乘公比後錯一位相減，中間就變成一串等比級數。',
    sumToTerm: '這是「由 $S_n$ 反求 $a_n$」：$n\\ge2$ 時用 $S_n-S_{n-1}$，第一項一定要另外用 $S_1$ 檢查。',
    absSum: '這是「等差的絕對值和」：先找出變號的位置，負的那一段整段變號再相加。',
    compound: '這是「複利與單利」：複利是逐年連乘，單利是逐年連加，先把兩個式子分開寫出來。',
    inductionStep: '這是「歸納法的遞推步驟」：把 $n=k+1$ 代進等式兩邊，看左式要多加哪一項、右式該長成什麼樣。',
    divisible: '這是「歸納法證整除」：先把 $f(k+1)$ 用 $f(k)$ 表示，再把假設代進去提出公因數。'
  };

  var L1_SOL = {};

  /* 1-1 等差：由兩項定數列 */
  L1_SOL.arTerm = function (p, o) {
    var d = p.ans.d, a1 = p.ans.a1, am = p.ans.am, k = p.q - p.p;
    var diff = p.ap === 0 ? String(p.aq) : p.aq + term(-p.ap, '', false) + '=' + (p.aq - p.ap);
    return ['兩項相減，首項會消掉，只剩公差：$a_{' + p.q + '}-a_{' + p.p + '}=' + diff + '$，而它等於 $' + k + 'd$，所以 $d=' + (p.aq - p.ap) + '\\div ' + k + '=' + d + '$。',
      '回推首項：$a_1=a_{' + p.p + '}-' + (p.p === 2 ? '' : (p.p - 1)) + 'd=' + p.ap + term(-(p.p - 1) * d, '', false) + '=' + a1 + '$。',
      '一般項 $a_n=a_1+(n-1)d=' + lin(d, a1 - d) + '$；代 $n=' + p.m + '$ 得 $a_{' + p.m + '}=' + a1 + term((p.m - 1) * d, '', false) + '=' + am + '$。' + fin(o)];
  };

  /* 1-2 等差的變號位置 */
  L1_SOL.arSign = function (p, o) {
    var n = p.ans.n, v = p.ans.v, gen = lin(p.d, p.a1 - p.d), bd = F(p.a1 - p.d, -p.d);
    return ['先寫一般項：$a_n=a_1+(n-1)d=' + p.a1 + term(p.d, '(n-1)', false) + '=' + gen + '$。',
      '解 $a_n\\gt 0$：$' + gen + '\\gt 0$ ⟹ $' + term(p.d, 'n', true) + '\\gt ' + (p.d - p.a1) + '$ ⟹ $n\\' + (p.d < 0 ? 'lt' : 'gt') + ' ' + Fr.tex(bd) + '$' + (p.d < 0 ? '（兩邊除以負數，不等號要換方向）' : '') + '。',
      '$n$ 只能取正整數，' + (p.pos ? '所以最後一個正的項是第 $' + n + '$ 項' : '所以第一個正的項是第 $' + n + '$ 項') + '：$a_{' + n + '}=' + p.a1 + term((n - 1) * p.d, '', false) + '=' + v + '$。' + fin(o)];
  };

  /* 1-3 三數成等差：對稱設法 */
  L1_SOL.arMiddle = function (p, o) {
    var x = p.ans, m = x[1], dd = x[1] - x[0];
    return ['三個數成等差就設成 $m-d,\\ m,\\ m+d$——這樣相加時 $d$ 會自己消掉：和 $=3m=' + p.S + '$，所以中間項 $m=' + m + '$。',
      (p.useSq ? '再用平方和：$(m-d)^2+m^2+(m+d)^2=3m^2+2d^2$，代 $m=' + m + '$ 得 $3\\times' + hpz(m) + '^2+2d^2=' + p.other + '$'
               : '再用乘積：$(m-d)\\cdot m\\cdot(m+d)=m(m^2-d^2)$，代 $m=' + m + '$ 得 $' + hpz(m) + parT(hpz(m) + '^2-d^2') + '=' + p.other + '$')
        + '，解得 $d^2=' + (dd * dd) + '$、$d=\\pm' + dd + '$。',
      '取 $d=' + dd + '$，三數依序是 $' + x.join(',\\ ') + '$；取 $d=-' + dd + '$ 只是把順序反過來，是同一組數。' + fin(o)];
  };

  /* 1-4 等比：由兩項求公比 */
  L1_SOL.gpTerm = function (p, o) {
    var r = p.ans.r, a1 = p.ans.a1, am = p.ans.am, k = p.q - p.p;
    return ['兩項相除，首項會消掉：$\\dfrac{a_{' + p.q + '}}{a_{' + p.p + '}}=r^{' + k + '}=' + p.aq + '\\div ' + hpz(p.ap) + '=' + (p.aq / p.ap) + '$。',
      '$' + k + '$ 是奇數，實數的' + k + '次方根唯一（不會有正負兩解）：$r=' + r + '$；回推首項 $a_1=a_{' + p.p + '}\\div ' + (p.p === 2 ? 'r' : 'r^{' + (p.p - 1) + '}') + '=' + p.ap + '\\div ' + hpz(ipow(r, p.p - 1)) + '=' + a1 + '$。',
      '最後 $a_{' + p.m + '}=a_1r^{' + (p.m - 1) + '}=' + hpz(a1) + '\\times ' + hpz(ipow(r, p.m - 1)) + '=' + am + '$。' + fin(o)];
  };

  /* 1-5 三數成等比：對稱設法 */
  L1_SOL.gpMiddle = function (p, o) {
    var x = p.ans, a = x[1], rho = x[2] / x[1], V = p.kind === 0 ? p.S : p.E;
    var q0 = F(V, a), cc = p.kind === 0 ? Fr.sub(q0, F(1)) : q0;
    return ['三個數成等比就設成 $\\dfrac ar,\\ a,\\ ar$——這樣相乘時 $r$ 會自己消掉：乘積 $=\\dfrac ar\\cdot a\\cdot ar=a^3=' + p.P + '$，所以中間項 $a=' + a + '$。',
      '再用' + (p.kind === 0 ? '和：$a\\left(\\dfrac1r+1+r\\right)=' + V + '$' : '頭尾之和：$a\\left(\\dfrac1r+r\\right)=' + V + '$') + '，兩邊除以 $a=' + a + '$ 得 $' + (p.kind === 0 ? '\\dfrac1r+1+r' : '\\dfrac1r+r') + '=' + Fr.tex(q0) + '$，也就是 $r+\\dfrac1r=' + Fr.tex(cc) + '$，解得 $r=' + rho + '$ 或 $r=\\dfrac1{' + rho + '}$。',
      '兩個 $r$ 給的是同一組數（只是順序相反）：$' + x.join(',\\ ') + '$。' + fin(o)];
  };

  /* 1-6 平均成長率 */
  L1_SOL.growth = function (p, o) {
    var n = p.rates.length, ans = p.ans;
    var pf = function (x) { return F(100 + x, 100); };
    var prod = F(1); for (var i = 0; i < n; i++) prod = Fr.mul(prod, pf(p.rates[i]));
    return ['成長率不能直接平均，要先各自加 $1$ 變成「倍率」：' + p.rates.map(function (x) { return '$1' + (x < 0 ? '-' : '+') + Math.abs(x) / 100 + '=' + Fr.tex(pf(x)) + '$'; }).join('、') + '。',
      '$' + n + '$ 年的總倍率是這些倍率連乘：$' + p.rates.map(function (x) { return Fr.tex(pf(x)); }).join('\\times') + '=' + Fr.tex(prod) + '$。',
      '平均成長率 $r\\%$ 要讓「每年都乘同一個倍率」得到同樣的總倍率：$\\left(1+\\dfrac{r}{100}\\right)^{' + n + '}=' + Fr.tex(prod) + '$，開 $' + n + '$ 次方得 $1+\\dfrac{r}{100}=' + Fr.tex(pf(ans)) + '$，所以 $r=' + ans + '$。' + fin(o)];
  };

  /* 1-7 一階線性遞迴：不動點法 */
  L1_SOL.recurLinear = function (p, o) {
    var xs = fF(p.ans.x), c = fF(p.ans.c), ak = fF(p.ans.ak), gen = aft(mseg(o.a)[0]);
    return ['先解不動點：令 $x=' + term(p.p, 'x', true) + term(p.q, '', false) + '$，得 $' + term(1 - p.p, 'x', true) + '=' + p.q + '$、$x^\\ast=' + Fr.tex(xs) + '$。',
      '把遞迴式減掉不動點：$a_{n+1}-x^\\ast=' + p.p + '(a_n-x^\\ast)$，所以 $\\langle a_n-x^\\ast\\rangle$ 是等比數列，首項 $a_1-x^\\ast=' + p.a1 + addF(Fr.sub(F(0), xs)) + '=' + Fr.tex(c) + '$、公比 $' + p.p + '$。',
      '於是 $a_n-x^\\ast=' + cdotT(c, signedNum(p.p) + '^{\\,n-1}') + '$，移項得 $a_n=' + gen + '$。',
      '代 $n=' + p.k + '$：$a_{' + p.k + '}=' + Fr.tex(ak) + '$。' + fin(o)];
  };

  /* 1-8 連加型遞迴（疊縮相加） */
  L1_SOL.recurSum = function (p, o) {
    var gen = aft(mseg(o.a)[0]), am = p.ans.am;
    return ['把每一步的差疊起來：$a_n=a_1+(a_2-a_1)+(a_3-a_2)+\\cdots+(a_n-a_{n-1})=a_1+\\displaystyle\\sum_{k=1}^{n-1}(' + lin(p.al, p.be, 'k') + ')$。',
      '套 $\\displaystyle\\sum_{k=1}^{n-1}k=\\dfrac{(n-1)n}{2}$、$\\displaystyle\\sum_{k=1}^{n-1}1=n-1$：$a_n=' + p.a1 + '+' + (p.al === 1 ? '' : p.al + '\\cdot') + '\\dfrac{(n-1)n}{2}' + term(p.be, '(n-1)', false) + '$。',
      '乘開合併同類項：$a_n=' + gen + '$；代 $n=' + p.m + '$ 得 $a_{' + p.m + '}=' + am + '$。' + fin(o)];
  };

  /* 1-9 連乘型遞迴（疊縮相乘） */
  L1_SOL.recurProd = function (p, o) {
    var NUM = ['2\\cdot3\\cdot4\\cdots n', '3\\cdot4\\cdot5\\cdots(n+1)', '1\\cdot2\\cdot3\\cdots(n-1)', '1\\cdot2\\cdot3\\cdots(n-1)'];
    var DEN = ['1\\cdot2\\cdot3\\cdots(n-1)', '1\\cdot2\\cdot3\\cdots(n-1)', '2\\cdot3\\cdot4\\cdots n', '3\\cdot4\\cdot5\\cdots(n+1)'];
    var LEFT = ['n', '\\dfrac{n(n+1)}{2}', '\\dfrac1n', '\\dfrac{2}{n(n+1)}'];
    var gen = aft(mseg(o.a)[0]), am = fF(p.ans);
    return ['把每一步的比值疊起來：$a_n=a_1\\cdot\\dfrac{a_2}{a_1}\\cdot\\dfrac{a_3}{a_2}\\cdots\\dfrac{a_n}{a_{n-1}}$，每一格就是題目給的比。',
      '把 $n=1,2,\\dots,n-1$ 依序代進去連乘：$\\dfrac{a_n}{a_1}=\\dfrac{' + NUM[p.kind] + '}{' + DEN[p.kind] + '}=' + LEFT[p.kind] + '$（分子分母交錯相消，只留頭尾）。',
      '乘回 $a_1=' + p.a1 + '$：$a_n=' + gen + '$；代 $n=' + p.m + '$ 得 $a_{' + p.m + '}=' + Fr.tex(am) + '$。' + fin(o)];
  };

  /* 1-10 分式型遞迴：取倒數 */
  L1_SOL.recurRecip = function (p, o) {
    var s = p.s, k = p.k, m = p.m;
    return ['兩邊取倒數：$\\dfrac1{a_{n+1}}=\\dfrac{' + (k === 1 ? '' : k) + 'a_n+1}{a_n}=\\dfrac1{a_n}+' + k + '$，所以 $\\left\\langle\\dfrac1{a_n}\\right\\rangle$ 是公差 $' + k + '$ 的等差數列，首項 $\\dfrac1{a_1}=' + s + '$。',
      '(1) $\\dfrac1{a_2}=' + s + '+' + k + '=' + (s + k) + '$、$\\dfrac1{a_3}=' + (s + k) + '+' + k + '=' + (s + 2 * k) + '$，倒回去得 $a_2=' + Fr.tex(fF(p.ans.a2)) + '$、$a_3=' + Fr.tex(fF(p.ans.a3)) + '$。',
      '(2) $\\dfrac1{a_n}=' + s + '+' + (k === 1 ? '(n-1)' : '(n-1)\\times' + k) + '=' + lin(k, s - k) + '$，倒回去得 $a_n=\\dfrac{1}{' + lin(k, s - k) + '}$。',
      '(3) 代 $n=' + m + '$：$\\dfrac1{a_{' + m + '}}=' + (s + k * (m - 1)) + '$，所以 $a_{' + m + '}=' + Fr.tex(fF(p.ans.am)) + '$。' + fin(o)];
  };

  /* 1-11 週期數列 */
  L1_SOL.periodic = function (p, o) {
    var stepf = function (x) { return p.kind === 0 ? Fr.div(F(1), Fr.sub(F(1), x)) : p.kind === 1 ? Fr.sub(F(1), Fr.div(F(1), x)) : Fr.div(Fr.sub(x, F(1)), Fr.add(x, F(1))); };
    var seq = [F(p.a1)]; for (var i = 0; i < 5; i++) seq.push(stepf(seq[i]));
    var per = p.ans.per, cyc = seq.slice(0, per);
    var cs = SUMF(0, per - 1, function (i) { return cyc[i]; });
    var full = Math.floor(p.N / per), rem = p.N % per;
    var part = SUMF(0, rem - 1, function (i) { return cyc[i]; });
    return ['(1) 一項一項代下去：$a_2=' + Fr.tex(seq[1]) + '$、$a_3=' + Fr.tex(seq[2]) + '$、$a_4=' + Fr.tex(seq[3]) + '$'
        + (per === 3 ? '——$a_4$ 已經回到 $a_1$，所以週期是 $3$。' : '、$a_5=' + Fr.tex(seq[4]) + '$——$a_5$ 才回到 $a_1$，所以週期是 $4$。'),
      '(2) 一個週期是 $' + cyc.map(function (u) { return Fr.tex(u); }).join(',\\ ') + '$。'
        + (rem === 0 ? '$' + p.N + '\\div ' + per + '$ 整除，$a_{' + p.N + '}$ 就是週期的最後一項：$a_{' + p.N + '}=' + Fr.tex(fF(p.ans.aN)) + '$。'
                     : '$' + p.N + '=' + per + '\\times' + full + '+' + rem + '$，$a_{' + p.N + '}$ 就是週期的第 $' + rem + '$ 項：$a_{' + p.N + '}=' + Fr.tex(fF(p.ans.aN)) + '$。'),
      '(3) 一個完整週期的和是 $' + Fr.tex(cs) + '$，共 $' + full + '$ 個完整週期' + (rem === 0 ? '' : '，再加零頭 $' + rem + '$ 項（和為 $' + Fr.tex(part) + '$）')
        + '：$S_{' + p.N + '}=' + full + '\\times' + parF(cs) + addF(part) + '=' + Fr.tex(fF(p.ans.SN)) + '$。' + fin(o)];
  };

  /* 2-1 Σ 的基本計算 */
  L1_SOL.sigmaCalc = function (p, o) {
    var N = p.N, al = p.al, be = p.be, ga = p.ga;
    var s2 = N * (N + 1) * (2 * N + 1) / 6, s1 = N * (N + 1) / 2;
    var pieces = '';
    if (al) pieces += term(al, '\\displaystyle\\sum k^2', true);
    if (be) pieces += term(be, '\\displaystyle\\sum k', pieces === '');
    if (ga) pieces += (pieces === '' ? (ga < 0 ? '-' : '') : (ga < 0 ? '-' : '+')) + Math.abs(ga) + '\\times ' + N;
    return ['一般項拆成三塊，$\\sum$ 可以逐塊算：$' + sigma(1, N, '(' + quad(al, be, ga, 'k') + ')') + '=' + pieces + '$（$\\displaystyle\\sum_{k=1}^{' + N + '}1=' + N + '$）。',
      '代公式：$\\displaystyle\\sum_{k=1}^{' + N + '}k^2=\\dfrac{' + N + '\\times' + (N + 1) + '\\times' + (2 * N + 1) + '}{6}=' + s2 + '$、$\\displaystyle\\sum_{k=1}^{' + N + '}k=\\dfrac{' + N + '\\times' + (N + 1) + '}{2}=' + s1 + '$。',
      '合起來：$' + sumT([al * s2, be * s1, ga * N]) + '=' + p.ans + '$。' + fin(o)];
  };

  /* 2-2 Σ 公式：以 n 表示 */
  L1_SOL.sigmaFormula = function (p, o) {
    var a = p.a, b = p.b, tex = mseg(o.a)[0];
    var bf = (b > 0 ? '+' : '-') + (Math.abs(b) === 1 ? '' : Math.abs(b) + '\\cdot');
    return ['先把 $k$ 乘進去再拆開：$\\displaystyle\\sum_{k=1}^{n}k(' + lin(a, b, 'k') + ')=\\displaystyle\\sum_{k=1}^{n}(' + term(a, 'k^2', true) + term(b, 'k', false) + ')=' + (a === 1 ? '' : a) + '\\displaystyle\\sum k^2' + term(b, '\\displaystyle\\sum k', false) + '$。',
      '代公式並提出公因式 $\\dfrac{n(n+1)}{6}$：$=' + (a === 1 ? '' : a + '\\cdot') + '\\dfrac{n(n+1)(2n+1)}{6}' + bf + '\\dfrac{n(n+1)}{2}=\\dfrac{n(n+1)}{6}\\left[' + (a === 1 ? '' : a) + '(2n+1)' + term(3 * b, '', false) + '\\right]$。',
      '括號內整理成 $' + lin(2 * a, a + 3 * b) + '$，再把分數約到最簡：$' + tex + '$。代 $n=1$ 檢查：左式只有一項 $1\\times' + parT(sumT([a, b])) + '=' + (a + b) + '$，右式也是 $' + (a + b) + '$。' + fin(o)];
  };

  /* 2-3 等差級數：S_N 與中段和 */
  L1_SOL.arSum = function (p, o) {
    var d = (p.aq - p.ap) / (p.q - p.p), a1 = p.ap - (p.p - 1) * d;
    var aN = a1 + (p.N - 1) * d, alo = a1 + (p.lo - 1) * d, ahi = a1 + (p.hi - 1) * d, cnt = p.hi - p.lo + 1;
    return ['先解出公差與首項：$d=\\dfrac{a_{' + p.q + '}-a_{' + p.p + '}}{' + p.q + '-' + p.p + '}=\\dfrac{' + (p.aq - p.ap) + '}{' + (p.q - p.p) + '}=' + d + '$，$a_1=a_{' + p.p + '}-' + (p.p === 2 ? '' : (p.p - 1)) + 'd=' + a1 + '$。',
      '(1) 末項 $a_{' + p.N + '}=' + a1 + term((p.N - 1) * d, '', false) + '=' + aN + '$，用「項數 $\\times$（首＋末）$\\div2$」：$S_{' + p.N + '}=\\dfrac{' + p.N + parT(sumT([a1, aN])) + '}{2}=' + p.ans.SN + '$。',
      '(2) 從第 $' + p.lo + '$ 項到第 $' + p.hi + '$ 項共 $' + p.hi + '-' + p.lo + '+1=' + cnt + '$ 項，首 $a_{' + p.lo + '}=' + alo + '$、末 $a_{' + p.hi + '}=' + ahi + '$：和 $=\\dfrac{' + cnt + parT(sumT([alo, ahi])) + '}{2}=' + p.ans.mid + '$。' + fin(o)];
  };

  /* 2-4 S_n 何時最大 */
  L1_SOL.arSumMax = function (p, o) {
    var n = p.ans.n, an = p.a1 + (n - 1) * p.d, bd = F(p.a1 - p.d, -p.d);
    return ['公差是負的，$S_n$ 一路加到最後一個正項時最大，之後再加只會變小——所以先解 $a_n\\gt 0$。',
      '$a_n=' + lin(p.d, p.a1 - p.d) + '\\gt 0$ ⟹ $n\\lt ' + Fr.tex(bd) + '$，$n$ 取正整數 ⟹ $n=' + n + '$（此時 $a_{' + n + '}=' + an + '\\gt 0$，下一項 $a_{' + (n + 1) + '}=' + (an + p.d) + '\\lt 0$）。',
      '$S_{' + n + '}=\\dfrac{' + n + parT(sumT([p.a1, an])) + '}{2}=' + p.ans.Smax + '$。' + fin(o)];
  };

  /* 2-5 等比級數 */
  L1_SOL.gpSum = function (p, o) {
    var rf = fF(p.r), S = fF(p.ans), N = p.N, a1 = p.a1;
    var rN = fpow(rf, N), num = Fr.mul(F(a1), Fr.sub(F(1), rN)), den = Fr.sub(F(1), rf);
    return ['套等比級數公式 $S_n=\\dfrac{a_1(1-r^{n})}{1-r}$，本題 $a_1=' + a1 + '$、$r=' + Fr.tex(rf) + '$、$n=' + N + '$。',
      '先算 $r^{' + N + '}=' + parF(rf) + '^{' + N + '}=' + Fr.tex(rN) + '$' + (rf.n < 0 ? '（公比是負的，' + N + ' 是' + (N % 2 === 0 ? '偶' : '奇') + '數，所以結果是' + (N % 2 === 0 ? '正' : '負') + '的）' : '') + '。',
      '分子 $a_1(1-r^{' + N + '})=' + hpz(a1) + '\\times' + parF(Fr.sub(F(1), rN)) + '=' + Fr.tex(num) + '$、分母 $1-r=' + Fr.tex(den) + '$，相除得 $S_{' + N + '}=' + Fr.tex(S) + '$。' + fin(o)];
  };

  /* 2-6 等比級數的分段和 */
  L1_SOL.gpBlocks = function (p, o) {
    var A = p.A, B2 = p.S2 - A, t = B2 / A, third = B2 * t;
    return ['把前 $3n$ 項切成等長的三段：$S_n$、$S_{2n}-S_n$、$S_{3n}-S_{2n}$。每一段都是前一段各項再乘 $r^{n}$，所以這三段和自己也成等比。',
      '前兩段：第一段 $=' + A + '$，第二段 $=' + p.S2 + '-' + A + '=' + B2 + '$，公比 $r^{n}=' + B2 + '\\div ' + A + '=' + t + '$。',
      '第三段 $=' + B2 + '\\times' + t + '=' + third + '$，三段加起來才是答案：$' + A + '+' + B2 + '+' + third + '=' + p.ans + '$。' + fin(o)];
  };

  /* 2-7 裂項相消 */
  L1_SOL.telescope = function (p, o) {
    var a = p.a, b = p.b, N = p.N, S = fF(p.ans);
    var co = a === 1 ? '' : '\\dfrac1{' + a + '}';
    var c1 = a + b, c2 = 2 * a + b, c3 = 3 * a + b, cN = a * N + b, cN1 = a * N + a + b;
    var inv = function (x) { return x === 1 ? '1' : '\\dfrac1{' + x + '}'; };
    return ['先裂項：$\\dfrac{1}{(' + lin(a, b, 'k') + ')(' + lin(a, a + b, 'k') + ')}=' + co + '\\left(\\dfrac1{' + lin(a, b, 'k') + '}-\\dfrac1{' + lin(a, a + b, 'k') + '}\\right)$（兩個分母相差 $' + a + '$）。',
      '整串加起來：$' + co + '\\left(' + inv(c1) + '-' + inv(c2) + '+' + inv(c2) + '-' + inv(c3) + '+\\cdots+' + inv(cN) + '-' + inv(cN1) + '\\right)$，中間每一項都被前後抵消，只剩頭尾。',
      '所以總和 $=' + co + '\\left(' + inv(c1) + '-' + inv(cN1) + '\\right)=' + Fr.tex(S) + '$。' + fin(o)];
  };

  /* 2-8 錯位相減 */
  L1_SOL.staggered = function (p, o) {
    var rr = p.r, N = p.N, c1 = p.c1, c0 = p.c0, f = function (k) { return c1 * k + c0; };
    var G = 0; for (var j = 1; j <= N - 1; j++) G += ipow(rr, j);
    var rhs = f(1) + c1 * G - f(N) * ipow(rr, N);
    var gtex = rr - 1 === 1 ? rr + parT(rr + '^{' + (N - 1) + '}-1') : '\\dfrac{' + rr + parT(rr + '^{' + (N - 1) + '}-1') + '}{' + (rr - 1) + '}';
    return ['設 $S=' + f(1) + '+' + f(2) + '\\times' + rr + '+\\cdots+' + f(N) + '\\times' + rr + '^{' + (N - 1) + '}$，兩邊乘 $' + rr + '$：$' + rr + 'S=' + f(1) + '\\times' + rr + '+' + f(2) + '\\times' + rr + '^2+\\cdots+' + f(N) + '\\times' + rr + '^{' + N + '}$。',
      '兩式錯一位相減，中間每一項的係數都變成公差 $' + c1 + '$：$(1-' + rr + ')S=' + f(1) + '+' + (c1 === 1 ? '' : c1) + '\\left(' + rr + '+' + rr + '^2+\\cdots+' + rr + '^{' + (N - 1) + '}\\right)-' + f(N) + '\\cdot' + rr + '^{' + N + '}$。',
      '中間是等比級數：$' + rr + '+\\cdots+' + rr + '^{' + (N - 1) + '}=' + gtex + '=' + G + '$，代回得 $(1-' + rr + ')S=' + sumT([f(1), c1 * G, -f(N) * ipow(rr, N)]) + '=' + rhs + '$。',
      '最後 $S=' + rhs + '\\div ' + hpz(1 - rr) + '=' + p.ans + '$。' + fin(o)];
  };

  /* 2-9 由 S_n 反求 a_n */
  L1_SOL.sumToTerm = function (p, o) {
    var a = p.a, b = p.b, c = p.c, a1 = p.ans.a1, co = p.ans.coef;
    var Sn = quad(a, b, c), Sm1 = term(a, '(n-1)^2', true) + term(b, '(n-1)', false) + term(c, '', false);
    return ['$a_1=S_1$：把 $n=1$ 代進 $S_n$，得 $a_1=' + sumT([a, b, c]) + '=' + a1 + '$。',
      '$n\\ge2$ 時 $a_n=S_n-S_{n-1}=\\left(' + Sn + '\\right)-\\left(' + Sm1 + '\\right)$，乘開後二次項抵消，剩下 $a_n=' + lin(co[0], co[1]) + '$。',
      '檢查第一項合不合：把 $n=1$ 代進 $' + lin(co[0], co[1]) + '$ 得 $' + (co[0] + co[1]) + '$，'
        + (p.ans.isAP ? '與 $a_1=' + a1 + '$ 相同，所以這一條對 $n=1$ 也成立，$\\langle a_n\\rangle$ 是等差數列。' : '與 $a_1=' + a1 + '$ 不同（$S_n$ 有常數項 $' + c + '$），第一項脫隊，所以不是等差數列。') + fin(o)];
  };

  /* 2-10 等差數列的絕對值和 */
  L1_SOL.absSum = function (p, o) {
    var a1 = p.a1, d = p.d, N = p.N, j = 0;
    while (a1 + j * d < 0) j++;                                   /* 前 j 項是負的（沒有恰為 0 的項） */
    var aj = a1 + (j - 1) * d, P = j * (a1 + aj) / 2;
    var an = a1 + (N - 1) * d, aj1 = a1 + j * d, Q = j >= N ? 0 : (N - j) * (aj1 + an) / 2;
    return ['先找變號位置：$a_n=' + lin(d, a1 - d) + '$，$a_n\\lt 0$ ⟺ $n\\lt ' + Fr.tex(F(-(a1 - d), d)) + '$，所以前 $' + j + '$ 項是負的'
        + (j >= N ? '——本題 $' + N + '$ 項全部都是負的。' : '、第 $' + (j + 1) + '$ 項起是正的。'),
      '取絕對值就是把負的那一段整段變號：$|a_1|+\\cdots+|a_{' + N + '}|=-\\left(a_1+\\cdots+a_{' + j + '}\\right)' + (j >= N ? '' : '+\\left(a_{' + (j + 1) + '}+\\cdots+a_{' + N + '}\\right)') + '$。',
      '前段和 $=\\dfrac{' + j + parT(sumT([a1, aj])) + '}{2}=' + P + '$'
        + (j >= N ? '，所以答案 $=-' + hpz(P) + '=' + p.ans + '$。' : '、後段和 $=\\dfrac{' + (N - j) + parT(sumT([aj1, an])) + '}{2}=' + Q + '$，所以答案 $=' + Q + '-' + hpz(P) + '=' + p.ans + '$。') + fin(o)];
  };

  /* 2-11 複利與單利 */
  L1_SOL.compound = function (p, o) {
    var P = p.P, i = p.i, n = p.n, comp = p.ans.comp, simple = p.ans.simple, rate = (100 + i) / 100;
    var yr = [], v = P;
    for (var k = 1; k <= n; k++) { v = Math.round(P * Math.pow(rate, k)); yr.push('第 $' + k + '$ 年末 $' + v + '$ 元'); }
    var I = P * i / 100;
    return ['(1) 複利是「本利和再生利息」，每年乘 $' + rate + '$：' + yr.join('、') + '。也可以直接寫成 $' + P + '\\times' + rate + '^{' + n + '}=' + comp + '$ 元。',
      '(2) 單利只有本金生利息，每年利息固定 $' + P + '\\times' + (i / 100) + '=' + I + '$ 元，$' + n + '$ 年共 $' + n + '\\times' + I + '=' + (n * I) + '$ 元，本利和 $=' + P + '+' + (n * I) + '=' + simple + '$ 元。',
      '兩者相差 $' + comp + '-' + simple + '=' + (comp - simple) + '$ 元——差的就是「利息也在生利息」的那一部分。' + fin(o)];
  };

  /* 3-1 歸納法的遞推步驟 */
  L1_SOL.inductionStep = function (p, o) {
    var I = null; for (var i = 0; i < IDENT.length; i++) if (IDENT[i].id === p.id) I = IDENT[i];
    return ['(1) 左式是把第 $1$ 項一路加到第 $' + p.m + '$ 項；右式是把 $n=' + p.m + '$ 代進 $' + I.gT + '$。兩邊都等於 $' + Fr.tex(fF(p.ans.gm)) + '$，$n=' + p.m + '$ 時等式成立。',
      '(2) 從 $n=k$ 到 $n=k+1$，左式多出來的正好是「第 $k+1$ 項」——把左式一般項的 $n$ 換成 $k+1$ 就得到 $' + I.fT + '$。',
      '右式也把 $' + I.gT + '$ 的 $n$ 換成 $k+1$ 再化簡，得 $' + I.gk1 + '$。遞推步驟要證的就是：$n=k$ 的右式再加上那一項，會等於這個式子。' + fin(o)];
  };

  /* 3-2 歸納法證整除 */
  L1_SOL.divisible = function (p, o) {
    var a = p.a, b = p.b, c = p.c, d = p.d, m = p.m, co = p.ans.coef;
    var ab = (a === 1 ? '' : a + '\\cdot') + b;
    var diff = term(c * (1 - b), 'k', false) + term(c + d * (1 - b), '', false);
    var inner = term(co[0], 't', true) + term(co[1], 'k', false) + term(co[2], '', false);
    return ['(1) 把 $n=1$ 代進去：$f(1)=' + sumT([a * b, c, d]) + '=' + p.ans.f1 + '$，確實是 $' + m + '$ 的倍數。',
      '(2) 先把兩個式子並排：$f(k+1)=' + ab + '^{\\,k+1}' + term(c, '(k+1)', false) + term(d, '', false) + '$、$' + b + '\\,f(k)=' + ab + '^{\\,k+1}' + term(b * c, 'k', false) + term(b * d, '', false) + '$，指數部分完全一樣，相減得 $f(k+1)=' + b + '\\,f(k)' + diff + '$。',
      '把假設 $f(k)=' + m + 't$（$t$ 為整數）代進去：$f(k+1)=' + b + '\\times' + m + 't' + diff + '=' + m + '\\left(' + inner + '\\right)$，括號內是整數，所以 $f(k+1)$ 也是 $' + m + '$ 的倍數。' + fin(o)];
  };
  var META_L1 = [
      ['arTerm', '§1 等差：由兩項定數列'], ['arSign', '§1 等差的變號位置'], ['arMiddle', '§1 三數等差：對稱設法'], ['gpTerm', '§1 等比：由兩項求公比'], ['gpMiddle', '§1 三數等比：對稱設法'], ['growth', '§1 平均成長率'],
      ['recurLinear', '§1 一階線性遞迴：不動點'], ['recurSum', '§1 連加型遞迴'], ['recurProd', '§1 連乘型遞迴'], ['recurRecip', '§1 分式遞迴：取倒數'], ['periodic', '§1 週期數列'],
      ['sigmaCalc', '§2 Σ 的計算'], ['sigmaFormula', '§2 Σ 公式：以 n 表示'], ['arSum', '§2 等差級數與中段和'], ['arSumMax', '§2 S_n 何時最大'], ['gpSum', '§2 等比級數'], ['gpBlocks', '§2 等比級數的分段和'],
      ['telescope', '§2 裂項相消'], ['staggered', '§2 錯位相減'], ['sumToTerm', '§2 由 S_n 反求 a_n'], ['absSum', '§2 等差的絕對值和'], ['compound', '§2 複利與單利'],
      ['inductionStep', '§3 歸納法：遞推步驟'], ['divisible', '§3 歸納法證整除']
  ];
  var META_L2 = [
      ['arSymm', '§2 S_m=S_n 的對稱性'], ['sumRatio', '§2 前 n 項和之比'], ['oddEvenGP', '§2 奇數項和與偶數項和'], ['gpSquares', '§2 平方後仍是等比'], ['sumFromSn', '§2 S_n 含指數：脫隊'],
      ['weightedRecur', '§2 由 Σ k·a_k 反求單項'], ['prodAP', '§2 等差×等差級數'], ['absQuad', '§2 二次數列的絕對值和'], ['floorSum', '§2 高斯符號分群'], ['groupSeq', '§2 分群數列'],
      ['kOver2k', '§2 等差÷等比'], ['telescopeN', '§2 裂項反求項數'], ['recurMixed', '§1 混合型遞迴'], ['annuity', '§2 零存整付'], ['snRecur', '§2 S_n 與 a_n 的關係式'], ['logGP', '§2 等比取 log 變等差']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     全部用整數／Fraction 逐項算；p 只放旗標，驗算器一律從題幹重算。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};
  function sgn3(n) { return n < 0 ? '(' + n + ')' : String(n); }
  function texPow(b, e) { return e === 1 ? String(b) : b + '^{' + e + '}'; }
  function ipowF(f, e) { var v = F(1); for (var i = 0; i < e; i++) v = Fr.mul(v, f); return v; }
  function fracCoefTex(f, v) {   /* f·v，f 為 Fraction，v 可空 */
    if (f.n === 0) return '0';
    if (!v) return Fr.tex(f);
    if (Fr.eq(f, F(1))) return v;
    if (Fr.eq(f, F(-1))) return '-' + v;
    return Fr.tex(f) + (f.d === 1 ? '\\cdot ' : '') + v;
  }

  /* L3-1　c·a_{n+1} − d·a_n = e：先除成 a_{n+1}=pa_n+q，再解不動點 */
  L3.recurDivide = function (r) {
    var c, d, e, a1, m, p, q, x, an, tries = 0;
    do { c = r.pick([2, 3, 4, 5]); d = r.pick([1, 2, 3, 4, 5, -1, -2, -3]); e = r.nz(-6, 6); a1 = r.int(-6, 9); m = r.int(5, 8); }
    while ((Math.abs(d) === c || gcd(c, Math.abs(d)) !== 1 || (a1 * (c - d) === e)) && tries++ < 200);
    p = F(d, c); q = F(e, c); x = Fr.div(q, Fr.sub(F(1), p));            /* 不動點 */
    an = Fr.add(Fr.mul(Fr.sub(F(a1), x), ipowF(p, m - 1)), x);
    var eq = term(c, 'a_{n+1}', true) + term(-d, 'a_n', false) + '=' + e;
    return { q: '設 ' + T('a_1=' + a1) + '，且 ' + T(eq) + '（' + T('n\\ge 1') + '）。求 ' + T('a_{' + m + '}') + '。', a: T('a_{' + m + '}=' + Fr.tex(an)),
      h: '先把 $a_{n+1}$ 的係數除掉：$a_{n+1}=' + Fr.tex(p) + 'a_n' + termF(q, '', false) + '$。不動點 $x=' + Fr.tex(p) + 'x' + termF(q, '', false) + '$ 解得 $x=' + Fr.tex(x) + '$，於是 $a_{n+1}' + termF(Fr.sub(F(0), x), '', false) + '=' + Fr.tex(p) + '\\left(a_n' + termF(Fr.sub(F(0), x), '', false) + '\\right)$：$\\langle a_n' + termF(Fr.sub(F(0), x), '', false) + '\\rangle$ 是公比 $' + Fr.tex(p) + '$ 的等比數列。',
      p: { c: c, d: d, e: e, a1: a1, m: m, ans: fr2(an) } };
  };

  /* L3-2／L3-4　給首項、末項、總和（項數不給）：S=(a₁−aₙr)/(1−r) 解 r */
  function gpEnds(r, askN) {
    var a1, rr, n, an, S, tries = 0;
    do { a1 = r.pick([1, 2, 3, 4, 5, 6]); rr = r.pick([2, 3, 4, -2, -3, 5]); n = r.int(4, 7); an = a1 * ipow(rr, n - 1); S = SUM(1, n, function (k) { return a1 * ipow(rr, k - 1); }); }
    while ((Math.abs(an) > 20000) && tries++ < 100);
    var k = r.int(2, 3), a2 = a1 * ipow(rr, 1), an1 = a1 * ipow(rr, n - 2), ak = a1 * ipow(rr, k - 1);
    var head = '等比數列 ' + T('\\langle a_n\\rangle') + ' 中 ' + T('a_1=' + a1) + '、' + T('a_n=' + an) + '，且 ' + T('a_1+a_2+\\cdots+a_n=' + S) + '。';
    var hint = '$S_n=\\dfrac{a_1-a_nr}{1-r}$ 不需要知道 $n$ 就能解 $r$：$' + S + '=\\dfrac{' + a1 + '-' + sgn3(an) + 'r}{1-r}$，交叉相乘解一次方程式。有了 $r$，再由 $a_1r^{n-1}=' + an + '$ 定出 $n$。';
    if (!askN) return { q: head + '求 ' + T('a_2+a_{n-1}') + '。', a: T(String(a2 + an1)), h: hint, p: { a1: a1, r: rr, n: n, ask: 0, ans: a2 + an1 } };
    return { q: head + '求項數 ' + T('n') + ' 與第 ' + T(String(k)) + ' 項。', a: T('n=' + n) + '、' + T('a_{' + k + '}=' + ak), h: hint, p: { a1: a1, r: rr, n: n, ask: k, ans: [n, ak] } };
  }
  L3.gpEndsSum = function (r) { return gpEnds(r, false); };
  L3.gpEndsSumN = function (r) { return gpEnds(r, true); };

  /* L3-3　五數等差、給和與積：設 m−2d,…,m+2d，積是 d² 的二次式 */
  L3.fiveAP = function (r) {
    var m, d, P, d2sq, v = r.int(0, 1), tries = 0;
    do { m = r.pick([4, 6, 8, 10, -4, -6, -8]); d = r.int(1, Math.abs(m) + 1); P = m * (m * m - d * d) * (m * m - 4 * d * d); d2sq = 5 * m * m / 4 - d * d; }
    while ((d2sq <= 0 || d2sq === d * d || P === 0 || (v === 1 && Number.isInteger(Math.sqrt(d2sq)))) && tries++ < 200);
    var isSq = Number.isInteger(Math.sqrt(d2sq)), other = isSq ? String(Math.sqrt(d2sq)) : '\\sqrt{' + d2sq + '}';
    var five = [m - 2 * d, m - d, m, m + d, m + 2 * d];
    var hh = '設五數為 $m-2d,\\ m-d,\\ m,\\ m+d,\\ m+2d$：和 $=5m=' + 5 * m + '$ ⟹ $m=' + m + '$。乘積 $=m(m^2-d^2)(m^2-4d^2)=' + P + '$，令 $t=d^2$ 得 $t$ 的二次方程式 $4t^2-' + 5 * m * m + 't' + term(m * m * m * m - P / m, '', false) + '=0$';
    if (v === 0) return { q: '五個數成等差數列，其和為 ' + T(String(5 * m)) + '、乘積為 ' + T(String(P)) + '。求公差 ' + T('d') + ' 所有可能的值。', a: T('d=\\pm' + d + '\\ \\text{或}\\ \\pm' + other),
      h: hh + '，兩個 $t$ 都要開根號（正負各一）。', p: { m: m, d: d, P: P, v: v, ans: [d * d, d2sq] } };
    return { q: '五個數成等差數列，其和為 ' + T(String(5 * m)) + '、乘積為 ' + T(String(P)) + '，且公差為正整數。求這五個數。', a: T(five.join(',\\ ')),
      h: hh + '，其中一個根 $t=' + d2sq + '$ 不是完全平方數，捨去；$t=' + d * d + '$ 開根號取正的 $d=' + d + '$，再由 $m=' + m + '$ 寫出五數。', p: { m: m, d: d, P: P, v: v, ans: five } };
  };

  /* L3-5　刪去一項後的平均：刪掉的項 = S_N − (N−1)×平均，再用 a_n=S_n−S_{n−1} 找是第幾項 */
  L3.removeTerm = function (r) {
    var a, b, N, k, SN, ak, rest, A, tries = 0;
    do { a = r.int(1, 4); b = r.int(-5, 5); N = r.pick([13, 16, 19, 21, 25, 31]); k = r.int(2, N - 1); SN = a * N * N + b * N; ak = 2 * a * k + (b - a); rest = SN - ak; A = rest / (N - 1); }
    while ((A !== Math.round(A) || ak <= 0) && tries++ < 3000);
    return { q: '數列 ' + T('\\langle a_n\\rangle') + ' 共 ' + T(String(N)) + ' 項，前 ' + T('n') + ' 項和 ' + T('S_n=' + quad(a, b, 0)) + '。若刪去某一項後，剩餘 ' + T(String(N - 1)) + ' 項的算術平均數為 ' + T(String(A)) + '，則刪去的是第幾項？', a: '第 ' + T(String(k)) + ' 項',
      h: '$S_{' + N + '}=' + SN + '$，剩餘 $' + (N - 1) + '$ 項的和 $=' + (N - 1) + '\\times' + A + '=' + rest + '$，所以刪掉的那一項是 $' + ak + '$。再用 $a_n=S_n-S_{n-1}$（$n\\ge2$）寫出一般項 $a_n=' + lin(2 * a, b - a) + '$（$a_1=S_1$ 也符合），解 $' + lin(2 * a, b - a) + '=' + ak + '$。',
      p: { a: a, b: b, N: N, A: A, ans: k } };
  };

  /* L3-6　a_n=a_{n−1}+(指數項)+(一次項)：疊縮相加，指數部分等比、一次部分等差 */
  L3.recurExpLin = function (r) {
    var base = r.pick([2, 2, 3]), pc = r.pick([1, 1, 2, 3]), c = r.int(-1, 2), qn = r.nz(-3, 3), s = r.int(-3, 3), a1 = r.int(-5, 9), m = r.int(6, 10), v = a1;
    for (var n = 2; n <= m; n++) v += pc * ipow(base, n + c) + qn * n + s;
    var expT = (pc === 1 ? '' : pc + '\\cdot ') + base + '^{n' + term(c, '', false) + '}', body = expT + term(qn, 'n', false) + term(s, '', false);
    return { q: '設 ' + T('a_1=' + a1) + '，且 ' + T('a_n=a_{n-1}+' + body) + '（' + T('n\\ge2') + '）。求 ' + T('a_{' + m + '}') + '。', a: T('a_{' + m + '}=' + v),
      h: '疊縮相加：$a_{' + m + '}=a_1+\\displaystyle\\sum_{n=2}^{' + m + '}\\left(' + body + '\\right)$，把指數項（等比級數，首項 $' + (pc === 1 ? '' : pc + '\\cdot ') + texPow(base, 2 + c) + '$、公比 $' + base + '$、共 $' + (m - 1) + '$ 項）與一次項（等差級數）分開加，常數項是 $' + (m - 1) + '$ 個 $' + s + '$。',
      p: { base: base, pc: pc, c: c, qn: qn, s: s, a1: a1, m: m, ans: v } };
  };

  /* L3-7　給 a_j 與 a_{n+1}=(n+2)/n·a_n(+A)：往前推、列前五項猜一般項、歸納驗證 */
  L3.recurGuess = function (r) {
    var A = r.int(1, 9), fam = r.int(0, 1), j = r.int(2, 4), gen = fam === 0 ? function (n) { return A * n * n; } : function (n) { return A * n * (n + 1); };
    var list = [1, 2, 3, 4, 5].map(gen), form = fam === 0 ? (A === 1 ? 'n^2' : A + 'n^2') : (A === 1 ? 'n(n+1)' : A + 'n(n+1)');
    var rec = 'a_{n+1}=\\dfrac{n+2}{n}a_n' + (fam === 0 ? '+' + A : '');
    return { q: '設數列 ' + T('\\langle a_n\\rangle') + ' 滿足 ' + T('a_' + j + '=' + gen(j)) + '，且對任意正整數 ' + T('n') + '，' + T(rec) + '。(1) 列出 ' + T('a_1,\\dots,a_5') + '。(2) 猜測一般項並用數學歸納法證明。',
      a: '(1) ' + T(list.join(',\\ ')) + '　(2) ' + T('a_n=' + form),
      h: '先往前推：由 $a_' + j + '=' + gen(j) + '$ 與 $a_' + j + '=' + fracCoefTex(F(j + 1, j - 1), 'a_' + (j - 1)) + (fam === 0 ? '+' + A : '') + '$ 解出 $a_' + (j - 1) + '$，一路推到 $a_1$，再往後推到 $a_5$。看 $a_1,\\dots,a_5$ 與 $' + (A === 1 ? 'n^2' : A + 'n^2') + '$、$' + (A === 1 ? 'n(n+1)' : A + 'n(n+1)') + '$ 哪個吻合，猜完設 $a_k$ 成立，代進遞迴式驗 $a_{k+1}$。',
      p: { A: A, fam: fam, j: j, ans: { list: list, fam: fam, A: A } } };
  };

  /* L3-8　分式遞迴：由一般項 g(n)=(αn+β)/(γn+δ) 反造遞迴式 M = G·T·adj(G) */
  L3.fracRecurGuess = function (r) {
    var al, be, ga, de, det, tries = 0, M, g;
    do {
      al = r.int(1, 3); be = r.int(0, 4); ga = r.int(1, 4); de = r.int(1, 6); det = al * de - be * ga;
      /* M = G·T·adj(G)，T=[[1,1],[0,1]] */
      var GT = [[al, al + be], [ga, ga + de]], adj = [[de, -be], [-ga, al]];
      M = [[GT[0][0] * adj[0][0] + GT[0][1] * adj[1][0], GT[0][0] * adj[0][1] + GT[0][1] * adj[1][1]], [GT[1][0] * adj[0][0] + GT[1][1] * adj[1][0], GT[1][0] * adj[0][1] + GT[1][1] * adj[1][1]]];
      var gg = gcd(gcd(M[0][0], M[0][1]), gcd(M[1][0], M[1][1])) || 1; M = M.map(function (row) { return row.map(function (x) { return x / gg; }); });
      if (M[1][0] < 0 || (M[1][0] === 0 && M[1][1] < 0)) M = M.map(function (row) { return row.map(function (x) { return -x; }); });
    } while ((det === 0 || M[1][0] === 0 || Math.abs(M[0][0]) > 30 || Math.abs(M[1][1]) > 30) && tries++ < 300);
    g = function (n) { return F(al * n + be, ga * n + de); };
    var vals = [2, 3, 4, 5].map(g), a1 = g(1);
    var num = term(M[0][0], 'a_{n-1}', true) + term(M[0][1], '', false), den = term(M[1][0], 'a_{n-1}', true) + term(M[1][1], '', false);
    var form = '\\dfrac{' + lin(al, be) + '}{' + lin(ga, de) + '}';
    return { q: '數列 ' + T('\\langle a_n\\rangle') + ' 滿足 ' + T('a_1=' + Fr.tex(a1)) + '，' + T('a_n=\\dfrac{' + num + '}{' + den + '}') + '（' + T('n\\ge2') + '）。(1) 求 ' + T('a_2,a_3,a_4,a_5') + '。(2) 猜測一般項。(3) 用數學歸納法證明。',
      a: '(1) ' + T(vals.map(function (f) { return Fr.tex(f); }).join(',\\ ')) + '　(2) ' + T('a_n=' + form),
      h: '老實算四項，<b>分子、分母分開看</b>：分子 $' + [1, 2, 3, 4, 5].map(function (n) { return al * n + be; }).join(',\\ ') + '$、分母 $' + [1, 2, 3, 4, 5].map(function (n) { return ga * n + de; }).join(',\\ ') + '$（要用同一種寫法、先不要約分）各是等差數列，猜出 $a_n$ 後設 $a_k$ 成立，代進遞迴式把 $a_{k+1}$ 整理出來。',
      p: { al: al, be: be, ga: ga, de: de, M: M, ans: { vals: vals.map(fr2), form: [al, be, ga, de] } } };
  };

  /* L3-9　方格斜線編號：第 k 條斜線有 k 個數 */
  L3.diagonalGrid = function (r) {
    var v = r.int(0, 1), N, k, j, row, col;
    if (v === 0) { N = r.int(30, 400); k = 1; while (k * (k + 1) / 2 < N) k++; j = N - k * (k - 1) / 2; row = k - j + 1; col = j; }
    else { row = r.int(2, 14); col = r.int(2, 14); k = row + col - 1; j = col; N = k * (k - 1) / 2 + j; }
    var rule = '在無限大的方格中編號：' + T('1') + ' 填在第一列第一行；' + T('2,3') + ' 從第二列第一行往右上填到第一列第二行；' + T('4,5,6') + ' 從第三列第一行往右上填到第一列第三行……依此類推。';
    return { q: rule + (v === 0 ? '若 ' + T(String(N)) + ' 在第 ' + T('m') + ' 列第 ' + T('n') + ' 行，求 ' + T('(m,n)') + '。' : '第 ' + T(String(row)) + ' 列第 ' + T(String(col)) + ' 行填的是哪一個數？'),
      a: v === 0 ? T('(m,n)=(' + row + ',' + col + ')') : T(String(N)),
      h: '第 $k$ 條斜線有 $k$ 個數，前 $k$ 條共 $\\dfrac{k(k+1)}{2}$ 個；第 $k$ 條從第 $k$ 列第 $1$ 行出發，每走一個「列減 $1$、行加 $1$」，所以第 $k$ 條的第 $j$ 個在第 $k-j+1$ 列、第 $j$ 行。' + (v === 0 ? '先用 $\\dfrac{k(k+1)}{2}$ 夾出 $' + N + '$ 在第幾條、第幾個。' : '反過來：第 $' + row + '$ 列第 $' + col + '$ 行是第 $' + row + '+' + col + '-1=' + k + '$ 條的第 $' + col + '$ 個。'),
      p: { v: v, N: N, row: row, col: col } };
  };

  /* L3-10　兩個數列交錯相加：拆成等差級數＋等比級數，各自數項數 */
  L3.mixedSeries = function (r) {
    var a1 = r.int(1, 5), d = r.int(2, 4), b1 = r.pick([1, 2, 3, 5]), rr = r.pick([2, 3]), K = r.int(6, 10), tries = 0;
    while (b1 * ipow(rr, K - 1) > 20000 && tries++ < 20) K--;
    var aK = a1 + (K - 1) * d, bK = b1 * ipow(rr, K - 1), SA = K * (a1 + aK) / 2, SB = SUM(1, K, function (k) { return b1 * ipow(rr, k - 1); });
    var lead = [a1, b1, a1 + d, b1 * rr, a1 + 2 * d, b1 * rr * rr].join('+');
    return { q: '求 ' + T(lead + '+\\cdots+(' + lin(d, a1 - d, 'k') + ')+' + (b1 === 1 ? '' : b1 + '\\cdot ') + rr + '^{\\,k-1}+\\cdots+' + aK + '+' + bK) + '。', a: T(String(SA + SB)),
      h: '拆成兩串：等差部分 $' + a1 + ',' + (a1 + d) + ',' + (a1 + 2 * d) + ',\\dots,' + aK + '$（$' + lin(d, a1 - d, 'k') + '=' + aK + '$ ⟹ $k=' + K + '$）與等比部分 $' + b1 + ',' + b1 * rr + ',' + b1 * rr * rr + ',\\dots,' + bK + '$（$' + (b1 === 1 ? '' : b1 + '\\cdot ') + rr + '^{k-1}=' + bK + '$ ⟹ $k=' + K + '$），各自套公式再相加。',
      p: { a1: a1, d: d, b1: b1, r: rr, K: K, ans: SA + SB } };
  };

  /* L3-11　兩個等比級數相除：分子公比 r²、分母公比 r，用 r^{2N}−1=(r^N−1)(r^N+1) 約分 */
  L3.gpRatioSeries = function (r) {
    var rr = r.pick([2, 2, 3, 5]), N = r.int(4, rr === 2 ? 10 : 7), v = r.int(0, 2), numT, denT, val, first, hh;
    if (v === 0) {                                                        /* r²+r⁴+…+r^{2N} 除以 r+r²+…+r^N */
      val = F(rr * (ipow(rr, N) + 1), rr + 1); first = rr * rr;
      numT = texPow(rr, 2) + '+' + texPow(rr, 4) + '+' + texPow(rr, 6) + '+\\cdots+' + texPow(rr, 2 * N); denT = rr + '+' + texPow(rr, 2) + '+' + texPow(rr, 3) + '+\\cdots+' + texPow(rr, N);
      hh = '分子是首項 $' + first + '$、公比 $' + rr * rr + '$、共 $' + N + '$ 項：$\\dfrac{' + first + '(' + rr * rr + '^{' + N + '}-1)}{' + (rr * rr - 1) + '}$；分母是首項 $' + rr + '$、公比 $' + rr + '$、共 $' + N + '$ 項：$\\dfrac{' + rr + '(' + rr + '^{' + N + '}-1)}{' + (rr - 1) + '}$。';
    } else if (v === 1) {                                                 /* r+r³+…+r^{2N−1} 除以 r+r²+…+r^N */
      val = F(ipow(rr, N) + 1, rr + 1); first = rr;
      numT = rr + '+' + texPow(rr, 3) + '+' + texPow(rr, 5) + '+\\cdots+' + texPow(rr, 2 * N - 1); denT = rr + '+' + texPow(rr, 2) + '+' + texPow(rr, 3) + '+\\cdots+' + texPow(rr, N);
      hh = '分子是首項 $' + rr + '$、公比 $' + rr * rr + '$、共 $' + N + '$ 項：$\\dfrac{' + rr + '(' + rr * rr + '^{' + N + '}-1)}{' + (rr * rr - 1) + '}$；分母是首項 $' + rr + '$、公比 $' + rr + '$、共 $' + N + '$ 項：$\\dfrac{' + rr + '(' + rr + '^{' + N + '}-1)}{' + (rr - 1) + '}$。';
    } else {                                                              /* 1+r²+…+r^{2N} 除以 1+r+…+r^N（各 N+1 項） */
      val = F(ipow(rr, N + 1) + 1, rr + 1); first = 1;
      numT = '1+' + texPow(rr, 2) + '+' + texPow(rr, 4) + '+\\cdots+' + texPow(rr, 2 * N); denT = '1+' + rr + '+' + texPow(rr, 2) + '+\\cdots+' + texPow(rr, N);
      hh = '分子是首項 $1$、公比 $' + rr * rr + '$、共 $' + (N + 1) + '$ 項：$\\dfrac{' + rr * rr + '^{' + (N + 1) + '}-1}{' + (rr * rr - 1) + '}$；分母是首項 $1$、公比 $' + rr + '$、共 $' + (N + 1) + '$ 項：$\\dfrac{' + rr + '^{' + (N + 1) + '}-1}{' + (rr - 1) + '}$。';
    }
    var M = v === 2 ? N + 1 : N;
    return { q: '求 ' + T('\\dfrac{' + numT + '}{' + denT + '}') + '（化為最簡分數）。', a: T(Fr.tex(val)),
      h: hh + '用 $' + rr * rr + '^{' + M + '}-1=(' + rr + '^{' + M + '}-1)(' + rr + '^{' + M + '}+1)$ 把公因式約掉，不必算出大數。',
      p: { r: rr, N: N, v: v, ans: fr2(val) } };
  };

  /* L3-12　Σk(k+a)(k+b) 的因式分解形：可分解的 (a,b) 在載入時列舉 */
  var SIGFAC = (function () {
    var out = [];
    for (var a = 1; a <= 9; a++) for (var b = a + 1; b <= 12; b++) {
      var B = 3 + 4 * (a + b), C = 2 * (a + b) + 6 * a * b;        /* 3n²+Bn+C，要 = 3(n+u)(n+v) */
      if (B % 3 || C % 3) continue;
      var su = B / 3, pr = C / 3, disc = su * su - 4 * pr, sq = Math.round(Math.sqrt(disc));
      if (disc < 0 || sq * sq !== disc) continue;
      var u = (su - sq) / 2, v = (su + sq) / 2;
      if (u !== Math.round(u) || u <= 0 || u === 1 || v === 1 || u === v) continue;
      out.push({ a: a, b: b, u: u, v: v });
    }
    return out;
  })();
  L3.sigmaFactorForm = function (r) {
    var it = r.pick(SIGFAC), fs = [1, it.u, it.v].sort(function (x, y) { return x - y; }), v = r.int(0, 1), n0 = r.int(3, 8);
    var lhs = '\\displaystyle\\sum_{k=1}^{n}k(k+' + it.a + ')(k+' + it.b + ')', rhs = '\\dfrac{n(n+' + fs[0] + ')(n+' + fs[1] + ')(n+' + fs[2] + ')}{4}';
    var val = SUM(1, n0, function (k) { return k * (k + it.a) * (k + it.b); });
    if (v === 0) return { q: '已知 ' + T(lhs + '=\\dfrac{n(n+b)(n+c)(n+d)}{a}') + '，其中 ' + T('a,b,c,d') + ' 為整數且 ' + T('b\\lt c\\lt d') + '。求 ' + T('(a,b,c,d)') + '。', a: T('(a,b,c,d)=(4,' + fs.join(',') + ')'),
      h: '$k(k+' + it.a + ')(k+' + it.b + ')=k^3+' + (it.a + it.b) + 'k^2+' + it.a * it.b + 'k$，套 $\\sum k^3$、$\\sum k^2$、$\\sum k$ 三個公式後，先把公因式 $\\dfrac{n(n+1)}{4}$ 提出來，括號裡剩一個 $n$ 的二次式，再把它因式分解成兩個一次因式。代 $n=1$ 驗算：左邊 $=' + (1 + it.a) * (1 + it.b) + '$。',
      p: { a: it.a, b: it.b, v: v, ans: [4].concat(fs) } };
    return { q: '已知 ' + T(lhs + '=' + rhs) + '。(1) 代 ' + T('n=1') + ' 驗證等式成立。(2) 利用此式求 ' + T('\\displaystyle\\sum_{k=1}^{' + n0 + '}k(k+' + it.a + ')(k+' + it.b + ')') + '。', a: '(1) 兩邊皆為 ' + T(String((1 + it.a) * (1 + it.b))) + '　(2) ' + T(String(val)),
      h: '(1) 左邊只有一項 $1\\cdot' + (1 + it.a) + '\\cdot' + (1 + it.b) + '$；右邊代 $n=1$。(2) 直接把 $n=' + n0 + '$ 代進右邊的公式，比逐項相加快得多。',
      p: { a: it.a, b: it.b, v: v, n0: n0, ans: [(1 + it.a) * (1 + it.b), val] } };
  };

  /* L3-13　c·S_n=(n+c−1)a_n：寫 n−1 的式子相減，得 a_n/a_{n−1}，疊縮相乘 */
  L3.snRelationProd = function (r) {
    var c = r.pick([2, 3, 3, 4]), a1 = r.int(1, 6), v = r.int(0, 1), m = r.int(5, 9);
    function an(n) { var v2 = F(a1); for (var i = 2; i <= n; i++) v2 = Fr.mul(v2, F(i + c - 2, i - 1)); return v2; }
    var form = c === 2 ? (a1 === 1 ? 'n' : a1 + 'n') : c === 3 ? (a1 === 1 ? '\\dfrac{n(n+1)}{2}' : '\\dfrac{' + a1 + 'n(n+1)}{2}') : (a1 === 1 ? '\\dfrac{n(n+1)(n+2)}{6}' : '\\dfrac{' + a1 + 'n(n+1)(n+2)}{6}');
    var eq = c + '(a_1+a_2+\\cdots+a_n)=(n' + term(c - 1, '', false) + ')a_n', nk = function (k) { return k ? '(n' + term(k, '', false) + ')' : 'n'; };
    return { q: '設數列 ' + T('\\langle a_n\\rangle') + ' 滿足 ' + T('a_1=' + a1) + '，且對所有正整數 ' + T('n') + '，' + T(eq) + '。求 ' + (v === 0 ? T('a_n') : T('a_{' + m + '}')) + '。',
      a: v === 0 ? T('a_n=' + form) : T('a_{' + m + '}=' + Fr.tex(an(m))),
      h: '$' + c + 'S_n=(n' + term(c - 1, '', false) + ')a_n$ 與 $' + c + 'S_{n-1}=' + nk(c - 2) + 'a_{n-1}$ 相減（$n\\ge2$）：$' + c + 'a_n=(n' + term(c - 1, '', false) + ')a_n-' + nk(c - 2) + 'a_{n-1}$ ⟹ $\\dfrac{a_n}{a_{n-1}}=\\dfrac{n' + term(c - 2, '', false) + '}{n-1}$。把 $\\dfrac{a_2}{a_1}\\cdot\\dfrac{a_3}{a_2}\\cdots\\dfrac{a_n}{a_{n-1}}$ 疊縮相乘，大部分因子會約掉。先算兩項檢查：$a_2=' + c + (a1 === 1 ? '' : '\\cdot' + a1) + '=' + Fr.tex(an(2)) + '$、$a_3=\\dfrac{' + (c + 1) + '}{2}\\cdot' + Fr.tex(an(2)) + '=' + Fr.tex(an(3)) + '$' + (v === 0 ? '，猜出 $a_n$ 的形狀後再用一般項驗算。' : '；求 $a_{' + m + '}$ 時把一般項的 $n=' + m + '$ 代入即可。'),
      p: { c: c, a1: a1, v: v, m: m, ans: v === 0 ? [c, a1] : fr2(an(m)) } };
  };

  /* L3-14　係數等差、公比為負的錯位相減 */
  L3.altStaggered = function (r) {
    var rr = r.pick([2, 2, 3, 4]), N = r.int(5, 10), v = r.int(0, 1), cf = function (k) { return v === 0 ? k : 2 * k - 1; };
    var S = SUM(1, N, function (k) { return cf(k) * ipow(-rr, k - 1); });
    var terms = []; for (var k = 1; k <= 4; k++) terms.push((k === 1 ? '' : (k % 2 === 0 ? '-' : '+')) + (k === 1 ? '1' : cf(k) + '\\times' + texPow(rr, k - 1)));
    var last = (N % 2 === 0 ? '-' : '+') + cf(N) + '\\times' + texPow(rr, N - 1), cfT = v === 0 ? 'k' : '(2k-1)', dif = v === 0 ? '' : '2\\left[';
    return { q: '求 ' + T('S=' + terms.join('') + '+\\cdots' + last) + '。', a: T('S=' + S),
      h: '$S=\\displaystyle\\sum_{k=1}^{' + N + '}' + cfT + '(-' + rr + ')^{k-1}$，係數 $' + cfT + '$ 成等差、公比是 $-' + rr + '$。錯位相減：算 $-' + rr + 'S$（每一項乘上公比、往後錯一位），$S-(-' + rr + 'S)=' + (rr + 1) + 'S$ 的右邊會變成 $1+' + dif + '(-' + rr + ')+\\cdots+(-' + rr + ')^{' + (N - 1) + '}' + (v === 0 ? '' : '\\right]') + '$（' + (v === 0 ? '相鄰係數差 $1$' : '相鄰係數差 $2$，所以中間那串等比級數要乘 $2$') + '）再減掉最後一項 $' + cf(N) + '(-' + rr + ')^{' + N + '}$。',
      p: { r: rr, N: N, v: v, ans: S } };
  };

  /* L3-15　兩條含 a_i,a_j 的方程相除得 r^s，配 S_N 定 a_1；剩下是「和與積」的二次方程 */
  L3.gpSystemXY = function (r) {
    var rr, a1, N, SN, i, j, s, u, v, xF, yF, ai, aj, ok, tries = 0, U, V;
    do {
      rr = r.pick([2, 3]); a1 = r.int(1, 5); N = r.int(5, 8); SN = SUM(1, N, function (k) { return a1 * ipow(rr, k - 1); });
      i = r.int(2, 4); j = i + r.int(1, 3); s = r.int(2, 5); ai = a1 * ipow(rr, i - 1); aj = a1 * ipow(rr, j - 1);
      u = r.int(1, 9); v = r.int(1, 9); xF = F(u, ai); yF = F(v, aj);                       /* u=a_i x、v=a_j y */
      var alt = [F(v, ai), F(u, aj)];                                                       /* 另一種配法 */
      ok = u !== v && xF.n < xF.d && yF.n < yF.d && !(alt[0].n < alt[0].d && alt[1].n < alt[1].d) && j + s <= 12;
      U = u + v; V = u * v;
    } while (!ok && tries++ < 500);
    var eq1 = 'a_{' + i + '}x+a_{' + j + '}y=' + U, eq2 = 'a_{' + (i + s) + '}x+a_{' + (j + s) + '}y=' + U * ipow(rr, s);
    return { q: '設 ' + T('\\langle a_n\\rangle') + ' 為等比數列，且 ' + T('a_1+a_2+\\cdots+a_{' + N + '}=' + SN) + '。' + T('x,y') + ' 皆為小於 ' + T('1') + ' 的正實數，滿足 ' + T('(a_{' + i + '}x)(a_{' + j + '}y)=' + V) + ' 與 ' + T('\\begin{cases}' + eq1 + '\\\\ ' + eq2 + '\\end{cases}') + '。求 ' + T('(x,y)') + '。',
      a: T('(x,y)=\\left(' + Fr.tex(xF, true) + ',\\ ' + Fr.tex(yF, true) + '\\right)'),
      h: '第二式是第一式每一項各乘 $r^{' + s + '}$ ⟹ $r^{' + s + '}=' + ipow(rr, s) + '$ ⟹ $r=' + rr + '$；再由 $S_{' + N + '}=' + SN + '$ 定 $a_1$。令 $u=a_{' + i + '}x$、$v=a_{' + j + '}y$：$u+v=' + U + '$、$uv=' + V + '$，$u,v$ 是 $t^2-' + U + 't+' + V + '=0$ 的兩根；兩種配法各算出 $(x,y)$，用「都小於 $1$」挑一種。',
      p: { r: rr, a1: a1, N: N, i: i, j: j, s: s, u: u, v: v, ans: [fr2(xF), fr2(yF)] } };
  };

  var META_L3 = [['recurDivide', '先除成 a_{n+1}=pa_n+q 再解不動點'], ['gpEndsSum', '首末項與總和求 r（求 a₂+aₙ₋₁）'], ['fiveAP', '五數等差給和與積'], ['gpEndsSumN', '首末項與總和求項數'], ['removeTerm', '刪去一項後的平均'], ['recurExpLin', '疊縮相加：指數＋一次'], ['recurGuess', '往前推再猜一般項（歸納）'], ['fracRecurGuess', '分式遞迴猜一般項'], ['diagonalGrid', '方格斜線編號'], ['mixedSeries', '兩數列交錯相加'], ['gpRatioSeries', '兩等比級數相除'], ['sigmaFactorForm', 'Σk(k+a)(k+b) 的因式分解形'], ['snRelationProd', 'c·Sₙ=(n+c−1)aₙ 疊縮相乘'], ['altStaggered', '交錯錯位相減'], ['gpSystemXY', '兩方程相除得 rˢ']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'recurDivide', 'L3-2': 'gpEndsSum', 'L3-3': 'fiveAP', 'L3-4': 'gpEndsSumN', 'L3-5': 'removeTerm', 'L3-6': 'recurExpLin', 'L3-7': 'recurGuess', 'L3-8': 'fracRecurGuess', 'L3-9': 'diagonalGrid', 'L3-10': 'mixedSeries', 'L3-11': 'gpRatioSeries', 'L3-12': 'sigmaFactorForm', 'L3-13': 'snRelationProd', 'L3-14': 'altStaggered', 'L3-15': 'gpSystemXY' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：等差／等比的第 n 項（國中）、指數律（高一上 ch1）、二元一次聯立（國中）、配方求極值（高一上 ch3）、分數的通分（國中）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  function l0pow(b, e) { return e === 1 ? String(b) : b + '^{' + e + '}'; }
  L0.seqNth = function (r) {
    var v = r.int(0, 1), a1 = r.nz(-6, 9), n = r.int(5, 12);
    if (v === 0) {
      var d = r.nz(-5, 6), an = a1 + (n - 1) * d;
      return { q: '等差數列的首項為 ' + T(String(a1)) + '、公差為 ' + T(String(d)) + '，求第 ' + T(String(n)) + ' 項。', a: T('a_{' + n + '}=' + an),
        h: '從第 $1$ 項走到第 $' + n + '$ 項要走 $' + (n - 1) + '$ 步，每步加 $' + d + '$：$a_{' + n + '}=a_1+(' + n + '-1)d=' + a1 + (d < 0 ? '-' : '+') + (n - 1) + '\\times' + Math.abs(d) + '$。本章一般項 $a_n=a_1+(n-1)d$ 的「$n-1$」就是這個步數。',
        p: { v: v, a1: a1, d: d, n: n, ans: an } };
    }
    var rr = r.pick([2, 3, -2, 2, 3, -3]), m = r.int(4, 7), b1 = r.pick([1, 2, 3, 5]), am = b1 * ipow(rr, m - 1);
    return { q: '等比數列的首項為 ' + T(String(b1)) + '、公比為 ' + T(String(rr)) + '，求第 ' + T(String(m)) + ' 項。', a: T('a_{' + m + '}=' + am),
      h: '從第 $1$ 項到第 $' + m + '$ 項要乘 $' + (m - 1) + '$ 次公比：$a_{' + m + '}=a_1\\cdot r^{' + m + '-1}=' + b1 + '\\times' + signedNum(rr) + '^{' + (m - 1) + '}$' + (rr < 0 ? '，負數的偶數次方是正的、奇數次方是負的' : '') + '。本章一般項 $a_n=a_1r^{n-1}$ 的指數是 $n-1$，不是 $n$。',
      p: { v: v, a1: b1, r: rr, n: m, ans: am } };
  };
  L0.expLaw = function (r) {
    var b = r.pick([2, 3, 5, 2]), v = r.int(0, 2), m = r.int(2, 6), n = r.int(2, 5);
    if (v === 0) {                                                 /* a^m · a^n ÷ a^p */
      var p = r.int(1, m + n - 1);
      return { q: '化簡 ' + T('\\dfrac{' + l0pow(b, m) + '\\times' + l0pow(b, n) + '}{' + l0pow(b, p) + '}') + '（以 ' + T(String(b)) + ' 的次方表示）。', a: T(l0pow(b, m + n - p)),
        h: '同底數相乘指數相加、相除指數相減：$' + b + '^{' + m + '+' + n + '-' + p + '}$。等比數列 $a_m\\cdot a_n\\div a_p$ 這類計算全靠指數律。',
        p: { v: v, b: b, ans: [b, m + n - p] } };
    }
    if (v === 1) {                                                 /* (a^m)^n 與 a^m·a^n 的差別 */
      var k = r.int(2, 3), e = r.int(2, 5);
      return { q: '化簡 ' + T('(' + l0pow(b, e) + ')^{' + k + '}') + ' 與 ' + T(l0pow(b, e) + '\\times' + l0pow(b, k)) + '（以 ' + T(String(b)) + ' 的次方表示）。', a: T('(' + l0pow(b, e) + ')^{' + k + '}=' + l0pow(b, e * k)) + '、' + T(l0pow(b, e) + '\\times' + l0pow(b, k) + '=' + l0pow(b, e + k)),
        h: '次方的次方指數相乘：$' + b + '^{' + e + '\\times' + k + '}$；同底相乘指數相加：$' + b + '^{' + e + '+' + k + '}$。本章公比 $r^2$ 的等比數列、$r^{2n}=(r^n)^2$ 都是這條。',
        p: { v: v, b: b, ans: [b, e * k, e + k] } };
    }
    var t = r.int(2, 3);                                           /* a^{n+t} − a^n = (a^t − 1)a^n */
    return { q: '化簡 ' + T(b + '^{n+' + t + '}-' + b + '^{n}') + '（提出公因式，寫成「數 ' + T('\\times ' + b + '^{n}') + '」）。', a: T((ipow(b, t) - 1) + '\\times ' + b + '^{n}'),
      h: '$' + b + '^{n+' + t + '}=' + b + '^{' + t + '}\\cdot ' + b + '^{n}=' + ipow(b, t) + '\\cdot ' + b + '^{n}$，再提出 $' + b + '^{n}$：$(' + ipow(b, t) + '-1)' + b + '^{n}$。等比級數公式的分子 $r^n-1$、錯位相減的整理都要這樣提公因式。',
      p: { v: v, b: b, t: t, ans: [ipow(b, t) - 1, b] } };
  };
  L0.linSys2 = function (r) {
    var x = r.int(-4, 5), y = r.int(-4, 5), a1, b1, a2, b2;
    do { a1 = r.nz(-4, 4); b1 = r.nz(-4, 4); a2 = r.nz(-4, 4); b2 = r.nz(-4, 4); } while (a1 * b2 - a2 * b1 === 0 || (a1 < 0 && b1 < 0) || (a2 < 0 && b2 < 0));
    var e1 = term(a1, 'x', true) + term(b1, 'y', false) + '=' + (a1 * x + b1 * y), e2 = term(a2, 'x', true) + term(b2, 'y', false) + '=' + (a2 * x + b2 * y);
    return { q: '解聯立方程式 ' + T('\\begin{cases}' + e1 + '\\\\ ' + e2 + '\\end{cases}') + '。', a: T('(x,y)=(' + x + ',' + y + ')'),
      h: '加減消去法：先決定消 $x$ 還是消 $y$（這題 $y$ 的係數是 $' + b1 + '$ 與 $' + b2 + '$），把兩式乘到係數絕對值相同，同號相減、異號相加。本章「已知 $a_3$ 與 $a_7$ 求首項與公差」列出來就是這樣的兩條方程式。',
      p: { l1: [a1, b1], l2: [a2, b2], ans: [x, y] } };
  };
  L0.quadExt = function (r) {
    var a = r.pick([1, 2, 3, -1, -2, -1]), h = r.nz(-5, 5), k = r.int(-20, 30), bq = -2 * a * h, cq = a * h * h + k, mx = a < 0;
    return { q: '求二次函數 ' + T('f(x)=' + quad(a, bq, cq, 'x')) + ' 的' + (mx ? '最大值' : '最小值') + '，以及此時的 ' + T('x') + '。', a: T('x=' + h) + ' 時，' + (mx ? '最大值 ' : '最小值 ') + T(String(k)),
      h: '配方：' + (Math.abs(a) === 1 ? (a < 0 ? '先提出負號，' : '') : '先把 $' + a + '$ 提出來，') + '$x$ 的一次項係數的一半是 $' + (-h) + '$，湊成 $' + (a === 1 ? '' : a === -1 ? '-' : a) + '(x' + term(-h, '', false) + ')^2' + term(k, '', false) + '$；' + (mx ? '$a\\lt0$ 開口向下，頂點是最高點' : '$a\\gt0$ 開口向上，頂點是最低點') + '。本章等差級數 $S_n$ 是 $n$ 的二次式，$S_n$ 的最大值就靠配方（再挑最接近頂點的正整數 $n$）。',
      p: { a: a, h: h, k: k, ans: [h, k] } };
  };
  L0.fracSub = function (r) {
    var v = r.int(0, 1), k = r.int(2, 9), m = r.int(1, 4);
    if (v === 0) {
      var val = Fr.sub(F(1, k), F(1, k + m));
      return { q: '計算 ' + T('\\dfrac{1}{' + k + '}-\\dfrac{1}{' + (k + m) + '}') + '（化為最簡分數）。', a: T(Fr.tex(val)),
        h: '通分：分母取 $' + k + '\\times' + (k + m) + '=' + k * (k + m) + '$，分子是 $' + (k + m) + '-' + k + '=' + m + '$' + (val.d !== k * (k + m) ? '，最後約分' : '') + '。本章裂項相消 $\\dfrac{1}{k(k+' + m + ')}=' + (m === 1 ? '' : '\\dfrac{1}{' + m + '}') + '\\left(\\dfrac{1}{k}-\\dfrac{1}{k+' + m + '}\\right)$ 就是把這個算式倒過來用。',
        p: { v: v, k: k, m: m, ans: fr2(val) } };
    }
    var p2 = r.int(2, 9), q2; do { q2 = r.int(2, 9); } while (q2 === p2);
    var val2 = Fr.add(F(1, p2), F(1, q2));
    return { q: '計算 ' + T('\\dfrac{1}{' + p2 + '}+\\dfrac{1}{' + q2 + '}') + '（化為最簡分數）。', a: T(Fr.tex(val2)),
      h: '通分：$\\dfrac{' + q2 + '+' + p2 + '}{' + p2 + '\\times' + q2 + '}=\\dfrac{' + (p2 + q2) + '}{' + p2 * q2 + '}$' + (val2.d !== p2 * q2 ? '，再約分成 $' + Fr.tex(val2) + '$' : '，已是最簡') + '。本章級數的部分和常是分數相加，通分要熟。',
      p: { v: v, p: p2, q: q2, ans: fr2(val2) } };
  };
  var META_L0 = [['seqNth', '等差、等比的第 n 項'], ['expLaw', '指數律'], ['linSys2', '二元一次聯立方程式'], ['quadExt', '配方求極值'], ['fracSub', '分數的通分']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    seqNth: { txt: '等差、等比數列的第 n 項（國中）——本章一般項公式的起點，走幾步、乘幾次都是 n−1', link: null },
    expLaw: { txt: '指數律（高一上第一章 數與式 §4）——等比數列、等比級數、錯位相減都在算次方', link: '../g10a-ch01/practice.html#L1' },
    linSys2: { txt: '二元一次聯立方程式（國中）——已知兩項求首項與公差、公比就是解它', link: null },
    quadExt: { txt: '二次函數配方求極值（高一上第三章 多項式）——等差級數 S_n 是 n 的二次式，最大值靠配方', link: '../g10a-ch03/practice.html#L1' },
    fracSub: { txt: '分數的通分與約分（國中）——裂項相消就是把「通分」倒過來用', link: null }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  function sign3(x) { return x > 0 ? 1 : x < 0 ? -1 : 0; }
  var CONTRAST = {
    'L1.arSign': { f: function (p) { return !!p.pos; }, why: '公差為負的遞減數列問「最後一個正項」、公差為正的遞增數列問「第一個正項」：都是解一次不等式 $a_1+(n-1)d\\gt0$，但一個取解的最大整數、一個取最小整數，方向相反。' },
    'L1.arMiddle': { f: function (p) { return !!p.useSq; }, why: '設三數為 $m-d,\\ m,\\ m+d$：和永遠先給出 $m$；平方和 $=3m^2+2d^2$ 是 $d^2$ 的一次式、乘積 $=m(m^2-d^2)$ 也是 $d^2$ 的一次式，兩種都只解一步，但乘積那型要先除以 $m$。' },
    'L1.gpTerm': { f: function (p) { return sign3(p.ans.r); }, why: '兩項相除得 $r^3$：奇數次方開根號只有一個實數解，所以公比可以是負的；若給的是 $r^2$（相隔偶數項）就會有正負兩個答案。負公比時各項正負交錯，寫 $a_m$ 要看 $m-1$ 的奇偶。' },
    'L1.recurLinear': { f: function (p) { return p.p < 0; }, why: '不動點法 $a_n-x=(a_1-x)p^{n-1}$ 對正負的 $p$ 都一樣；差別在 $p\\lt0$ 時 $a_n-x$ 正負交錯，數列在不動點兩側跳來跳去，代第 $k$ 項時要注意 $p^{k-1}$ 的符號。' },
    'L1.gpSum': { f: function (p) { return p.r[0] < 0 ? 'neg' : p.r[1] !== 1 ? 'frac' : 'pos'; }, why: '公式 $S_n=\\dfrac{a_1(r^n-1)}{r-1}$ 三種情況都能用：公比為負時 $r^n$ 的正負看 $n$ 的奇偶；公比是分數時分母 $r-1$ 也是分數，先把分母通分再除。' },
    'L1.sumToTerm': { f: function (p) { return !!p.ans.isAP; }, why: '$a_n=S_n-S_{n-1}$ 只對 $n\\ge2$ 成立，$a_1=S_1$ 要另外算。$S_n$ 沒有常數項時 $a_1$ 恰好符合通式、數列是等差；有常數項 $c\\ne0$ 時 $a_1$ 多了 $c$、不符合通式，就不是等差。' },
    'L1.telescope': { f: function (p) { return p.a === 1; }, why: '$\\dfrac{1}{(ak+b)(ak+a+b)}=\\dfrac{1}{a}\\left(\\dfrac{1}{ak+b}-\\dfrac{1}{ak+a+b}\\right)$：兩個分母相差 $a$，拆開後要乘 $\\dfrac1a$。相差 $1$ 時係數是 $1$、最容易忘的是相差 $2$ 或 $3$ 時前面那個 $\\dfrac12$、$\\dfrac13$。' },
    'L2.sumFromSn': { f: function (p) { return !!p.ans.isGP; }, why: '$S_n=A\\cdot b^n+C$：$n\\ge2$ 時 $a_n=A(b-1)b^{n-1}$ 是等比；$a_1=Ab+C$ 只有在 $C=-A$ 時才等於 $A(b-1)$、整個數列才是等比，否則第一項要分開寫。' },
    'L2.oddEvenGP': { f: function (p) { return sign3(p.ans.r); }, why: '偶數項的和 $=r\\times$ 奇數項的和，所以 $r=\\dfrac{E}{O}$：兩個和同號則 $r\\gt0$、異號則 $r\\lt0$。公比為負時再由 $O=a_1\\dfrac{r^{2m}-1}{r^2-1}$ 反求 $a_1$，$r^2$ 是正的，不會受符號影響。' },
    'L2.snRecur': { f: function (p) { return p.al > 0; }, why: '$S_n=\\alpha a_n+\\beta$ 都用 $a_n=S_n-S_{n-1}$ 消掉 $S$，得 $a_n=\\dfrac{\\alpha}{\\alpha-1}a_{n-1}$：$\\alpha\\gt1$ 時公比大於 $1$（數列越來越大），$\\alpha\\lt0$ 時公比在 $0$ 與 $1$ 之間（越來越小）——公比由係數決定，首項一律由 $n=1$ 代回求。' },
    'L1.gpMiddle': { f: function (p) { return p.kind; }, why: '設三數為 $\\dfrac ar,\\ a,\\ ar$：乘積永遠先給出中間項 $a$。「三數之和」給的是 $a\\left(\\dfrac1r+1+r\\right)$、「頭尾兩數之和」給的是 $a\\left(\\dfrac1r+r\\right)$，差一個 $a$，兩種都化成 $r+\\dfrac1r$ 的二次方程式。' },
    'L2.kOver2k': { f: function (p) { return p.base; }, why: '分母是 $2^k$ 或 $3^k$，錯位相減都是「$S$ 減去 $\\dfrac1{\\text{底}}S$」：底數換了，相減後留下的等比級數公比與最後一項的分母都跟著換，做法完全一樣。' },
    'L2.groupSeq': { f: function (p) { return p.kind; }, why: '分群數列先算「第 $N$ 項在第幾群、群內第幾個」（用 $1+2+\\cdots+K\\ge N$）；問「第 $N$ 項是多少」只要定位，問「前 $N$ 項和」還要把前面完整的群整群加起來再加零頭。' },
    'L2.annuity': { f: function (p) { return !!p.begin; }, why: '每期期末存：最後一筆不生息，本利和 $=D\\dfrac{(1+i)^n-1}{i}$；每期期初存：每一筆都多生一期利息，整個再乘 $(1+i)$。差的就是那一個 $(1+i)$。' },
    'L3.gpEndsSumN': { f: function (p) { return p.r < 0; }, why: '$S=\\dfrac{a_1-a_nr}{1-r}$ 對正負公比都一樣，先解出 $r$，再由 $a_1r^{n-1}=a_n$ 定 $n$；公比為負時 $a_n$ 與 $a_1$ 同號或異號，直接告訴你 $n-1$ 是偶數還是奇數，可以拿來檢查 $n$ 有沒有算錯。' },
    'L3.fiveAP': { f: function (p) { return p.v; }, why: '令 $t=d^2$ 得二次方程式，兩個 $t$ 都是正的：問「$d$ 所有可能值」時每個 $t$ 開根號都給正負兩個；加了「公差為正整數」，就只留下完全平方的那個 $t$ 且取正根。' },
    'L3.recurGuess': { f: function (p) { return p.fam; }, why: '前幾項猜出 $a_n=An^2$ 或 $a_n=An(n+1)$ 後，都要用遞迴式驗證；差別在一個多了常數項 $+A$、一個沒有——代回時看 $\\dfrac{n+2}{n}a_n$ 差多少就知道是哪一家。' },
    'L3.diagonalGrid': { f: function (p) { return p.v; }, why: '斜線編號的格子：第 $k$ 條斜線有 $k$ 格，前 $k$ 條共 $\\dfrac{k(k+1)}{2}$ 格。由編號找位置是「解 $\\dfrac{k(k+1)}{2}\\ge N$」，由位置找編號是「算前 $k-1$ 條的總數再加上斜線內的序號」，兩題互為反問。' },
    'L3.gpRatioSeries': { f: function (p) { return p.v; }, why: '不管分子從 $r^2$、$r$ 還是 $1$ 開始，都是「公比 $r^2$ 的等比級數 ÷ 公比 $r$ 的等比級數」，$r^{2N}-1=(r^N-1)(r^N+1)$ 一約，剩下的只是首項不同造成的一個因子 $r$ 或 $1$。' },
    'L3.sigmaFactorForm': { f: function (p) { return p.v; }, why: '同一條公式，一題要你把它「算出來」（展開、套三個求和公式、因式分解），一題只要你「用它」（代 $n=1$ 驗證、代 $n$ 求值）。段考兩種都考，先會用再會推。' },
    'L3.snRelationProd': { f: function (p) { return p.c; }, why: '$cS_n=(n+c-1)a_n$ 相減得 $\\dfrac{a_n}{a_{n-1}}=\\dfrac{n+c-2}{n-1}$：$c=2$ 疊縮成 $n$、$c=3$ 成 $\\dfrac{n(n+1)}{2}$、$c=4$ 成 $\\dfrac{n(n+1)(n+2)}{6}$，係數 $c$ 每大 $1$，一般項就多一個因子。' },
    'L3.altStaggered': { f: function (p) { return p.v; }, why: '錯位相減後中間那串等比級數的係數是「相鄰係數的差」：係數 $k$ 差 $1$、係數 $2k-1$ 差 $2$，所以第二型要多乘一個 $2$；最後一項與首項的處理完全一樣。' }
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr } };
}));
