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

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* 1-1 等差：由兩項決定整個數列 */
  L1.arTerm = function (r) {
    var p = r.int(2, 6), q = p + r.int(3, 8), d = r.nz(-5, 6), a1 = r.int(-10, 15), m = r.int(15, 40);
    var ap = a1 + (p - 1) * d, aq = a1 + (q - 1) * d, am = a1 + (m - 1) * d;
    return { q: '設 ' + T(sq(AN)) + ' 為等差數列，已知 ' + T('a_{' + p + '}=' + ap) + '、' + T('a_{' + q + '}=' + aq) + '。求公差 ' + T('d') + '、首項 ' + T('a_1') + '、一般項 ' + T(AN) + ' 與 ' + T('a_{' + m + '}') + '。',
             a: T('d=' + d) + '、' + T('a_1=' + a1) + '、' + T(AN + '=' + lin(d, a1 - d)) + '、' + T('a_{' + m + '}=' + am),
             h: '兩項相減：$a_{' + q + '}-a_{' + p + '}=' + (q - p) + 'd$；再用 $a_n=a_1+(n-1)d$。',
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
             h: '兩項相除：$\\dfrac{a_{' + q + '}}{a_{' + p + '}}=r^{3}$，立方根唯一（不會有正負兩解）。',
             p: { p: p, q: q, ap: ap, aq: aq, m: m, ans: { r: rr, a1: a1, am: am } } };
  };

  /* 1-5 三數成等比：乘法版對稱設法 */
  L1.gpMiddle = function (r) {
    var rho = r.pick([2, 3, 4]), k = r.int(1, 4), a = rho * k * (r() < 0.75 ? 1 : -1);
    var x = [a / rho, a, a * rho]; x.sort(function (u, v) { return u - v; });
    var P = x[0] * x[1] * x[2], S = x[0] + x[1] + x[2];
    return { q: '三個數成等比數列，其乘積為 ' + T(String(P)) + '、和為 ' + T(String(S)) + '，求此三數。',
             a: T(x.join(',\\ ')) + '（或逆序）',
             h: '設三數為 $\\dfrac ar,\\ a,\\ ar$：乘積 $=a^3$ 先定出中間項 $a=' + a + '$，再由和解 $r+\\dfrac1r$。',
             p: { P: P, S: S, ans: x } };
  };

  /* 1-6 平均成長率（幾何平均） */
  var GROWTH = [
    [20, [-20, 20, 80]], [20, [-40, 20, 140]], [20, [-10, 20, 60]], [20, [-40, 20, 20, 60, 80]], [20, [-20, 80]], [20, [-10, 60]], [20, [-40, 140]],
    [10, [-45, 120]], [30, [-35, 160]], [50, [-10, 150]], [50, [-25, 200]], [50, [25, 80]], [40, [-30, 180]], [40, [-2, 100]], [40, [12, 75]], [0, [-20, 25]], [0, [-50, 100]], [0, [-20, -20, 25, 25]], [50, [-25, 200, 50]], [10, [10, 10, 10]]
  ];
  L1.growth = function (r) {
    var g = r.pick(GROWTH), rates = g[1], ans = g[0];
    var txt = rates.map(function (x) { return '$' + x + '\\%$'; }).join('、');
    return { q: '某公司連續 ' + T(String(rates.length)) + ' 年的營收成長率依序為 ' + txt + '。若這 ' + T(String(rates.length)) + ' 年的平均成長率為 ' + T('r\\%') + '，求 ' + T('r') + '。',
             a: T('r=' + ans),
             h: '「平均成長率」是幾何平均：$(1+r)^{' + rates.length + '}=' + rates.map(function (x) { return '(1' + (x < 0 ? '-' : '+') + Math.abs(x) / 100 + ')'; }).join('') + '$。',
             p: { rates: rates, ans: ans } };
  };

  /* 1-7 一階線性遞迴：不動點法 */
  L1.recurLinear = function (r) {
    var pp = r.pick([2, 3, -2, 4, -3]), qq = r.nz(-6, 6), a1 = r.int(-3, 6), k = r.int(4, 6);
    var xs = F(qq, 1 - pp), c = Fr.sub(F(a1), xs);
    if (c.n === 0) a1 += 1, c = Fr.sub(F(a1), xs);
    var ak = Fr.add(Fr.mul(c, F(ipow(pp, k - 1))), xs);
    var gen = termF(c, '\\cdot' + signedNum(pp) + '^{\\,n-1}', true) + termF(xs, '', false);
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
    var genTex = [a1 === 1 ? 'n' : a1 + 'n', a1 % 2 === 0 ? (a1 / 2 === 1 ? 'n(n+1)' : (a1 / 2) + 'n(n+1)') : '\\dfrac{' + a1 + 'n(n+1)}{2}', a1 === 1 ? '\\dfrac1n' : '\\dfrac{' + a1 + '}{n}', '\\dfrac{' + (2 * a1) + '}{n(n+1)}'][kind];
    var am = [F(a1 * m), F(a1 * m * (m + 1), 2), F(a1, m), F(2 * a1, m * (m + 1))][kind];
    return { q: '設 ' + T('a_1=' + a1) + '，且 ' + T(AN1 + '=' + ratio + '\\,a_n') + '（' + T('n\\ge1') + '）。求一般項 ' + T(AN) + ' 與 ' + T('a_{' + m + '}') + '。',
             a: T(AN + '=' + genTex) + '，' + T('a_{' + m + '}=' + Fr.tex(am)),
             h: '$a_n=a_1\\cdot\\dfrac{a_2}{a_1}\\cdot\\dfrac{a_3}{a_2}\\cdots\\dfrac{a_n}{a_{n-1}}$，分子分母交錯相消，只留頭尾。',
             p: { kind: kind, a1: a1, m: m, ans: fr2(am) } };
  };

  /* 1-10 分式型遞迴：取倒數 */
  L1.recurRecip = function (r) {
    var s = r.int(1, 3), k = r.int(1, 4), m = r.int(10, 100);
    /* a1 = 1/s, a_{n+1} = a_n/(k a_n + 1) ⟹ 1/a_n = s + k(n-1) */
    var a2 = F(1, s + k), a3 = F(1, s + 2 * k), am = F(1, s + k * (m - 1));
    return { q: '設 ' + T('a_1=' + Fr.tex(F(1, s))) + '、' + T(AN1 + '=\\dfrac{a_n}{' + (k === 1 ? '' : k) + 'a_n+1}') + '。(1) 求 ' + T('a_2,a_3') + '。(2) 求一般項 ' + T(AN) + '。(3) 求 ' + T('a_{' + m + '}') + '。',
             a: '(1) ' + T(Fr.tex(a2) + ',\\ ' + Fr.tex(a3)) + '　(2) ' + T(AN + '=\\dfrac{1}{' + lin(k, s - k) + '}') + '　(3) ' + T(Fr.tex(am)),
             h: '兩邊取倒數：$\\dfrac1{a_{n+1}}=\\dfrac1{a_n}+' + k + '$，所以 $\\left\\langle\\dfrac1{a_n}\\right\\rangle$ 是公差 $' + k + '$ 的等差數列。',
             p: { s: s, k: k, m: m, ans: { a2: fr2(a2), a3: fr2(a3), am: fr2(am) } } };
  };

  /* 1-11 週期數列 */
  L1.periodic = function (r) {
    var kind = r.int(0, 2), a1 = r.pick([2, 3, 4, 5, -2, -3]), N = r.pick([100, 101, 200, 2025, 2026]);
    var rule = ['\\dfrac{1}{1-a_n}', '1-\\dfrac{1}{a_n}', '\\dfrac{a_n-1}{a_n+1}'][kind];
    var step = function (x) { return kind === 0 ? Fr.div(F(1), Fr.sub(F(1), x)) : kind === 1 ? Fr.sub(F(1), Fr.div(F(1), x)) : Fr.div(Fr.sub(x, F(1)), Fr.add(x, F(1))); };
    var seq = [F(a1)]; for (var i = 0; i < 5; i++) seq.push(step(seq[i]));
    var per = Fr.eq(seq[3], seq[0]) ? 3 : 4;
    var cyc = seq.slice(0, per), cs = SUMF(0, per - 1, function (i) { return cyc[i]; });
    var aN = cyc[(N - 1) % per], full = Math.floor(N / per), rem = N % per;
    var SN = Fr.add(Fr.mul(F(full), cs), SUMF(0, rem - 1, function (i) { return cyc[i]; }));
    return { q: '設 ' + T('a_1=' + a1) + '、' + T(AN1 + '=' + rule) + '。(1) 求 ' + T('a_2,a_3,a_4') + ' 並說明此數列的週期。(2) 求 ' + T('a_{' + N + '}') + '。(3) 求 ' + T('a_1+a_2+\\cdots+a_{' + N + '}') + '。',
             a: '(1) ' + T(Fr.tex(seq[1]) + ',\\ ' + Fr.tex(seq[2]) + ',\\ ' + Fr.tex(seq[3])) + '，週期 ' + T(String(per)) + '　(2) ' + T(Fr.tex(aN)) + '　(3) ' + T(Fr.tex(SN)),
             h: '算到某一項與 $a_1$ 相同就找到週期；$' + N + '=' + per + '\\times' + full + '+' + rem + '$，用「幾個完整週期＋零頭」。',
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
             h: '拆成 $' + (al ? al + '\\sum k^2' : '') + (al && be ? (be > 0 ? '+' : '') : '') + (be ? (Math.abs(be) === 1 ? (be < 0 ? '-' : '') : be) + '\\sum k' : '') + (ga ? (ga > 0 ? '+' : '-') + Math.abs(ga) + '\\cdot' + N : '') + '$，套 $\\sum k=\\frac{n(n+1)}2$、$\\sum k^2=\\frac{n(n+1)(2n+1)}6$。',
             p: { N: N, al: al, be: be, ga: ga, ans: val } };
  };

  /* 2-2 Σ 公式：以 n 表示 */
  L1.sigmaFormula = function (r) {
    var a = r.int(1, 4), b = r.nz(-3, 3);
    /* Σ k(ak+b) = n(n+1)(2an + a + 3b)/6 */
    var c3 = F(2 * a, 6), c2 = F(3 * a + 3 * b, 6), c1 = F(a + 3 * b, 6);
    var inner = lin(2 * a, a + 3 * b), g = gcd(gcd(2 * a, Math.abs(a + 3 * b)), 6);
    var innerR = lin(2 * a / g, (a + 3 * b) / g), den = 6 / g;
    var tex = den === 1 ? 'n(n+1)(' + innerR + ')' : '\\dfrac{n(n+1)(' + innerR + ')}{' + den + '}';
    if ((a + 3 * b) === 0) tex = (2 * a / g === 1 ? '' : (2 * a / g)) + (den === 1 ? 'n^2(n+1)' : '\\dfrac{n^2(n+1)}{' + den + '}');
    return { q: '求 ' + T(sigma(1, 'n', 'k(' + lin(a, b, 'k') + ')')) + '（以 ' + T('n') + ' 表示，化到最簡）。',
             a: T(tex),
             h: '$=' + (a === 1 ? '' : a) + '\\sum k^2' + (b > 0 ? '+' : '-') + (Math.abs(b) === 1 ? '' : Math.abs(b)) + '\\sum k$，提出公因式 $\\dfrac{n(n+1)}{6}$。代 $n=1$ 驗算：左式 $=' + (a + b) + '$。',
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
    return { q: '等比數列首項 ' + T(String(a1)) + '、公比 ' + T(Fr.tex(rf)) + '，求前 ' + T(String(N)) + ' 項的和 ' + T('S_{' + N + '}') + '。',
             a: T('S_{' + N + '}=' + Fr.tex(S)),
             h: '$S_n=\\dfrac{a_1(1-r^{n})}{1-r}$；公比為負時 $r^{' + N + '}$ 的正負號要看 $' + N + '$ 是奇是偶。',
             p: { a1: a1, r: fr2(rf), N: N, ans: fr2(S) } };
  };

  /* 2-6 等比級數的分段和 */
  L1.gpBlocks = function (r) {
    var A = r.pick([3, 5, 6, 10, 12]) * r.pick([1, 2]), t = r.pick([2, 3, 4, 5]), n = r.pick(['n', 5, 10]);
    var B = A * t, S3 = A + B + B * t;
    var nn = n === 'n' ? 'n' : String(n), n2 = n === 'n' ? '2n' : String(2 * n), n3 = n === 'n' ? '3n' : String(3 * n);
    return { q: '設等比數列的前 ' + T(nn) + ' 項和 ' + T('S_{' + nn + '}=' + A) + '、前 ' + T(n2) + ' 項和 ' + T('S_{' + n2 + '}=' + (A + B)) + '。求前 ' + T(n3) + ' 項和 ' + T('S_{' + n3 + '}') + '。',
             a: T('S_{' + n3 + '}=' + S3),
             h: '三段和 $S_{' + nn + '},\\ S_{' + n2 + '}-S_{' + nn + '},\\ S_{' + n3 + '}-S_{' + n2 + '}$ 自己也成等比（公比 $r^{' + nn + '}=' + t + '$）。',
             p: { A: A, S2: A + B, ans: S3 } };
  };

  /* 2-7 裂項相消 */
  L1.telescope = function (r) {
    var a = r.pick([1, 2, 3]), b = r.int(0, 2); if (a + b === 0) b = 1;
    var N = r.int(8, 30);
    var S = SUMF(1, N, function (k) { return F(1, (a * k + b) * (a * k + a + b)); });
    var t = function (k) { return '\\dfrac{1}{' + (a * k + b) + '\\times' + (a * k + a + b) + '}'; };
    return { q: '求 ' + T(t(1) + '+' + t(2) + '+' + t(3) + '+\\cdots+' + t(N)) + '（化為最簡分數）。',
             a: T(Fr.tex(S)),
             h: '$\\dfrac{1}{(' + lin(a, b, 'k') + ')(' + lin(a, a + b, 'k') + ')}=' + (a === 1 ? '' : '\\dfrac1{' + a + '}') + '\\left(\\dfrac1{' + lin(a, b, 'k') + '}-\\dfrac1{' + lin(a, a + b, 'k') + '}\\right)$，中間全部相消。',
             p: { a: a, b: b, N: N, ans: fr2(S) } };
  };

  /* 2-8 錯位相減 */
  L1.staggered = function (r) {
    var rr = r.pick([2, 3]), N = r.int(5, 8);
    var S = SUM(1, N, function (k) { return k * ipow(rr, k - 1); });
    var terms = ['1', '2\\times' + rr, '3\\times' + rr + '^2'];
    return { q: '求 ' + T(terms.join('+') + '+\\cdots+' + N + '\\times' + rr + '^{' + (N - 1) + '}') + '。',
             a: T(String(S)),
             h: '設 $S$，兩邊乘 $' + rr + '$ 後錯一位相減：$(1-' + rr + ')S=1+' + rr + '+\\cdots+' + rr + '^{' + (N - 1) + '}-' + N + '\\cdot' + rr + '^{' + N + '}$。',
             p: { r: rr, N: N, ans: S } };
  };

  /* 2-9 由 S_n 反求 a_n */
  L1.sumToTerm = function (r) {
    var a = r.nz(-3, 4), b = r.nz(-5, 6), c = r() < 0.5 ? 0 : r.nz(-4, 4);
    var Sn = quad(a, b, c), a1 = a + b + c, coef = [2 * a, b - a];
    return { q: '已知數列 ' + T(sq(AN)) + ' 的前 ' + T('n') + ' 項和為 ' + T('S_n=' + Sn) + '。求 ' + T('a_1') + '、' + T('a_n') + '（' + T('n\\ge2') + '），並判斷 ' + T(sq(AN)) + ' 是否為等差數列。',
             a: T('a_1=' + a1) + '、' + T('n\\ge2' + '\\text{ 時 }a_n=' + lin(coef[0], coef[1])) + '；' + (c === 0 ? '是等差數列（' + T('a_1') + ' 也符合該式）' : '不是等差數列（' + T('a_1=' + a1) + ' 不符合 ' + T(lin(coef[0], coef[1])) + '，第一項脫隊）'),
             h: '$a_1=S_1$；$n\\ge2$ 時 $a_n=S_n-S_{n-1}$。$S_n$ 有常數項 $' + c + '$，第一項' + (c === 0 ? '合得起來' : '就會脫隊') + '。',
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

  /* 2-11 複利與單利 */
  L1.compound = function (r) {
    var i = r.pick([2, 3, 4, 5, 10]), n = r.pick([2, 3]), P = n === 2 ? r.pick([10000, 20000, 50000]) : 1000000;
    var comp = P; for (var j = 0; j < n; j++) comp = comp * (100 + i) / 100;
    comp = Math.round(comp);
    var simple = P + P * i * n / 100;
    return { q: '將 ' + T(String(P)) + ' 元存入銀行，年利率 ' + T(i + '\\%') + '。(1) 若每年複利一次，' + T(String(n)) + ' 年後的本利和為多少元？(2) 若改用單利，' + T(String(n)) + ' 年後的本利和為多少元？兩者相差多少？',
             a: '(1) ' + T(String(comp)) + ' 元　(2) ' + T(String(simple)) + ' 元，相差 ' + T(String(comp - simple)) + ' 元',
             h: '複利：$P(1+' + (i / 100) + ')^{' + n + '}$；單利：$P(1+' + (i / 100) + '\\times' + n + ')$。',
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
             h: '遞推步驟的目標永遠是：$\\big(n=k\\text{ 的右式}\\big)+\\big(\\text{第 }k+1\\text{ 項}\\big)=\\big(n=k+1\\text{ 的右式}\\big)$，把 $n$ 換成 $k+1$ 寫出來即可。',
             p: { id: I.id, m: m, ans: { gm: fr2(gmF) } } };
  };

  /* 3-2 歸納法證整除：f(k+1) 用 f(k) 表示 */
  var DIV = [  /* f(n) = a·b^n + c n + d 恆為 m 的倍數 */
    [1, 4, 15, -1, 9], [1, 7, 0, -1, 6], [1, 5, 0, 3, 4], [1, 9, 0, -1, 8], [2, 4, 0, 1, 3], [1, 10, 9, -1, 9], [1, 7, 3, -1, 9], [1, 3, 2, -1, 4], [1, 8, 7, -1, 7], [1, 5, 4, 3, 4], [1, 4, 0, 2, 3]
  ];
  L1.divisible = function (r) {
    var D = r.pick(DIV), a = D[0], b = D[1], c = D[2], d = D[3], m = D[4];
    var fT = (a === 1 ? '' : a + '\\cdot') + b + '^{\\,n}' + term(c, 'n', false) + term(d, '', false);
    var f1 = a * b + c + d;
    /* f(k+1) = b f(k) + c(1-b)k + (c + d(1-b)) ；f(k)=m t */
    var ck = c * (1 - b) / m, c0 = (c + d * (1 - b)) / m;
    var inner = term(b, 't', true) + term(ck, 'k', false) + term(c0, '', false);
    return { q: '已知對所有正整數 ' + T('n') + '，' + T('f(n)=' + fT) + ' 恆為 ' + T(String(m)) + ' 的倍數。(1) 求 ' + T('f(1)') + '。(2) 用歸納法證明時，設 ' + T('f(k)=' + m + 't') + '（' + T('t') + ' 為整數），把 ' + T('f(k+1)') + ' 整理成 ' + T(m + '\\times(\\ \\ \\ )') + '，求括號內的式子（以 ' + T('t,k') + ' 表示）。',
             a: '(1) ' + T('f(1)=' + f1) + '　(2) ' + T(inner),
             h: '$f(k+1)=' + b + '\\,f(k)' + (c ? (c * (1 - b) > 0 ? '+' : '-') + Math.abs(c * (1 - b)) + 'k' : '') + ((c + d * (1 - b)) ? ((c + d * (1 - b)) > 0 ? '+' : '-') + Math.abs(c + d * (1 - b)) : '') + '$：先寫出 $' + b + 'f(k)$，再看差多少。',
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
             h: '$S_{' + m + '}=S_{' + n + '}$ ⟹ $a_{' + (m + 1) + '}+\\cdots+a_{' + n + '}=0$，這 $' + (n - m) + '$ 項的正中間 $a_{' + zero + '}=0$；對稱軸在 $' + zero + '$，故 $a_p+a_q=0$ 只要 $p+q=' + (m + n + 1) + '$。',
             p: { m: m, n: n, p: p, q: q, A: A, ans: { kmax: kmax, d: d, Smax: Smax } } };
  };

  /* 2-2 前 n 項和之比 ⟹ 第 k 項之比 */
  L2.sumRatio = function (r) {
    var a = r.int(1, 5), b = r.int(-3, 7), c = r.int(1, 5), d = r.int(-3, 9), k = r.int(4, 15);
    if (a * d === b * c) d += 1;
    var num = a * (2 * k - 1) + b, den = c * (2 * k - 1) + d; if (den <= 0) den = c * (2 * k - 1) + (d = Math.abs(d) + 1);
    var g = gcd(num, den) || 1;
    return { q: '兩等差數列 ' + T(sq(AN)) + '、' + T(sq('b_n')) + ' 的前 ' + T('n') + ' 項和分別為 ' + T('S_n,T_n') + '，且 ' + T('\\dfrac{S_n}{T_n}=\\dfrac{' + lin(a, b) + '}{' + lin(c, d) + '}') + '。求 ' + T('\\dfrac{a_{' + k + '}}{b_{' + k + '}}') + '。',
             a: T('\\dfrac{' + (num / g) + '}{' + (den / g) + '}'),
             h: '$a_k=\\dfrac{S_{2k-1}}{2k-1}$（奇數項的和＝項數 $\\times$ 中間項），所以第 $' + k + '$ 項之比＝前 $' + (2 * k - 1) + '$ 項和之比。',
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
             h: '$\\langle a_n^{\\,2}\\rangle$ 也是等比，公比 $r^2$：$\\dfrac{a_{' + q + '}^{\\,2}}{a_{' + p + '}^{\\,2}}=r^{8}=' + ipow(s, 4) + '$ ⟹ $r^2=' + s + '$，全程不必決定 $r$ 的正負。',
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
    return { q: '已知數列 ' + T(sq(AN)) + ' 的前 ' + T('n') + ' 項和為 ' + T('S_n=' + Sn) + '。求 ' + T('a_1') + '、' + T('a_{' + m + '}') + '，並判斷 ' + T(sq(AN)) + ' 是否為等比數列。',
             a: T('a_1=' + a1) + '、' + T('a_{' + m + '}=' + am) + '；' + (isGP ? '是等比數列（' + T('a_n=' + gen) + ' 對所有 ' + T('n') + ' 成立）' : '不是（' + T('n\\ge2') + ' 時 ' + T('a_n=' + gen) + '，但 ' + T('a_1=' + a1 + '\\ne' + (A * (b - 1))) + '）'),
             h: '$a_n=S_n-S_{n-1}$ 只對 $n\\ge2$ 成立；$S_n$ 的常數項 $' + C + '$ 就是第一項脫隊的原因。',
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
             h: '$c_nd_n=(' + lin(al, be) + ')(' + lin(ga, de) + ')$ 是 $n$ 的二次式，乘開後套 $\\sum n^2,\\sum n,\\sum1$；不要用錯位相減（那是給等差 $\\times$ 等比用的）。',
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
    return { q: '將等差數列 ' + T('\\dfrac1{' + m + '},\\dfrac2{' + m + '},\\dfrac3{' + m + '},\\dots,\\dfrac{' + N + '}{' + m + '}') + ' 的每一項用無條件捨去法取到整數，依序排成 ' + T(sq('b_n')) + '，求 ' + T('b_1+b_2+\\cdots+b_{' + N + '}') + '。',
             a: T(String(S)),
             h: '$b_k=\\left\\lfloor\\dfrac k{' + m + '}\\right\\rfloor$ 每 $' + m + '$ 個一群：值 $1$ 有 $' + m + '$ 個、值 $2$ 有 $' + m + '$ 個……最後一群（值 $' + Math.floor(N / m) + '$）只有 $' + (N - m * Math.floor(N / m) + 1) + '$ 個。',
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
    var kind = r.int(0, 1), N = r.int(5, 10);
    var S = SUMF(1, N, function (k) { return F(kind === 0 ? k : 2 * k - 1, ipow(2, k)); });
    var body = kind === 0 ? '\\dfrac{k}{2^{k}}' : '\\dfrac{2k-1}{2^{k}}';
    var closed = kind === 0 ? '2-\\dfrac{n+2}{2^{n}}' : '3-\\dfrac{2n+3}{2^{n}}';
    return { q: '求 ' + T(sigma(1, N, body)) + '（化為最簡分數）。',
             a: T(Fr.tex(S)),
             h: '等差 $\\div$ 等比＝等差 $\\times$ 等比（公比 $\\frac12$），用錯位相減；通式 $\\sum_{k=1}^{n}' + body + '=' + closed + '$，代 $n=' + N + '$。',
             p: { kind: kind, N: N, ans: fr2(S) } };
  };

  /* 2-12 裂項反求項數 */
  L2.telescopeN = function (r) {
    var kind = r.int(0, 1), n = r.int(20, 1200);
    var val = kind === 0 ? F(n, 2 * n + 1) : F(n, n + 1);
    var lhs = kind === 0 ? '\\dfrac13+\\dfrac1{15}+\\dfrac1{35}+\\cdots+\\dfrac1{(2n-1)(2n+1)}' : '\\dfrac1{1\\cdot2}+\\dfrac1{2\\cdot3}+\\dfrac1{3\\cdot4}+\\cdots+\\dfrac1{n(n+1)}';
    return { q: '已知 ' + T(lhs + '=' + Fr.tex(val)) + '，求正整數 ' + T('n') + '。',
             a: T('n=' + n),
             h: '裂項後和為 $' + (kind === 0 ? '\\dfrac{n}{2n+1}' : '\\dfrac{n}{n+1}') + '$；分數已是最簡，直接比對分子分母。',
             p: { kind: kind, val: fr2(val), ans: n } };
  };

  /* 2-13 混合型遞迴：a_{n+1} = p a_n + q^n */
  L2.recurMixed = function (r) {
    var p = r.pick([2, 3]), q = r.pick([2, 3, 4, 5]); if (q === p) q = p + 1;
    var a1 = r.int(1, 6), m = r.int(4, 6);
    var a = [a1]; for (var i = 1; i < m; i++) a.push(p * a[i - 1] + ipow(q, i));
    /* a_n = (a1 - q/(q-p)) p^{n-1} + q^n/(q-p) */
    var c = Fr.sub(F(a1), F(q, q - p)), e = F(1, q - p);
    var gen = termF(c, '\\cdot' + p + '^{\\,n-1}', true) + termF(e, '\\cdot' + q + '^{\\,n}', false);
    return { q: '設 ' + T('a_1=' + a1) + '，且 ' + T(AN1 + '=' + p + 'a_n+' + q + '^{\\,n}') + '。(1) 求 ' + T('a_2,a_3') + '。(2) 求 ' + T('a_{' + m + '}') + '。(3) 求一般項 ' + T(AN) + '。',
             a: '(1) ' + T(a[1] + ',\\ ' + a[2]) + '　(2) ' + T(String(a[m - 1])) + '　(3) ' + T(AN + '=' + gen),
             h: '兩邊除以 $' + q + '^{\\,n+1}$，令 $b_n=\\dfrac{a_n}{' + q + '^{\\,n}}$ 得 $b_{n+1}=\\dfrac{' + p + '}{' + q + '}b_n+\\dfrac1{' + q + '}$，回到一階線性遞迴（不動點 $\\dfrac1{' + (q - p) + '}$）。',
             p: { p: p, q: q, a1: a1, m: m, ans: { a2: a[1], a3: a[2], am: a[m - 1], c: fr2(c), e: fr2(e) } } };
  };

  /* 2-14 零存整付（年金） */
  L2.annuity = function (r) {
    var D = r.pick([10000, 20000, 50000]), i = r.pick([2, 3, 5]), n = r.pick([4, 5, 6]), begin = r() < 0.5;
    var g = Math.round(Math.pow(1 + i / 100, n) * 10000) / 10000;    /* 題目給的近似值 */
    var val = D * (g - 1) / (i / 100) * (begin ? (1 + i / 100) : 1);
    var ans = Math.round(val);
    return { q: '某人自今年起每年 ' + (begin ? '1 月 1 日' : '12 月 31 日') + ' 存入銀行 ' + T(String(D)) + ' 元，年利率 ' + T(i + '\\%') + '、每年複利一次。連續存 ' + T(String(n)) + ' 年，求第 ' + T(String(n)) + ' 年 12 月 31 日結算時的本利和（取到整數元；已知 ' + T('(' + (1 + i / 100) + ')^{' + n + '}\\approx' + g) + '）。',
             a: '約 ' + T(String(ans)) + ' 元',
             h: (begin ? '各筆分別滾 $' + n + ',' + (n - 1) + ',\\dots,1$ 年' : '各筆分別滾 $' + (n - 1) + ',' + (n - 2) + ',\\dots,0$ 年') + '，本利和是公比 $' + (1 + i / 100) + '$ 的等比級數：$' + D + '\\cdot\\dfrac{' + (begin ? (1 + i / 100) + '\\left[' : '\\left[') + (1 + i / 100) + '^{' + n + '}-1\\right]}{' + (i / 100) + '}$。',
             p: { D: D, i: i, n: n, begin: begin, g: g, ans: ans } };
  };

  /* 2-15 由 S_n 與 a_n 的關係求一般項 */
  L2.snRecur = function (r) {
    var kind = r.int(0, 2), c = r.pick([2, 4, 6, 8, 10, 12]), a1, ratio, rel;
    if (kind === 0) { rel = 'S_n=' + c + '-a_n'; a1 = F(c, 2); ratio = F(1, 2); }
    else if (kind === 1) { rel = 'S_n=2a_n-' + c; a1 = F(c); ratio = F(2); }
    else { rel = 'S_n=3a_n-' + c; a1 = F(c, 2); ratio = F(3, 2); }
    var a2 = Fr.mul(a1, ratio), a3 = Fr.mul(a2, ratio);
    var gen = Fr.tex(a1) + '\\cdot\\left(' + Fr.tex(ratio) + '\\right)^{n-1}';
    if (kind === 1) gen = c + '\\cdot2^{\\,n-1}';
    return { q: '設數列 ' + T(sq(AN)) + ' 的前 ' + T('n') + ' 項和為 ' + T('S_n') + '，且對所有正整數 ' + T('n') + '，' + T(rel) + ' 恆成立。求 ' + T('a_1,a_2,a_3') + ' 與一般項 ' + T(AN) + '。',
             a: T('a_1=' + Fr.tex(a1) + ',\\ a_2=' + Fr.tex(a2) + ',\\ a_3=' + Fr.tex(a3)) + '，' + T(AN + '=' + gen),
             h: '$n=1$ 時 $S_1=a_1$ 先解出 $a_1$；$n\\ge2$ 時兩式相減 $a_n=S_n-S_{n-1}$ 得 $a_n$ 與 $a_{n-1}$ 的關係，是公比 $' + Fr.tex(ratio, true) + '$ 的等比數列。',
             p: { kind: kind, c: c, ans: { a1: fr2(a1), ratio: fr2(ratio), a3: fr2(a3) } } };
  };

  /* 2-16 等比取對數變等差（跨章：對數） */
  L2.logGP = function (r) {
    var u = r.int(1, 2), v = r.pick([1, 2, 3]), N = r.int(5, 12), half = r() < 0.4;
    var vv = half ? F(2 * v + 1, 2) : F(v);      /* 公比 3^{vv} */
    var rTex = half ? (v === 1 ? '3\\sqrt3' : '3^{' + v + '}\\sqrt3') : (v === 1 ? '3' : '3^{' + v + '}');
    var a1Tex = u === 1 ? '3' : '9';
    var S = Fr.add(F(N * u), Fr.mul(vv, F(N * (N - 1), 2)));
    return { q: '設 ' + T('a_1,a_2,\\dots,a_{' + N + '}') + ' 是首項為 ' + T(a1Tex) + '、公比為 ' + T(rTex) + ' 的等比數列，求 ' + T('\\log_3a_1+\\log_3a_2+\\cdots+\\log_3a_{' + N + '}') + '。',
             a: T(Fr.tex(S)),
             h: '$\\log_3a_k=' + u + '+(k-1)\\cdot' + Fr.tex(vv, true) + '$ 是等差數列（等比取 $\\log$ 變等差），用等差級數公式。',
             p: { u: u, v: fr2(vv), N: N, ans: fr2(S) } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['arTerm', '§1 等差：由兩項定數列'], ['arSign', '§1 等差的變號位置'], ['arMiddle', '§1 三數等差：對稱設法'], ['gpTerm', '§1 等比：由兩項求公比'], ['gpMiddle', '§1 三數等比：對稱設法'], ['growth', '§1 平均成長率'],
      ['recurLinear', '§1 一階線性遞迴：不動點'], ['recurSum', '§1 連加型遞迴'], ['recurProd', '§1 連乘型遞迴'], ['recurRecip', '§1 分式遞迴：取倒數'], ['periodic', '§1 週期數列'],
      ['sigmaCalc', '§2 Σ 的計算'], ['sigmaFormula', '§2 Σ 公式：以 n 表示'], ['arSum', '§2 等差級數與中段和'], ['arSumMax', '§2 S_n 何時最大'], ['gpSum', '§2 等比級數'], ['gpBlocks', '§2 等比級數的分段和'],
      ['telescope', '§2 裂項相消'], ['staggered', '§2 錯位相減'], ['sumToTerm', '§2 由 S_n 反求 a_n'], ['absSum', '§2 等差的絕對值和'], ['compound', '§2 複利與單利'],
      ['inductionStep', '§3 歸納法：遞推步驟'], ['divisible', '§3 歸納法證整除']
    ],
    L2: [
      ['arSymm', '§2 S_m=S_n 的對稱性'], ['sumRatio', '§2 前 n 項和之比'], ['oddEvenGP', '§2 奇數項和與偶數項和'], ['gpSquares', '§2 平方後仍是等比'], ['sumFromSn', '§2 S_n 含指數：脫隊'],
      ['weightedRecur', '§2 由 Σ k·a_k 反求單項'], ['prodAP', '§2 等差×等差級數'], ['absQuad', '§2 二次數列的絕對值和'], ['floorSum', '§2 高斯符號分群'], ['groupSeq', '§2 分群數列'],
      ['kOver2k', '§2 等差÷等比'], ['telescopeN', '§2 裂項反求項數'], ['recurMixed', '§1 混合型遞迴'], ['annuity', '§2 零存整付'], ['snRecur', '§2 S_n 與 a_n 的關係式'], ['logGP', '§2 等比取 log 變等差']
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

  return { makeRng: makeRng, L1: L1, L2: L2, META: META, _util: { gcd: gcd, F: F, Fr: Fr } };
}));
