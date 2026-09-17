/* ══════════════════════════════════════════════════════════════
   g10a-ch03 多項式・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示                         p：參數與結構化答案（給 verify_gen03.py 獨立重算）
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
  function T(s) { return '$' + s + '$'; }
  /* ── 整係數多項式工具（係數陣列：最高次在前）── */
  function polyTex(c, v) {
    v = v || 'x'; var n = c.length - 1, s = '', first = true;
    for (var i = 0; i <= n; i++) {
      var k = c[i], e = n - i; if (k === 0) continue;
      var sgn = k < 0 ? '-' : (first ? '' : '+'), ab = Math.abs(k);
      var body = (e === 0) ? String(ab) : ((ab === 1 ? '' : String(ab)) + (e === 1 ? v : v + '^{' + e + '}'));
      s += sgn + body; first = false;
    }
    return s || '0';
  }
  function trim(c) { var i = 0; while (i < c.length - 1 && c[i] === 0) i++; return c.slice(i); }
  function polyMul(a, b) {
    var out = []; for (var i = 0; i < a.length + b.length - 1; i++) out.push(0);
    for (var i2 = 0; i2 < a.length; i2++) for (var j = 0; j < b.length; j++) out[i2 + j] += a[i2] * b[j];
    return out;
  }
  function polyAdd(a, b) {
    var n = Math.max(a.length, b.length), out = [];
    for (var i = 0; i < n; i++) { var x = a[a.length - n + i] || 0, y = b[b.length - n + i] || 0; out.push(x + y); }
    return trim(out);
  }
  function polyScale(a, k) { return a.map(function (v) { return v * k; }); }
  function polyEval(c, x) { var v = 0; for (var i = 0; i < c.length; i++) v = v * x + c[i]; return v; }
  function polyShift(c, h) {   /* f(x+h) 的係數 */
    var out = [c[0]];
    for (var i = 1; i < c.length; i++) out = polyAdd(polyMul(out, [1, h]), [c[i]]);
    return out;
  }
  function polyDeriv(c) { var n = c.length - 1, out = []; for (var i = 0; i < n; i++) out.push(c[i] * (n - i)); return out.length ? out : [0]; }
  function synth(c, k) {        /* 除以 (x-k)：{q, r} */
    var q = [c[0]]; for (var i = 1; i < c.length - 1; i++) q.push(q[i - 1] * k + c[i]);
    return { q: q, r: q[q.length - 1] * k + c[c.length - 1] };
  }
  function linTex(p) { return polyTex(p); }     /* 一次式 [m,n] */
  function factTex(r) { return r === 0 ? 'x' : '(x' + (r > 0 ? '-' + r : '+' + (-r)) + ')'; }
  function term(coef, v, first) {
    if (coef === 0) return '';
    var sgn = coef < 0 ? '-' : (first ? '' : '+');
    var ab = Math.abs(coef);
    return sgn + (ab === 1 && v ? '' : ab) + v;
  }
  /* ── 不等式解集：factors=[{r,m}]（整數根與重數），lead=±1，rel ∈ '<','<=','>','>=' ── */
  /* ────────── 提示專用：把本題的數字代進式子 ────────── */
  function hpz(n) { return n < 0 ? '(' + n + ')' : String(n); }                 /* 負數代入時加括號 */
  function hrow(c) { return c.join(',\\ '); }                                    /* 綜合除法的係數列 */
  function hmono(k, e) {                                                         /* 單項式：-3x^{2}、4x、5 */
    if (e === 0) return String(k);
    return (k === 1 ? '' : (k === -1 ? '-' : String(k))) + (e === 1 ? 'x' : 'x^{' + e + '}');
  }
  function hsubst(c, v) {        /* 把 x=v 代進係數陣列 c 的寫法；v=1 只留係數，0 項與係數 1 都省略 */
    var n = c.length - 1, s = '', first = true;
    for (var i = 0; i <= n; i++) {
      var k = c[i], e = n - i;
      if (k === 0) continue;
      var sg = k < 0 ? '-' : (first ? '' : '+'), ab = Math.abs(k), body;
      if (e === 0 || v === 1) body = String(ab);
      else body = (ab === 1 ? '' : ab + '\\times ') + hpz(v) + (e === 1 ? '' : '^{' + e + '}');
      s += sg + body; first = false;
    }
    return s || '0';
  }
  function solveSign(factors, lead, rel) {
    var roots = factors.map(function (f) { return f.r; }).sort(function (a, b) { return a - b; });
    var uniq = roots.filter(function (v, i) { return roots.indexOf(v) === i; });
    var multOf = {}; factors.forEach(function (f) { multOf[f.r] = (multOf[f.r] || 0) + f.m; });
    var strict = (rel === '<' || rel === '>'), want = (rel === '<' || rel === '<=') ? -1 : 1;
    function sgnAt(x) { var s = lead; factors.forEach(function (f) { if (f.m % 2 === 1) s *= (x > f.r ? 1 : -1); }); return s; }
    var pts = [-Infinity].concat(uniq, [Infinity]), segs = [];
    for (var i = 0; i < pts.length - 1; i++) {
      var lo = pts[i], hi = pts[i + 1], mid = (lo === -Infinity) ? hi - 1 : (hi === Infinity ? lo + 1 : (lo + hi) / 2);
      segs.push({ lo: lo, hi: hi, on: sgnAt(mid) === want });
    }
    var incl = {}; uniq.forEach(function (rt) { incl[rt] = !strict; });
    /* 合併 */
    var ivs = [], pts2 = [];
    for (var j = 0; j < segs.length; j++) {
      if (!segs[j].on) continue;
      var lo2 = segs[j].lo, hi2 = segs[j].hi, lc = (lo2 !== -Infinity) && incl[lo2], hc = (hi2 !== Infinity) && incl[hi2];
      var last = ivs[ivs.length - 1];
      if (last && last.hi === lo2 && last.hc) { last.hi = hi2; last.hc = hc; } else ivs.push({ lo: lo2, hi: hi2, lc: lc, hc: hc });
    }
    uniq.forEach(function (rt) {
      if (!incl[rt]) return;
      var inside = ivs.some(function (iv) { return (iv.lo < rt && rt < iv.hi) || (iv.lo === rt && iv.lc) || (iv.hi === rt && iv.hc); });
      if (!inside) pts2.push(rt);
    });
    /* 挖洞：嚴格不等式且偶次根落在區間內部 */
    var holes = [];
    if (strict) uniq.forEach(function (rt) { if (multOf[rt] % 2 === 0 && ivs.some(function (iv) { return iv.lo < rt && rt < iv.hi; })) holes.push(rt); });
    return { ivs: ivs.map(function (iv) { return [iv.lo === -Infinity ? null : iv.lo, iv.hi === Infinity ? null : iv.hi, iv.lc, iv.hc]; }), pts: pts2, holes: holes };
  }
  function setTex(sol) {
    var parts = sol.ivs.map(function (iv) {
      var lo = iv[0], hi = iv[1], lc = iv[2], hc = iv[3];
      if (lo === null && hi === null) return '\\text{所有實數}';
      if (lo === null) return 'x' + (hc ? '\\le ' : '\\lt ') + hi;
      if (hi === null) return 'x' + (lc ? '\\ge ' : '\\gt ') + lo;
      return lo + (lc ? '\\le ' : '\\lt ') + 'x' + (hc ? '\\le ' : '\\lt ') + hi;
    });
    sol.pts.forEach(function (p) { parts.push('x=' + p); });
    if (!parts.length) return '無解';
    var s = parts.map(function (t) { return '$' + t + '$'; }).join(' 或 ');
    if (sol.holes.length) s += '（且 ' + sol.holes.map(function (h) { return '$x\\ne ' + h + '$'; }).join('、') + '）';
    return s;
  }
  var REL = { '<': '\\lt ', '<=': '\\le ', '>': '\\gt ', '>=': '\\ge ' };
  function pt(x, y) { return '(' + x + ',' + y + ')'; }
  function fr2(f) { return [f.n, f.d]; }

  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* 1-1 次數的加減乘與合成 */
  L1.degOps = function (r) {
    var m = r.int(4, 10), n = r.int(2, m - 1), t = r.int(0, 2);
    var OPS = { prod: ['f(x)\\,g(x)', m + n], sum: ['f(x)+g(x)', m], diff: ['f(x)-g(x)', m],
                comp: ['f\\big(g(x)\\big)', m * n], comp2: ['g\\big(f(x)\\big)', m * n], sq: ['\\big(f(x)\\big)^{2}', 2 * m] };
    var SETS = [['prod', 'sum', 'comp', 'quo'], ['prod', 'diff', 'comp2', 'sq'], ['comp', 'sq', 'quo', 'sum']];
    var ops = SETS[t], qs = [], ans = [];
    ops.forEach(function (key, i) {
      if (key === 'quo') { qs.push('(' + (i + 1) + ') ' + T('f(x)') + ' 除以 ' + T('g(x)') + ' 的商式'); ans.push(m - n); }
      else { qs.push('(' + (i + 1) + ') ' + T(OPS[key][0])); ans.push(OPS[key][1]); }
    });
    return { q: '設 ' + T('\\deg f(x)=' + m) + '、' + T('\\deg g(x)=' + n) + '。求下列各式的次數：<br>' + qs.join('　'),
             a: ans.map(function (v, i) { return '(' + (i + 1) + ') ' + T(String(v)); }).join('　'),
             h: '先用最簡單的例子想：把 $f$ 想成 $x^{' + m + '}$、$g$ 想成 $x^{' + n + '}$。相乘時指數相加、相除時指數相減；合成是把 $x^{' + n + '}$ 代進去變成 $(x^{' + n + '})^{' + m + '}$，指數相乘；相加減則由次數高的那一項決定（低次的蓋不掉它）。',
             p: { m: m, n: n, t: t, ops: ops, ans: ans } };
  };

  /* 1-2 恆等式：換基底的係數 */
  L1.identCoef = function (r) {
    var pr = r.pick([[1, 2], [1, 3], [2, 3], [-1, 1], [-1, 2], [1, -2]]), s1 = pr[0], s2 = pr[1];
    var a = r.nz(-4, 4), b = r.nz(-6, 6), c = r.nz(-9, 9);
    var poly = polyAdd(polyAdd(polyScale(polyMul([1, -s1], [1, -s2]), a), polyScale([1, -s1], b)), [c]);
    return { q: '設 ' + T(polyTex(poly) + '=a' + factTex(s1) + factTex(s2) + '+b' + factTex(s1) + '+c') + ' 對所有實數 ' + T('x') + ' 均成立，求 ' + T('(a,b,c)') + '。',
             a: T('(a,b,c)=' + pt(a, b) .replace(')', ',' + c + ')')),
             h: '代 $x=' + s1 + '$ 可以一次消掉右邊的前兩項、只剩 $c$：左邊的值是 $' + hsubst(poly, s1) + '$。同樣代 $x=' + s2 + '$ 會消掉第一項而求出 $b$；最後比較 $x^{2}$ 的係數得 $a$。',
             p: { s1: s1, s2: s2, poly: poly, ans: [a, b, c] } };
  };

  /* 1-3 乘積中指定項的係數與係數總和 */
  L1.prodCoef = function (r) {
    var A = [r.nz(-3, 3), r.int(-4, 4), r.int(-4, 4), r.nz(-3, 3)], B = [r.nz(-3, 3), r.int(-4, 4), r.nz(-4, 4)];
    var P = polyMul(A, B), k = r.pick([2, 3, 4]), coef = P[P.length - 1 - k], sum = polyEval(P, 1);
    var pairs = [];
    for (var i = 0; i < A.length; i++) for (var j = 0; j < B.length; j++) {
      var eA = A.length - 1 - i, eB = B.length - 1 - j;
      if (eA + eB === k && A[i] !== 0 && B[j] !== 0) pairs.push('$(' + hmono(A[i], eA) + ')(' + hmono(B[j], eB) + ')$');
    }
    return { q: '設 ' + T('f(x)=(' + polyTex(A) + ')(' + polyTex(B) + ')') + '。<br>(1) 求 ' + T('f(x)') + ' 中 ' + T('x^{' + k + '}') + ' 項的係數。　(2) 求 ' + T('f(x)') + ' 的所有係數總和。',
             a: '(1) ' + T(String(coef)) + '　(2) ' + T(String(sum)),
             h: '(1) 只要挑出「次數相加剛好等於 $' + k + '$」的配對：' + (pairs.length ? pairs.join('、') + '，把每組的係數相乘再相加' : '兩個括號裡湊不出次數和為 $' + k + '$ 的配對，所以係數是 $0$') + '。(2) 係數總和就是 $f(1)$：把兩個括號各自在 $x=1$ 的值算出來再相乘，不必展開。',
             p: { A: A, B: B, k: k, ans: [coef, sum] } };
  };

  /* 1-4 綜合除法：除以 x-k */
  L1.synthDiv = function (r) {
    var c = [r.nz(-3, 3), r.int(-6, 6), r.int(-6, 6), r.int(-6, 6)], k = r.nz(-3, 3), d = synth(c, k);
    return { q: '用綜合除法求 ' + T(polyTex(c)) + ' 除以 ' + T(factTex(k).replace(/[()]/g, '')) + ' 的商式與餘式。',
             a: '商式 ' + T(polyTex(d.q)) + '，餘式 ' + T(String(d.r)),
             h: '把係數由高次排到常數：$' + hrow(c) + '$，左邊寫上 $' + k + '$（除式是 $x' + (k > 0 ? '-' + k : '+' + (-k)) + '$，所以用 $' + k + '$）。第一個係數 $' + c[0] + '$ 直接抄下來，乘 $' + k + '$ 得 $' + (c[0] * k) + '$，與第二個係數相加得 $' + (c[0] * k + c[1]) + '$；接著一路「乘 $' + k + '$ 再加」做到底，最後一格就是餘式。',
             p: { c: c, k: k, ans: { q: d.q, r: d.r } } };
  };

  /* 1-5 秦九韶：數字題偽裝的多項式 */
  L1.hornerVal = function (r) {
    var b = r.pick([7, 8, 9, 11, 12, 13]), g = [r.nz(-3, 3), r.int(-5, 5), r.int(-5, 5), r.int(-5, 5)], rem = r.int(-20, 20);
    var c = polyAdd(polyMul(g, [1, -b]), [rem]);
    var terms = c.map(function (k, i) {
      var e = 4 - i; if (e === 0 || k === 0) return null;
      var ab = Math.abs(k);                                   /* 係數 ±1 不印 `1\times` */
      return (k < 0 ? '-' : (i ? '+' : '')) + (ab === 1 ? '' : ab + '\\times ') + b + (e === 1 ? '' : '^{' + e + '}');
    }).filter(Boolean).join('');
    return { q: '求 ' + T(terms + (c[4] === 0 ? '' : (c[4] < 0 ? '-' : '+') + Math.abs(c[4]))) + ' 的值。',
             a: T(String(rem)),
             h: '把 $' + b + '$ 看成 $x$，這個式子就是 $f(x)=' + polyTex(c) + '$ 在 $x=' + b + '$ 的值。用綜合除法除以 $x-' + b + '$：係數列 $' + hrow(c) + '$，第一個 $' + c[0] + '$ 抄下來，乘 $' + b + '$ 加到 $' + c[1] + '$ 得 $' + (c[0] * b + c[1]) + '$，一路做到最後一格就是答案。',
             p: { b: b, c: c, ans: rem } };
  };

  /* 1-6 餘式定理反求係數 */
  L1.remThm = function (r) {
    var a = r.nz(-6, 6), k = r.nz(-3, 3), c = [1, r.int(-4, 4), a, r.nz(-5, 5), r.nz(-6, 6)];
    var R = polyEval(c, k);
    var q = 'x^{4}' + (c[1] ? term(c[1], 'x^{3}', false) : '') + '+ax^{2}' + (c[3] ? term(c[3], 'x', false) : '') + (c[4] ? term(c[4], '', false) : '');
    function pw(co, e) { var ab = Math.abs(co); return (co < 0 ? '-' : '+') + (ab === 1 ? '' : ab + '\\times ') + hpz(k) + (e === 1 ? '' : '^{' + e + '}'); }
    var ex = hpz(k) + '^{4}' + (c[1] ? pw(c[1], 3) : '') + '+' + hpz(k) + '^{2}a' + (c[3] ? pw(c[3], 1) : '') + (c[4] ? (c[4] < 0 ? '-' : '+') + Math.abs(c[4]) : '');
    return { q: '設 ' + T('f(x)=' + q) + '。若 ' + T('f(x)') + ' 除以 ' + T(factTex(k).replace(/[()]/g, '')) + ' 的餘式為 ' + T(String(R)) + '，求 ' + T('a') + '。',
             a: T('a=' + a),
             h: '餘式定理：除以 $x' + (k > 0 ? '-' + k : '+' + (-k)) + '$ 的餘式就是 $f(' + k + ')$。代進去得 $f(' + k + ')=' + ex + '$，其中含 $a$ 的那一項是 $' + (k * k === 1 ? '' : k * k) + 'a$；讓整個式子等於 $' + R + '$ 就是 $a$ 的一次方程式。',
             p: { c: c, k: k, R: R, ans: a } };
  };

  /* 1-7 除以兩個一次式 → 除以二次式的餘式 */
  L1.rem2pts = function (r) {
    var p = r.int(-3, 3), q; do { q = r.int(-3, 3); } while (q === p);
    var m = r.nz(-4, 4), n = r.int(-6, 6), r1 = m * p + n, r2 = m * q + n;
    return { q: '設多項式 ' + T('f(x)') + ' 除以 ' + T(factTex(p).replace(/[()]/g, '')) + ' 的餘式為 ' + T(String(r1)) + '，除以 ' + T(factTex(q).replace(/[()]/g, '')) + ' 的餘式為 ' + T(String(r2)) + '。求 ' + T('f(x)') + ' 除以 ' + T(polyTex(polyMul([1, -p], [1, -q]))) + ' 的餘式。',
             a: T(polyTex([m, n])),
             h: '餘式設 $ax+b$，它是通過 $(' + p + ',' + r1 + ')$、$(' + q + ',' + r2 + ')$ 的直線。',
             p: { p: p, q: q, r1: r1, r2: r2, ans: [m, n] } };
  };

  /* 1-8 因式定理求係數與第三個根 */
  L1.factorThm = function (r) {
    var roots = r.shuffle([r.nz(-4, 4), r.nz(-4, 4), r.nz(-4, 4)]);
    while (roots[0] === roots[1]) roots[1] = r.nz(-4, 4);
    var p = roots[0], q = roots[1], s = roots[2], c = polyMul(polyMul([1, -p], [1, -q]), [1, -s]);
    return { q: '設 ' + T('f(x)=x^{3}+ax^{2}+bx' + (c[3] < 0 ? '-' : '+') + Math.abs(c[3])) + ' 同時有因式 ' + T(factTex(p)) + ' 與 ' + T(factTex(q)) + '，求 ' + T('(a,b)') + '，並求方程式 ' + T('f(x)=0') + ' 的第三個根。',
             a: T('(a,b)=' + pt(c[1], c[2])) + '，第三個根為 ' + T(String(s)),
             h: '$f(' + p + ')=0$、$f(' + q + ')=0$ 聯立解 $a,b$；第三個根用「三根之積 $=' + (-c[3]) + '$」最快。',
             p: { p: p, q: q, c3: c[3], ans: [c[1], c[2], s] } };
  };

  /* 1-9 因式分解（有理數係數） */
  L1.factorize = function (r) {
    var lead = r.pick([1, 1, 2]), p = r.nz(-4, 4), q; do { q = r.nz(-4, 4); } while (q === p);
    var lin = lead === 1 ? [1, -r.nz(-4, 4)] : [2, r.pick([-3, -1, 1, 3])];
    var c = polyMul(polyMul([1, -p], [1, -q]), lin);
    var facs = [[1, -p], [1, -q], lin];
    var v1 = polyEval(c, 1), v2 = polyEval(c, -1);
    var cnt = {}, ord = [];   /* 重複的因式合併成次方 */
    facs.forEach(function (f) { var s = polyTex(f); if (!cnt[s]) { cnt[s] = 0; ord.push(s); } cnt[s]++; });
    return { q: '將 ' + T(polyTex(c)) + ' 在有理數係數範圍內完全因式分解。',
             a: T(ord.map(function (s) { return '(' + s + ')' + (cnt[s] > 1 ? '^{' + cnt[s] + '}' : ''); }).join('')),
             h: '先試最好算的兩個：$f(1)=' + v1 + '$、$f(-1)=' + v2 + '$。' + ((v1 === 0 || v2 === 0) ? '其中一個是 $0$，那個 $x$ 值就是根，直接用綜合除法除掉它、降成二次再分解。' : '兩個都不是 $0$，改用牛頓一次因式檢驗法：可能的根是「常數項 $' + c[3] + '$ 的因數」除以「首項係數 $' + c[0] + '$ 的因數」，一個一個試；找到根 $x=s$ 就用綜合除法除以 $x-s$ 降成二次再分解。'),
             p: { c: c, ans: facs } };
  };

  /* 1-10 勘根定理：根落在哪些相鄰整數之間 */
  L1.rootLoc = function (r) {
    var c, vals, ivs, tries = 0;
    do {
      c = [1, r.int(-3, 3), r.int(-6, 6), r.nz(-6, 6)];
      vals = []; for (var x = -3; x <= 3; x++) vals.push(polyEval(c, x));
      ivs = []; for (var i = 0; i < 6; i++) if (vals[i] * vals[i + 1] < 0) ivs.push(i - 3);
      tries++;
    } while ((ivs.length < 2 || vals.some(function (v) { return v === 0; })) && tries < 200);
    return { q: '方程式 ' + T(polyTex(c) + '=0') + ' 在 ' + T('-3\\le x\\le3') + ' 之間，落在哪些「相鄰整數」之間必有實根？（列出所有區間）',
             a: ivs.map(function (l) { return T('(' + l + ',' + (l + 1) + ')'); }).join('、'),
             h: '把 $f(-3)$ 到 $f(3)$ 七個值都算出來（用綜合除法比直接代入快），例如 $f(-3)=' + vals[0] + '$、$f(-2)=' + vals[1] + '$；再看相鄰兩個值哪裡「一正一負」，那一段裡面就一定有根（勘根定理）。',
             p: { c: c, ans: ivs } };
  };

  /* 1-11 配方求頂點 */
  L1.vertex = function (r) {
    var a = r.pick([1, -1, 2, -2, 3]), b = r.nz(-8, 8), c = r.int(-6, 6);
    var h = F(-b, 2 * a), k = Fr.sub(F(c), F(b * b, 4 * a));
    return { q: '求二次函數 ' + T('f(x)=' + polyTex([a, b, c])) + ' 圖形的頂點坐標，並說明它是最大值還是最小值。',
             a: '頂點 ' + T('\\left(' + Fr.tex(h) + ',' + Fr.tex(k) + '\\right)') + '，' + (a > 0 ? '最小值' : '最大值') + ' ' + T(Fr.tex(k)),
             h: '對稱軸用公式 $x=-\\dfrac{b}{2a}$：本題 $a=' + a + '$、$b=' + b + '$，先算 $x=-\\dfrac{' + hpz(b) + '}{2\\times' + hpz(a) + '}$，再把這個 $x$ 代回 $f(x)$ 求 $y$ 坐標。$a=' + a + (a > 0 ? '\\gt 0$，開口向上，頂點是最低點。' : '\\lt 0$，開口向下，頂點是最高點。'),
             p: { a: a, b: b, c: c, ans: { h: fr2(h), k: fr2(k), min: a > 0 } } };
  };

  /* 1-12 對稱軸的偽裝：f(p+t)=f(q-t) */
  L1.axisCond = function (r) {
    var h = r.int(-4, 4), d = r.int(1, 4), p = h - d, q = h + d, c = r.int(-9, 9);
    var b = -2 * h, mn = c - h * h;
    var cond = 'f(' + (p === 0 ? 't' : p + '+t') + ')=f(' + (q === 0 ? '-t' : q + '-t') + ')';
    return { q: '設 ' + T('f(x)=x^{2}+bx' + (c === 0 ? '' : (c < 0 ? '-' : '+') + Math.abs(c))) + '，且對任意實數 ' + T('t') + ' 都有 ' + T(cond) + '。求 ' + T('b') + ' 與 ' + T('f(x)') + ' 的最小值。',
             a: T('b=' + b) + '，最小值 ' + T(String(mn)),
             h: '$' + cond + '$ 表示對稱軸在 $' + p + '$ 與 $' + q + '$ 的正中間 $x=' + h + '$，於是 $-\\frac b2=' + h + '$。',
             p: { p: p, q: q, c: c, ans: [b, mn] } };
  };

  /* 1-13 二次函數的平移 */
  L1.shiftQuad = function (r) {
    var a = r.pick([1, -1, 2, -2]), h1 = r.int(-3, 3), k1 = r.int(-5, 5), h = r.nz(-4, 4), k = r.nz(-6, 6);
    var f = polyAdd(polyScale(polyMul([1, -h1], [1, -h1]), a), [k1]);
    var g = polyAdd(polyScale(polyMul([1, -(h1 + h)], [1, -(h1 + h)]), a), [k1 + k]);
    return { q: '將 ' + T('y=' + polyTex(f)) + ' 的圖形' + (h > 0 ? '向右平移 ' + h : '向左平移 ' + (-h)) + ' 單位，再' + (k > 0 ? '向上平移 ' + k : '向下平移 ' + (-k)) + ' 單位，求所得圖形的方程式（展開）。',
             a: T('y=' + polyTex(g)),
             h: '先配方找頂點 $(' + h1 + ',' + k1 + ')$，平移只動頂點，$a$ 不變；再展開。',
             p: { f: f, h: h, k: k, ans: g } };
  };

  /* 1-14 判別式：兩交點距離 */
  L1.discrimDist = function (r) {
    var b = r.nz(-8, 8), d = r.pick([2, 4, 6]); if (Math.abs(b) % 2 === 1) d = r.pick([1, 3, 5]);
    var k = (b * b - d * d) / 4;
    return { q: '設 ' + T('f(x)=x^{2}' + term(b, 'x', false) + '+k') + ' 的圖形交 ' + T('x') + ' 軸於 ' + T('P,Q') + ' 兩點，且 ' + T('\\overline{PQ}=' + d) + '，求 ' + T('k') + '。',
             a: T('k=' + k),
             h: '首項係數是 $1$，兩根之差就是 $\\sqrt{b^{2}-4k}$。本題 $b=' + b + '$、$\\overline{PQ}=' + d + '$，先算 $b^{2}=' + (b * b) + '$ 與 $\\overline{PQ}^{2}=' + (d * d) + '$，再由 $b^{2}-4k=\\overline{PQ}^{2}$ 解出 $k$。',
             p: { b: b, d: d, ans: k } };
  };

  /* 1-15 區間最值 */
  L1.intervalMax = function (r) {
    var a = r.pick([1, -1, 2, -2]), h = r.int(-2, 3), k = r.int(-5, 5), lo = h - r.int(0, 3), hi = h + r.int(0, 4);
    if (lo === hi) hi = lo + 2;
    if (r() < 0.35) { var w = r.int(1, 3); if (r() < 0.5) { lo = h + 1; hi = h + 1 + w; } else { hi = h - 1; lo = h - 1 - w; } }
    var f = polyAdd(polyScale(polyMul([1, -h], [1, -h]), a), [k]);
    var cands = [lo, hi]; if (lo <= h && h <= hi) cands.push(h);
    var vals = cands.map(function (x) { return polyEval(f, x); }), M = Math.max.apply(null, vals), m = Math.min.apply(null, vals);
    var vtx = (a === 1 ? '' : (a === -1 ? '-' : a)) + (h === 0 ? 'x^{2}' : '(x' + (h > 0 ? '-' + h : '+' + (-h)) + ')^{2}') + (k === 0 ? '' : (k > 0 ? '+' + k : '-' + (-k)));
    var inside = (lo <= h && h <= hi);
    return { q: '求 ' + T('f(x)=' + polyTex(f)) + ' 在 ' + T(lo + '\\le x\\le ' + hi) + ' 上的最大值 ' + T('M') + ' 與最小值 ' + T('m') + '。',
             a: T('M=' + M) + '，' + T('m=' + m),
             h: '先配方：$f(x)=' + vtx + '$，對稱軸 $x=' + h + '$。本題的區間是 $' + lo + '\\le x\\le ' + hi + '$，對稱軸' + (inside ? '落在區間內，所以要比較頂點與兩個端點 $f(' + lo + ')$、$f(' + hi + ')$ 這三個值' : '落在區間外，函數在這一段上單調，最大與最小都在端點 $f(' + lo + ')$、$f(' + hi + ')$') + '。',
             p: { f: f, lo: lo, hi: hi, ans: [M, m] } };
  };

  /* 1-16 恆成立：判別式 */
  L1.alwaysPos = function (r) {
    var u, v;                      /* 判別式的兩根 u<v 都是整數；u+v≠0、uv≠0 讓題幹不出現 0 係數 */
    do { u = r.nz(-4, 4); v = r.nz(-4, 4); } while (u >= v || u + v === 0);
    var pp = u + v, nn = -u * v, form = r.int(0, 1), rel = r.pick(['>', '>=']);
    var con = term(pp, 'm', true) + term(nn, '', false);           /* 常數項 pm+n */
    var d4 = 'm^{2}' + term(-pp, 'm', false) + term(-nn, '', false);
    return { q: '若對所有實數 ' + T('x') + '，' + T('x^{2}' + (form === 0 ? '-2mx' : '+2mx') + '+(' + con + ')' + (rel === '>' ? '\\gt 0' : '\\ge 0')) + ' 恆成立，求實數 ' + T('m') + ' 的範圍。',
             a: T(u + (rel === '>' ? '\\lt m\\lt ' : '\\le m\\le ') + v),
             h: '首項係數 $1\\gt 0$ 已經固定，只要判別式 ' + (rel === '>' ? '$\\lt 0$（圖形完全在 $x$ 軸上方）' : '$\\le 0$（可以碰到 $x$ 軸）') + '就成立。本題 $\\dfrac{D}{4}=m^{2}-(' + con + ')=' + d4 + '$，這個 $m$ 的二次式兩根都是整數，先分解再解 $m$ 的不等式。',
             p: { u: u, v: v, pp: pp, nn: nn, form: form, rel: rel, ans: [u, v] } };
  };

  /* 1-17 三次函數的對稱中心 */
  L1.cubicCenter = function (r) {
    var a = r.pick([1, -1, 2, -2]), h = r.nz(-3, 3), p = r.int(-6, 6), k = r.int(-9, 9);
    var f = polyAdd(polyAdd(polyScale(polyMul(polyMul([1, -h], [1, -h]), [1, -h]), a), polyScale([1, -h], p)), [k]);
    return { q: '求三次函數 ' + T('f(x)=' + polyTex(f)) + ' 圖形的對稱中心。',
             a: T(pt(h, k)),
             h: '對稱中心的 $x$ 坐標是 $-\\dfrac{b}{3a}$（$a$ 是 $x^{3}$ 的係數、$b$ 是 $x^{2}$ 的係數）：本題 $a=' + f[0] + '$、$b=' + f[1] + '$，先算 $-\\dfrac{' + hpz(f[1]) + '}{3\\times' + hpz(f[0]) + '}$；再把這個 $x$ 代回求 $y$ 坐標——用係數列 $' + hrow(f) + '$ 做綜合除法，餘式就是 $f$ 的值。',
             p: { f: f, ans: [h, k] } };
  };

  /* 1-18 一次近似直線 */
  L1.linApprox = function (r) {
    var f = [r.pick([1, -1, 2]), r.int(-4, 4), r.int(-5, 5), r.int(-6, 6)], c = r.nz(-2, 2);
    var y0 = polyEval(f, c), m = polyEval(polyDeriv(f), c), n = y0 - m * c;
    var xc = 'x' + (c > 0 ? '-' + c : '+' + (-c));
    return { q: '求 ' + T('y=' + polyTex(f)) + ' 的圖形在 ' + T('x=' + c) + ' 附近的一次近似直線。',
             a: T('y=' + polyTex([m, n])),
             h: '把係數列 $' + hrow(f) + '$ 用綜合除法連除兩次 $' + xc + '$：第一次的餘式是 $f(' + c + ')$，也就是常數項 $c_{0}$；對商式再除一次，餘式就是一次項係數 $c_{1}$。近似直線是 $y=c_{0}+c_{1}(' + xc + ')$，最後展開整理。',
             p: { f: f, c: c, ans: [m, n] } };
  };

  /* 1-19 二次不等式 */
  L1.quadIneq = function (r) {
    var p = r.int(-4, 3), q = p + r.int(1, 5), a = r.pick([1, 1, -1, 2]), rel = r.pick(['<', '<=', '>', '>=']);
    var f = polyScale(polyMul([1, -p], [1, -q]), a), sol = solveSign([{ r: p, m: 1 }, { r: q, m: 1 }], a > 0 ? 1 : -1, rel);
    return { q: '解不等式 ' + T(polyTex(f) + REL[rel] + '0') + '。',
             a: setTex(sol),
             h: '先分解成 $' + (a === 1 ? '' : (a === -1 ? '-' : a)) + factTex(p) + factTex(q) + '$；' + (a > 0 ? '開口向上' : '開口向下，先把負號除掉並反向') + '，「兩根之間為負、兩根之外為正」。',
             p: { f: f, factors: [[p, 1], [q, 1]], lead: a > 0 ? 1 : -1, rel: rel, ans: sol } };
  };

  /* 1-20 已分解的三次不等式 */
  L1.cubicIneq = function (r) {
    var rs = r.shuffle([r.int(-4, 4), r.int(-4, 4), r.int(-4, 4)]);
    while (rs[1] === rs[0]) rs[1] = r.int(-4, 4);
    while (rs[2] === rs[0] || rs[2] === rs[1]) rs[2] = r.int(-4, 4);
    var lead = r.pick([1, 1, -1]), rel = r.pick(['<', '<=', '>', '>=']);
    var sol = solveSign(rs.map(function (v) { return { r: v, m: 1 }; }), lead, rel);
    var srt = rs.slice().sort(function (a, b) { return a - b; });
    return { q: '解不等式 ' + T((lead < 0 ? '-' : '') + rs.map(factTex).join('') + REL[rel] + '0') + '。',
             a: setTex(sol),
             h: '三個根由小到大是 $' + srt.join(',\\ ') + '$，把它們標在數線上分成四段。最右邊那一段的符號就是首項係數的符號（本題首項係數 $' + (lead > 0 ? '1' : '-1') + '$，所以最右段是' + (lead > 0 ? '正' : '負') + '的），往左每經過一個根就變號一次；再挑出符合 $' + REL[rel] + '0$ 的那幾段' + ((rel === '<=' || rel === '>=') ? '，三個根本身也要算進去。' : '，三個根本身不能取。'),
             p: { roots: rs, lead: lead, rel: rel, ans: sol } };
  };

  /* 1-21 分式不等式 */
  L1.fracIneq = function (r) {
    var a = r.int(-4, 4), b; do { b = r.int(-4, 4); } while (b === a);
    var rel = r.pick(['<', '<=', '>', '>=']);
    var sol = solveSign([{ r: a, m: 1 }, { r: b, m: 1 }], 1, rel);
    /* 分母 x=b 一律不可取 */
    sol.ivs = sol.ivs.map(function (iv) { if (iv[0] === b) iv[2] = false; if (iv[1] === b) iv[3] = false; return iv; });
    sol.pts = sol.pts.filter(function (v) { return v !== b; });
    return { q: '解不等式 ' + T('\\dfrac{x' + (a > 0 ? '-' + a : (a < 0 ? '+' + (-a) : '')) + '}{x' + (b > 0 ? '-' + b : (b < 0 ? '+' + (-b) : '')) + '}' + REL[rel] + '0') + '。',
             a: setTex(sol),
             h: '同號相除與同號相乘一樣，改成 $' + factTex(a) + factTex(b) + REL[rel] + '0$ 來解，但分母 $x=' + b + '$ 一定要挖掉。',
             p: { a: a, b: b, rel: rel, ans: sol } };
  };

  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 2-1 兩個二次條件，拼出第三個 */
  L2.remQuadTwo = function (r) {
    var rs = r.shuffle([-3, -2, -1, 1, 2, 3, 4]).slice(0, 3), A = rs[0], B = rs[1], C = rs[2];
    var m1 = r.nz(-4, 4), n1 = r.int(-6, 6), m2 = r.nz(-4, 4), fA = m1 * A + n1, fB = m1 * B + n1, fC = fB + m2 * (C - B);
    for (var tries = 0; tries < 30 && ((fA - fC) % (A - C) !== 0 || m2 === m1); tries++) { m2 = r.nz(-4, 4); fC = fB + m2 * (C - B); }
    if ((fA - fC) % (A - C) !== 0 || m2 === m1) {   /* m2=m1 會讓兩個已知餘式一模一樣（退化）；(m2-m1)(A-B) 是 (A-C) 的倍數即可整除 */
      var stp = Math.abs(A - C) / gcd(A - B, A - C);
      m2 = (m1 > 0 && m1 - stp !== 0) ? m1 - stp : (m1 + stp !== 0 ? m1 + stp : m1 - stp); fC = fB + m2 * (C - B);
    }
    function line(x1, y1, x2, y2) { var m = F(y1 - y2, x1 - x2), n = Fr.sub(F(y1), Fr.mul(m, F(x1))); return [m, n]; }
    var r1 = line(A, fA, B, fB), r2 = line(B, fB, C, fC), ans = line(A, fA, C, fC);
    function lt(l) { var m = l[0], n = l[1]; var s = (m.n === 0 ? '' : (Fr.eq(m, F(1)) ? '' : (Fr.eq(m, F(-1)) ? '-' : Fr.tex(m, true))) + 'x'); if (n.n !== 0) s += (n.n < 0 ? '-' : (s ? '+' : '')) + Fr.tex(F(Math.abs(n.n), n.d), true); return s || '0'; }
    var d1 = polyMul([1, -A], [1, -B]), d2 = polyMul([1, -B], [1, -C]), d3 = polyMul([1, -A], [1, -C]);
    return { q: '設多項式 ' + T('f(x)') + ' 除以 ' + T(polyTex(d1)) + ' 的餘式為 ' + T(lt(r1)) + '，除以 ' + T(polyTex(d2)) + ' 的餘式為 ' + T(lt(r2)) + '。求 ' + T('f(x)') + ' 除以 ' + T(polyTex(d3)) + ' 的餘式。',
             a: T(lt(ans)),
             h: '三個二次式分別是 $' + factTex(A) + factTex(B) + '$、$' + factTex(B) + factTex(C) + '$、$' + factTex(A) + factTex(C) + '$；由前兩式取出 $f(' + A + ')$、$f(' + C + ')$，再求過兩點的直線。',
             p: { A: A, B: B, C: C, r1: [fr2(r1[0]), fr2(r1[1])], r2: [fr2(r2[0]), fr2(r2[1])], ans: [fr2(ans[0]), fr2(ans[1])] } };
  };

  /* 2-2 x^n 除以 (x±1)^2 */
  L2.remSqr = function (r) {
    var n = r.int(20, 199), s = r.pick([1, -1]);           /* 除式 (x-s)^2 */
    /* x=t+s：(t+s)^n ≈ s^n + n s^{n-1} t ⇒ 餘式 n s^{n-1}(x-s)+s^n */
    var m = n * Math.pow(s, n - 1), c0 = Math.pow(s, n) - m * s;
    return { q: '求 ' + T('x^{' + n + '}') + ' 除以 ' + T('(x' + (s > 0 ? '-1' : '+1') + ')^{2}') + ' 的餘式。',
             a: T(polyTex([m, c0])),
             h: '令 $x=t' + (s > 0 ? '+1' : '-1') + '$，只留 $(t' + (s > 0 ? '+1' : '-1') + ')^{' + n + '}$ 展開的常數項與一次項（二項式定理），再把 $t$ 換回 $x' + (s > 0 ? '-1' : '+1') + '$。',
             p: { n: n, s: s, ans: [m, c0] } };
  };

  /* 2-3 同餘：(x-k)f(x) 的餘式 → f(x) 的餘式 */
  L2.congRem = function (r) {
    var p = r.int(-3, 3), q = r.nz(-5, 5), k;
    do { k = r.nz(-3, 3); } while (k * k + p * k + q === 0);
    var u = r.nz(-3, 3), v = r.int(-5, 5);
    /* (x-k)(ux+v) = u x^2 + (v-ku)x - kv ≡ u(-px-q) + (v-ku)x - kv */
    var R = [-u * p + v - k * u, -u * q - k * v];
    var mod = [1, p, q];
    return { q: '設 ' + T('f(x)') + ' 為多項式。若 ' + T(factTex(k) + 'f(x)') + ' 除以 ' + T(polyTex(mod)) + ' 的餘式為 ' + T(polyTex(R)) + '，求 ' + T('f(x)') + ' 除以 ' + T(polyTex(mod)) + ' 的餘式。',
             a: T(polyTex([u, v])),
             h: '設 $f\\equiv ax+b$，在 $\\bmod(' + polyTex(mod) + ')$ 下 $x^2\\equiv ' + polyTex([-p, -q]) + '$，把 $' + factTex(k) + '(ax+b)$ 降到一次後比較係數。',
             p: { p: p, q: q, k: k, R: R, ans: [u, v] } };
  };

  /* 2-4 三次的根與係數 */
  L2.vieta3 = function (r) {
    var rs = [r.nz(-3, 3), r.nz(-3, 3), r.nz(-3, 3)];
    var c = polyMul(polyMul([1, -rs[0]], [1, -rs[1]]), [1, -rs[2]]);
    var e1 = -c[1], e2 = c[2], e3 = -c[3], type = r.pick([0, 1, 2]);
    var ans, expr;
    if (type === 0) { ans = F(e2, e3); expr = '\\dfrac1\\alpha+\\dfrac1\\beta+\\dfrac1\\gamma'; }
    else if (type === 1) { ans = F(e1 * e1 - 2 * e2); expr = '\\alpha^{2}+\\beta^{2}+\\gamma^{2}'; }
    else { ans = F(1 + e1 + e2 + e3); expr = '(\\alpha+1)(\\beta+1)(\\gamma+1)'; }
    return { q: '設 ' + T('\\alpha,\\beta,\\gamma') + ' 為方程式 ' + T(polyTex(c) + '=0') + ' 的三根，求 ' + T(expr) + '。',
             a: T(Fr.tex(ans)),
             h: '三根和 $=' + e1 + '$、兩兩積之和 $=' + e2 + '$、三根積 $=' + e3 + '$；' + (type === 0 ? '倒數和 $=\\dfrac{\\text{兩兩積之和}}{\\text{三根積}}$' : (type === 1 ? '平方和 $=(\\text{和})^2-2(\\text{兩兩積之和})$' : '展開後 $=1+\\text{和}+\\text{兩兩積和}+\\text{積}$，也等於 $-f(-1)$')) + '。',
             p: { c: c, type: type, ans: fr2(ans) } };
  };

  /* 2-5 三根成等差 */
  L2.cubicAP = function (r) {
    var d = r.nz(-5, 5), e = r.int(1, 4), t = r.int(0, 2), rs = [d - e, d, d + e];
    var c = polyMul(polyMul([1, -rs[0]], [1, -rs[1]]), [1, -rs[2]]);
    var ask = ['三根之積', '三根中最大的一根', '三根的平方和'][t];
    var val = [-c[3], d + e, rs[0] * rs[0] + rs[1] * rs[1] + rs[2] * rs[2]][t];
    return { q: '設 ' + T('x^{3}' + term(c[1], 'x^{2}', false) + term(c[2], 'x', false) + '+k=0') + ' 的三根成等差數列，求 ' + T('k') + ' 與' + ask + '。',
             a: T('k=' + c[3]) + '，' + ask + ' ' + T(String(val)),
             h: '三根成等差就設成 $d-e,\\ d,\\ d+e$，三根和 $=3d$。由 $x^{2}$ 的係數得三根和 $3d=' + (-c[1]) + '$ ⟹ $d=' + d + '$，所以 $x=' + d + '$ 一定是一根。把它代回方程式：$' + hsubst([1, c[1], c[2], 0], d) + '+k=0$，就能解出 $k$；有了 $k$ 再把三根求出來。',
             p: { c: c, d: d, e: e, t: t, ask: ask, ans: [c[3], val, rs] } };
  };

  /* 2-6 由對稱軸、y 截距、與 x 軸兩交點距離求二次函數 */
  L2.quadFromCond = function (r) {
    var h, half; do { h = r.int(-3, 3); half = r.int(1, 3); } while (Math.abs(h) === half);   /* 有根為 0 ⟹ y 截距 0，a 定不出來 */
    var a = r.pick([1, -1, 2, -2]);
    var p = h - half, q = h + half, f = polyScale(polyMul([1, -p], [1, -q]), a), c = f[2];
    return { q: '二次函數 ' + T('y=ax^{2}+bx+c') + ' 的圖形對稱軸為 ' + T('x=' + h) + '，與 ' + T('y') + ' 軸交於 ' + T(pt(0, c)) + '，與 ' + T('x') + ' 軸交於 ' + T('A,B') + ' 兩點且 ' + T('\\overline{AB}=' + (2 * half)) + '。求 ' + T('(a,b,c)') + '。',
             a: T('(a,b,c)=(' + f.join(',') + ')'),
             h: '兩根在對稱軸兩側各 $' + half + '$：$x=' + p + ',' + q + '$，所以可設 $y=a' + factTex(p) + factTex(q) + '$。再用 $y$ 截距定 $a$：把 $x=0$ 代進去得 $a\\times' + hpz(p * q) + '=' + c + '$，解出 $a$ 之後展開就有 $b,c$。',
             p: { h: h, half: half, c: c, ans: f } };
  };

  /* 2-7 由三個函數值求二次函數（拉格朗日／聯立） */
  L2.quadThreePts = function (r) {
    var a = r.nz(-3, 3), b = r.int(-5, 5), c = r.int(-6, 6), xs = r.shuffle([-2, -1, 0, 1, 2, 3]).slice(0, 3).sort(function (u, v) { return u - v; });
    var f = [a, b, c], ys = xs.map(function (x) { return polyEval(f, x); });
    var eqs = xs.map(function (x, i) {
      var s = term(x * x, 'a', true); s += term(x, 'b', s === ''); s += term(1, 'c', s === '');
      return s + '=' + ys[i];
    });
    return { q: '已知二次函數 ' + T('f(x)') + ' 滿足 ' + xs.map(function (x, i) { return T('f(' + x + ')=' + ys[i]); }).join('、') + '，求 ' + T('f(x)') + '。',
             a: T('f(x)=' + polyTex(f)),
             h: '設 $f(x)=ax^{2}+bx+c$，把三個點代進去：$' + eqs[0] + '$、$' + eqs[1] + '$、$' + eqs[2] + '$。先用兩式相減消掉 $c$，解出 $a,b$ 後再回代求 $c$。',
             p: { xs: xs, ys: ys, ans: f } };
  };

  /* 2-8 區間最值含參數（開口方向兩解） */
  L2.intervalParam = function (r) {
    var h = r.int(-2, 3), w = r.pick([1, 2, 3]), lo = h - w, hi = h;      /* 軸在右端點 */
    var diff = w * w * r.pick([1, 2]), m = r.int(-6, 4), M = m + diff;
    var aP = diff / (w * w), bP = m + aP * h * h, aN = -aP, bN = M + aN * h * h;
    var fTex = 'f(x)=ax^{2}' + term(-2 * h, 'ax', false) + '+b';
    if (h === 0) fTex = 'f(x)=ax^{2}+b';
    function fv(x) { var s = term(x * x - 2 * h * x, 'a', true); return s + term(1, 'b', s === ''); }
    return { q: '已知二次函數 ' + T(fTex) + ' 在區間 ' + T(lo + '\\le x\\le ' + hi) + ' 的最大值為 ' + T(String(M)) + '、最小值為 ' + T(String(m)) + '，求數對 ' + T('(a,b)') + ' 的所有可能值。',
             a: T('(a,b)=' + pt(aP, bP)) + ' 或 ' + T(pt(aN, bN)),
             h: '配方 $f(x)=a' + factTex(h) + '^2+(b' + (h ? '-' + (h * h === 1 ? '' : h * h) + 'a' : '') + ')$，對稱軸 $x=' + h + '$ 剛好是右端點 ⟹ 區間內單調，最值只在兩端點：$f(' + lo + ')=' + fv(lo) + '$、$f(' + hi + ')=' + fv(hi) + '$。把這兩個式子分別配成 $' + M + '$ 與 $' + m + '$（$a\\gt0$ 與 $a\\lt0$ 剛好對調誰大誰小），兩種配法各聯立解一次。',
             p: { h: h, lo: lo, hi: hi, M: M, m: m, ans: [[aP, bP], [aN, bN]] } };
  };

  /* 2-9 恆成立：別漏掉首項係數為 0 */
  L2.alwaysPosCount = function (r) {
    var c = r.int(-4, 4), n = r.int(3, 9);
    var q = '(m' + (c ? (c > 0 ? '+' + c : '-' + (-c)) : '') + ')x^{2}+2(m' + (c ? (c > 0 ? '+' + c : '-' + (-c)) : '') + ')x+' + n + '\\gt0';
    return { q: '設對任何實數 ' + T('x') + '，不等式 ' + T(q) + ' 恆成立。求滿足條件的整數 ' + T('m') + ' 共有幾個。',
             a: T(String(n)) + ' 個（' + T(-c + '\\le m\\lt ' + (n - c)) + '）',
             h: '先看 $m' + (c ? (c > 0 ? '+' + c : '-' + (-c)) : '') + '=0$：式子變成 $' + n + '\\gt0$ 成立！再看 $t\\gt0$ 且 $D\\lt0$：$4t^2-' + (4 * n) + 't\\lt0$ ⟹ $0\\lt t\\lt ' + n + '$（$t$ 為首項係數）。',
             p: { c: c, n: n, ans: { count: n, lo: -c, hi: n - c } } };
  };

  /* 2-10 拋物線恆在直線上方 */
  L2.lineBelowParab = function (r) {
    var p = r.nz(-5, 5), s = r.int(1, 4), q = r.int(-5, 5), c = q + s * s;
    var bp = '(b' + (p > 0 ? '-' + p : '+' + (-p)) + ')';
    return { q: '若拋物線 ' + T('y=x^{2}+bx' + (c === 0 ? '' : (c < 0 ? '-' : '+') + Math.abs(c))) + ' 的圖形恆在直線 ' + T('y=' + polyTex([p, q])) + ' 的上方，求實數 ' + T('b') + ' 的範圍。',
             a: T((p - 2 * s) + '\\lt b\\lt ' + (p + 2 * s)),
             h: '相減：$x^2+' + bp + 'x+' + (s * s) + '\\gt0$ 恆成立 ⟹ $' + bp + '^2-4\\cdot' + (s * s) + '\\lt0$。',
             p: { p: p, q: q, c: c, ans: [p - 2 * s, p + 2 * s] } };
  };

  /* 2-11 定價與最大利潤 */
  L2.profit = function (r) {
    var d = r.pick([5, 10, 10, 20]), e = r.pick([5, 10, 20, 50]), tStar = r.int(-3, 3), u = r.int(Math.max(2 * tStar + 2, 4), 2 * tStar + 12), v = u - 2 * tStar;
    var Q0 = e * u, marg = d * v, C = r.pick([40, 50, 80, 100, 120]), P0 = C + marg;
    /* 利潤 (marg + d t)(Q0 - e t)，t 為調價次數 */
    var best = P0 + d * tStar, prof = (marg + d * tStar) * (Q0 - e * tStar);
    return { q: '某商品成本每件 ' + T(String(C)) + ' 元。若定價 ' + T(String(P0)) + ' 元，每週可賣 ' + T(String(Q0)) + ' 件；價格每上漲（下跌）' + T(String(d)) + ' 元，每週就少賣（多賣）' + T(String(e)) + ' 件。求定價多少元時每週利潤最大，並求最大利潤。',
             a: '定價 ' + T(String(best)) + ' 元，最大利潤 ' + T(String(prof)) + ' 元',
             h: '設調價 $t$ 次（漲為正）：利潤 $=(' + marg + '+' + d + 't)(' + Q0 + '-' + e + 't)$，是開口向下的二次式，頂點在兩根 $t=' + (-marg / d) + '$ 與 $t=' + (Q0 / e) + '$ 的正中間。',
             p: { C: C, P0: P0, Q0: Q0, d: d, e: e, ans: [best, prof] } };
  };

  /* 2-12 對稱中心＋兩點 → 求第三點 */
  L2.cubicCenterPts = function (r) {
    var h = r.int(-2, 2), k = r.int(-5, 5), a = r.pick([1, -1, 2]), p = r.int(-5, 5);
    var f = polyAdd(polyAdd(polyScale(polyMul(polyMul([1, -h], [1, -h]), [1, -h]), a), polyScale([1, -h], p)), [k]);
    var x1 = h + 1, x2 = h - 2, x3 = h + 3;
    return { q: '設三次函數 ' + T('f(x)') + ' 圖形的對稱中心為 ' + T(pt(h, k)) + '，且圖形通過 ' + T(pt(x1, polyEval(f, x1))) + ' 與 ' + T(pt(x2, polyEval(f, x2))) + '。求 ' + T('f(' + x3 + ')') + '。',
             a: T('f(' + x3 + ')=' + polyEval(f, x3)),
             h: '設 $f(x)=' + (h ? 'a(x' + (h > 0 ? '-' + h : '+' + (-h)) + ')^3+p(x' + (h > 0 ? '-' + h : '+' + (-h)) + ')' : 'ax^3+px') + (k ? (k > 0 ? '+' + k : '-' + (-k)) : '') + '$，代兩點解 $a,p$。',
             p: { h: h, k: k, x1: x1, y1: polyEval(f, x1), x2: x2, y2: polyEval(f, x2), x3: x3, ans: polyEval(f, x3) } };
  };

  /* 2-13 三次函數平移後的標準式 */
  L2.cubicShift = function (r) {
    var a = r.pick([1, -1, 2]), h0 = r.int(-2, 2), p = r.nz(-6, 6), k0 = r.int(-5, 5), dh = r.nz(-3, 3), dk = r.nz(-5, 5);
    var f = polyAdd(polyAdd(polyScale(polyMul(polyMul([1, -h0], [1, -h0]), [1, -h0]), a), polyScale([1, -h0], p)), [k0]);
    var h = h0 + dh, k = k0 + dk;
    return { q: '設 ' + T('f(x)=' + polyTex(f)) + '。將 ' + T('y=f(x)') + ' 的圖形' + (dh > 0 ? '向右平移 ' + dh : '向左平移 ' + (-dh)) + ' 單位、' + (dk > 0 ? '向上平移 ' + dk : '向下平移 ' + (-dk)) + ' 單位後，會和 ' + T('y=a(x-h)^{3}+p(x-h)+k') + ' 重合，求 ' + T('a+p+h+k') + '。',
             a: T('a+p+h+k=' + (a + p + h + k)) + '（' + T('a=' + a + ',\\ p=' + p + ',\\ h=' + h + ',\\ k=' + k) + '）',
             h: '先把 $f$ 寫成標準式：中心 $x=' + h0 + '$，$f(' + h0 + ')=' + k0 + '$，連除兩次得 $p$；平移只改 $h,k$，$a,p$ 不變。',
             p: { f: f, dh: dh, dk: dk, ans: { a: a, p: p, h: h, k: k, sum: a + p + h + k } } };
  };

  /* 2-14 一次近似求近似值 */
  L2.linApproxVal = function (r) {
    var f, c, delta, exact, lin, tries = 0;
    do {
      f = [r.pick([1, 2, 3, -1, -2]), r.int(-6, 6), r.int(-8, 8), r.int(-9, 9)]; c = r.nz(-3, 3); delta = r.pick([0.01, -0.01, 0.02, -0.02]);
      var m = polyEval(polyDeriv(f), c);
      exact = polyEval(f, c + delta); lin = polyEval(f, c) + m * delta; tries++;
    } while (tries < 200 && (Math.round(exact * 100) !== Math.round(lin * 100) || Math.abs(Math.round(exact * 100) - exact * 100) > 0.35));
    var ans = Math.round(exact * 100) / 100;
    var xs = (c + delta).toFixed(2);
    var xc = 'x' + (c > 0 ? '-' + c : '+' + (-c));
    return { q: '已知 ' + T('f(x)=' + polyTex(f)) + '，求 ' + T('f(' + xs + ')') + ' 的近似值（四捨五入至小數點後第二位）。',
             a: T(ans.toFixed(2)),
             h: '先找離 $' + xs + '$ 最近的整數 $x=' + c + '$，差 $' + delta + '$。把係數列 $' + hrow(f) + '$ 用綜合除法連除兩次 $' + xc + '$（也就是把 $f$ 寫成 $' + xc + '$ 的展開式）：第一次的餘式是 $f(' + c + ')$，第二次的餘式就是一次項的係數，也就是一次近似的斜率。近似值 $\\approx f(' + c + ')+\\text{斜率}\\times' + hpz(delta) + '$。',
             p: { f: f, c: c, delta: delta, ans: ans } };
  };

  /* 2-15 高次不等式：奇偶重根 */
  L2.highIneq = function (r) {
    var rs = r.shuffle([-3, -2, -1, 0, 1, 2, 3, 4]).slice(0, 3), ms = r.shuffle([1, 2, r.pick([1, 3])]);
    var rel = r.pick(['<', '<=', '>', '>=']), lead = r.pick([1, 1, -1]);
    var factors = rs.map(function (v, i) { return { r: v, m: ms[i] }; }), sol = solveSign(factors, lead, rel);
    var tex = (lead < 0 ? '-' : '') + factors.map(function (f) { return factTex(f.r) + (f.m > 1 ? '^{' + f.m + '}' : ''); }).join('');
    var srt = factors.slice().sort(function (u, v) { return u.r - v.r; });
    return { q: '解不等式 ' + T(tex + REL[rel] + '0') + '。',
             a: setTex(sol),
             h: '把每個根和它的次數標在數線上：' + srt.map(function (f) { return '$x=' + f.r + '$（' + f.m + ' 次）'; }).join('、') + '。最右邊那一段的符號就是首項係數的符號（本題 $' + (lead > 0 ? '1' : '-1') + '$），往左每經過一個根，奇次要變號、偶次不變號；' + ((rel === '<=' || rel === '>=') ? '因為含等號，每個根本身都要取進去（偶次根可能只是一個孤立的解）。' : '因為不含等號，每個根本身都不能取（偶次根若在解的區間內部就要挖掉）。'),
             p: { factors: factors.map(function (f) { return [f.r, f.m]; }), lead: lead, rel: rel, ans: sol } };
  };

  /* 2-16 由三次不等式的解反推係數 */
  L2.ineqFromSol = function (r) {
    var p, q, s; do { p = r.int(-4, 0); q = p + r.int(1, 3); s = q + r.int(1, 3); } while (p * q * s === 0);   /* 有根為 0 ⟹ 常數項 0，a 定不出來 */
    var a = r.pick([1, -1, 2, -2]);
    var f = polyScale(polyMul(polyMul([1, -p], [1, -q]), [1, -s]), a), sol = solveSign([{ r: p, m: 1 }, { r: q, m: 1 }, { r: s, m: 1 }], a > 0 ? 1 : -1, '<=');
    return { q: '設 ' + T('a,b,c') + ' 為實數。若三次不等式 ' + T('ax^{3}+bx^{2}+cx' + (f[3] < 0 ? '-' : '+') + Math.abs(f[3]) + '\\le0') + ' 的解為「' + setTex(sol) + '」，求 ' + T('(a,b,c)') + '。',
             a: T('(a,b,c)=(' + f.slice(0, 3).join(',') + ')'),
             h: '解區間的端點 $' + p + ',' + q + ',' + s + '$ 就是三根：設 $a' + factTex(p) + factTex(q) + factTex(s) + '$，用常數項 $' + f[3] + '$ 定 $a$，並用「最右邊區間的正負」核對 $a$ 的符號。',
             p: { roots: [p, q, s], d: f[3], ans: f.slice(0, 3) } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p 重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     用法：用 splice 腳本插在 var META_L1 之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     ══════════════════════════════════════════════════════════ */
  function pzT(n) { return n < 0 ? '(' + n + ')' : String(n); }                 /* 負數代入時加括號 */
  function rowT(c) { return c.join(',\\ '); }                                   /* 綜合除法的係數列 */
  function subT(c, v) {        /* 把 x=v 代進係數陣列 c 的寫法；v=1 只留係數，0 項與係數 1 都省略 */
    var n = c.length - 1, s = '', first = true;
    for (var i = 0; i <= n; i++) {
      var k = c[i], e = n - i;
      if (k === 0) continue;
      var sg = k < 0 ? '-' : (first ? '' : '+'), ab = Math.abs(k), body;
      if (e === 0 || v === 1) body = String(ab);
      else body = (ab === 1 ? '' : ab + '\\times ') + pzT(v) + (e === 1 ? '' : '^{' + e + '}');
      s += sg + body; first = false;
    }
    return s || '0';
  }
  function chainT(c, k) {      /* 綜合除法「乘 k 再加」的逐步文字 */
    var out = [], cur = c[0];
    for (var i = 1; i < c.length; i++) {
      var pr = cur * k, nx = pr + c[i];
      out.push('$' + cur + '\\times ' + pzT(k) + '=' + pr + '$，加上 $' + c[i] + '$ 得 $' + nx + '$');
      cur = nx;
    }
    return out.join('；');
  }
  function monoT(k, e) {       /* 單項式：-3x^{2}、4x、5 */
    if (e === 0) return String(k);
    return (k === 1 ? '' : (k === -1 ? '-' : String(k))) + (e === 1 ? 'x' : 'x^{' + e + '}');
  }
  function coefT(k, body, first) {      /* k·body，係數 ±1 省略、係數 0 整項略去 */
    if (k === 0) return '';
    var ab = Math.abs(k);
    return (k < 0 ? '-' : (first ? '' : '+')) + (ab === 1 ? '' : ab) + body;
  }
  function eqT(co, s1, c2, s2, rhs) {   /* co·s1 + c2·s2 = rhs（係數 1 省略、係數 0 略去） */
    var s = term(co, s1, true); s += term(c2, s2, s === '');
    return (s === '' ? '0' : s) + '=' + rhs;
  }
  function pairT(u, v) { return '(' + u + ',' + v + ')'; }

  var L1_H1 = {
    degOps: '這是「次數的運算」：先把 $f$、$g$ 想成最單純的單項式（只留最高次那一項），再看每個運算對指數做了什麼。',
    identCoef: '這是「恆等式換基底」：不要硬展開，先找能讓右邊某幾項一起變成 $0$ 的 $x$ 值代進去。',
    prodCoef: '這是「乘積的指定項係數」：不必展開整個乘積，只挑出「兩邊次數加起來剛好等於指定次數」的配對；係數總和則代 $x=1$。',
    synthDiv: '這是「綜合除法」：先把被除式的係數由高次排到常數（缺項補 $0$），再用除式的根一路「乘再加」。',
    hornerVal: '這是「秦九韶（綜合除法求值）」：把題目裡那個一直重複出現的數字看成 $x$，式子就變成一個多項式的值。',
    remThm: '這是「餘式定理反求係數」：除以一次式的餘式就是把那個根代進去的函數值，代完會得到未知係數的一次方程式。',
    rem2pts: '這是「除以二次式的餘式」：餘式最多一次，先設成 $ax+b$，再把兩個一次因式的根代進去。',
    factorThm: '這是「因式定理求係數」：是因式就代表把那個根代進去等於 $0$，兩個因式給你兩個方程式。',
    factorize: '這是「因式分解」：先試根找出一個一次因式，用綜合除法降次之後再分解剩下的二次式。',
    rootLoc: '這是「勘根定理」：把整數點的函數值一個一個算出來，看哪兩個相鄰的值一正一負。',
    vertex: '這是「配方求頂點」：先用對稱軸公式求頂點的 $x$ 坐標，再代回求 $y$；開口方向決定它是最大還是最小。',
    axisCond: '這是「對稱軸的偽裝」：$f(\\text{甲})=f(\\text{乙})$ 對所有 $t$ 成立，表示這兩個位置對稱，對稱軸就在它們的正中間。',
    shiftQuad: '這是「二次函數的平移」：先配方找到頂點，平移只改頂點、不改開口係數，最後再展開。',
    discrimDist: '這是「判別式與交點距離」：兩交點的距離就是兩根之差，用「和與積」把它平方成判別式。',
    intervalMax: '這是「區間最值」：先配方找對稱軸，再看對稱軸在不在區間裡，最值只會出現在頂點或端點。',
    alwaysPos: '這是「恆成立」：開口向上時，整條拋物線在 $x$ 軸上方（或不低於 $x$ 軸）就等於判別式的條件。',
    cubicCenter: '這是「三次函數的對稱中心」：中心的 $x$ 坐標由前兩項的係數決定，$y$ 坐標再把它代回去算。',
    linApprox: '這是「一次近似直線」：把多項式改寫成以 $(x-c)$ 為單位的展開式，只留常數項與一次項。',
    quadIneq: '這是「二次不等式」：先分解成兩個一次式的乘積，再用「兩根之間」與「兩根之外」判斷正負。',
    cubicIneq: '這是「三次不等式」：把根標在數線上，從最右邊的區間開始標號，每經過一個單根就變號一次。',
    fracIneq: '這是「分式不等式」：兩數相除與相乘同號，可以改看乘積，但分母為 $0$ 的那個點一定要挖掉。'
  };

  var L1_SOL = {};

  /* 1-1 次數的加減乘與合成 */
  L1_SOL.degOps = function (p) {
    var m = p.m, n = p.n;
    var NAME = { prod: '乘積：次數相加 $' + m + '+' + n + '=' + (m + n) + '$',
                 sum: '和：兩者次數不同，由高次的決定，仍是 $' + m + '$',
                 diff: '差：兩者次數不同，高次項消不掉，仍是 $' + m + '$',
                 comp: '合成 $f\\big(g(x)\\big)$：次數相乘 $' + m + '\\times ' + n + '=' + (m * n) + '$',
                 comp2: '合成 $g\\big(f(x)\\big)$：次數相乘 $' + n + '\\times ' + m + '=' + (n * m) + '$',
                 sq: '平方：自己乘自己，次數變兩倍 $' + m + '\\times 2=' + (2 * m) + '$',
                 quo: '商式：次數相減 $' + m + '-' + n + '=' + (m - n) + '$' };
    return ['把 $f$、$g$ 想成最單純的 $x^{' + m + '}$ 與 $x^{' + n + '}$：乘就是指數相加、除就是指數相減、合成是把 $x^{' + n + '}$ 代進去變成 $(x^{' + n + '})^{' + m + '}$（指數相乘）、加減則由次數高的那一項決定。',
      '逐項算：' + p.ops.map(function (k, i) { return '(' + (i + 1) + ') ' + NAME[k]; }).join('；') + '。',
      '所以四個答案依序是 ' + p.ans.map(function (v, i) { return '(' + (i + 1) + ') $' + v + '$'; }).join('　') + '。'];
  };

  /* 1-2 恆等式：換基底的係數 */
  L1_SOL.identCoef = function (p) {
    var s1 = p.s1, s2 = p.s2, a = p.ans[0], b = p.ans[1], c = p.ans[2], v2 = polyEval(p.poly, s2), d = s2 - s1;
    return ['右邊的前兩項都含有因式 $(x' + (s1 > 0 ? '-' + s1 : '+' + (-s1)) + ')$，所以代 $x=' + s1 + '$ 時它們都會變成 $0$，只剩下 $c$。',
      '代 $x=' + s1 + '$：左邊 $=' + subT(p.poly, s1) + '=' + polyEval(p.poly, s1) + '$，所以 $c=' + c + '$。',
      '再代 $x=' + s2 + '$：第一項含 $(x' + (s2 > 0 ? '-' + s2 : '+' + (-s2)) + ')$ 也變 $0$，左邊 $=' + subT(p.poly, s2) + '=' + v2 + '$，右邊 $=' + eqT(d, 'b', c, '', v2) + '$，解得 $b=' + b + '$。',
      '最後比較 $x^{2}$ 的係數：左邊是 $' + p.poly[0] + '$、右邊是 $a$，所以 $a=' + a + '$，答案 $(a,b,c)=(' + a + ',' + b + ',' + c + ')$。'];
  };

  /* 1-3 乘積中指定項的係數與係數總和 */
  L1_SOL.prodCoef = function (p) {
    var A = p.A, B = p.B, k = p.k, terms = [], parts = [];
    for (var i = 0; i < A.length; i++) for (var j = 0; j < B.length; j++) {
      var eA = A.length - 1 - i, eB = B.length - 1 - j;
      if (eA + eB === k && A[i] !== 0 && B[j] !== 0) {
        terms.push('$(' + monoT(A[i], eA) + ')(' + monoT(B[j], eB) + ')$ 給出 $' + pzT(A[i]) + '\\times ' + pzT(B[j]) + '=' + (A[i] * B[j]) + '$');
        parts.push(A[i] * B[j]);
      }
    }
    var a1 = polyEval(A, 1), b1 = polyEval(B, 1);
    return ['(1) 不必展開整個乘積：$x^{' + k + '}$ 只會從「次數相加等於 $' + k + '$」的配對跑出來。' + (terms.length ? '本題有 ' + terms.join('、') + '。' : '本題湊不出這樣的配對，所以係數是 $0$。'),
      '把這些貢獻加起來：$' + (parts.length ? parts.map(pzT).join('+') + '=' + p.ans[0] : '0') + '$，所以 $x^{' + k + '}$ 的係數是 $' + p.ans[0] + '$。',
      '(2) 係數總和就是 $f(1)$：$f(1)=(' + subT(A, 1) + ')(' + subT(B, 1) + ')=' + pzT(a1) + '\\times ' + pzT(b1) + '=' + p.ans[1] + '$。',
      '所以 (1) $' + p.ans[0] + '$　(2) $' + p.ans[1] + '$。'];
  };

  /* 1-4 綜合除法：除以 x-k */
  L1_SOL.synthDiv = function (p) {
    var c = p.c, k = p.k, q = p.ans.q, r = p.ans.r;
    return ['除式是 $x' + (k > 0 ? '-' + k : '+' + (-k)) + '$，它的根是 $' + k + '$，所以綜合除法左邊寫 $' + k + '$；被除式的係數由高次排到常數是 $' + rowT(c) + '$。',
      '首項 $' + c[0] + '$ 直接抄下來，接著一路「乘 $' + k + '$ 再加下一個係數」：' + chainT(c, k) + '。',
      '前面 ' + q.length + ' 個數 $' + rowT(q) + '$ 是商式的係數（次數比被除式少一次）、最後一個是餘式，所以商式 $' + polyTex(q) + '$，餘式 $' + r + '$。'];
  };

  /* 1-5 秦九韶：數字題偽裝的多項式 */
  L1_SOL.hornerVal = function (p) {
    var b = p.b, c = p.c;
    return ['題目裡的 $' + b + '$ 一直重複出現，把它看成 $x$：整個式子就是 $f(x)=' + polyTex(c) + '$ 在 $x=' + b + '$ 的值。',
      '求 $f(' + b + ')$ 用綜合除法最快（餘式定理）：係數列 $' + rowT(c) + '$，一路「乘 $' + b + '$ 再加」：' + chainT(c, b) + '。',
      '最後一格就是餘式，也就是 $f(' + b + ')$，所以答案是 $' + p.ans + '$。'];
  };

  /* 1-6 餘式定理反求係數 */
  L1_SOL.remThm = function (p) {
    var k = p.k, c = p.c, a = p.ans, ca = k * k, rest = polyEval([c[0], c[1], 0, c[3], c[4]], k);
    return ['餘式定理：$f(x)$ 除以 $x' + (k > 0 ? '-' + k : '+' + (-k)) + '$ 的餘式就是 $f(' + k + ')$，所以先把 $x=' + k + '$ 代進去。',
      '$f(' + k + ')=' + pzT(k) + '^{4}' + (c[1] ? (c[1] < 0 ? '-' : '+') + (Math.abs(c[1]) === 1 ? '' : Math.abs(c[1]) + '\\times ') + pzT(k) + '^{3}' : '') + '+' + pzT(k) + '^{2}a' + (c[3] ? (c[3] < 0 ? '-' : '+') + (Math.abs(c[3]) === 1 ? '' : Math.abs(c[3]) + '\\times ') + pzT(k) : '') + (c[4] ? (c[4] < 0 ? '-' : '+') + Math.abs(c[4]) : '') + '=' + eqT(ca, 'a', rest, '', p.R) + '$。',
      '解這個一次方程式：$' + (ca === 1 ? 'a' : ca + 'a') + '=' + (p.R - rest) + '$，所以 $a=' + a + '$。'];
  };

  /* 1-7 除以兩個一次式 → 除以二次式的餘式 */
  L1_SOL.rem2pts = function (p) {
    var u = p.p, v = p.q, m = p.ans[0], n = p.ans[1];
    return ['除式 $' + factTex(u) + factTex(v) + '$ 是二次的，餘式最多一次，設它是 $ax+b$：$f(x)=' + factTex(u) + factTex(v) + 'Q(x)+ax+b$。',
      '代 $x=' + u + '$：前面那一項變 $0$，得 $' + eqT(u, 'a', 1, 'b', p.r1) + '$（這就是 $f(' + u + ')$，由餘式定理等於 $' + p.r1 + '$）；同理代 $x=' + v + '$ 得 $' + eqT(v, 'a', 1, 'b', p.r2) + '$。',
      '兩式相減消掉 $b$：$' + eqT(u - v, 'a', 0, '', p.r1 - p.r2) + '$，得 $a=' + m + '$，回代得 $b=' + n + '$，所以餘式是 $' + polyTex([m, n]) + '$。'];
  };

  /* 1-8 因式定理求係數與第三個根 */
  L1_SOL.factorThm = function (p) {
    var u = p.p, v = p.q, d = p.c3, a = p.ans[0], b = p.ans[1], s = p.ans[2];
    return ['「有因式 $(x' + (u > 0 ? '-' + u : '+' + (-u)) + ')$」就是「$f(' + u + ')=0$」，同樣地 $f(' + v + ')=0$，兩個條件剛好解兩個未知數。',
      '代入 $f(x)=x^{3}+ax^{2}+bx' + (d < 0 ? '-' : '+') + Math.abs(d) + '$：$' + eqT(u * u, 'a', u, 'b', -(u * u * u + d)) + '$、$' + eqT(v * v, 'a', v, 'b', -(v * v * v + d)) + '$，聯立解得 $a=' + a + '$、$b=' + b + '$。',
      '第三個根用「三根之積 $=' + (-d) + '$」（常數項變號）最快：已知兩根之積是 $' + (u * v) + '$，所以第三根 $=\\dfrac{' + (-d) + '}{' + (u * v) + '}=' + s + '$。',
      '所以 $(a,b)=' + pairT(a, b) + '$，第三個根為 $' + s + '$。'];
  };

  /* 1-9 因式分解（有理數係數） */
  L1_SOL.factorize = function (p) {
    var facs = p.ans, root = -facs[0][1], quo = polyMul(facs[1], facs[2]);
    var cnt = {}, ord = [];
    facs.forEach(function (f) { var s = polyTex(f); if (!cnt[s]) { cnt[s] = 0; ord.push(s); } cnt[s]++; });
    var ansTex = ord.map(function (s) { return '(' + s + ')' + (cnt[s] > 1 ? '^{' + cnt[s] + '}' : ''); }).join('');
    return ['先找一個一次因式：試根（先試 $x=1$、$x=-1$，再用牛頓一次因式檢驗法試常數項的因數除以首項係數的因數）。本題 $f(' + root + ')=' + subT(p.c, root) + '=0$，所以 $(x' + (root > 0 ? '-' + root : '+' + (-root)) + ')$ 是因式。',
      '用綜合除法除以 $x' + (root > 0 ? '-' + root : '+' + (-root)) + '$（係數列 $' + rowT(p.c) + '$）降次，商式是 $' + polyTex(quo) + '$。',
      '再把這個二次式分解：$' + polyTex(quo) + '=' + (polyTex(facs[1]) === polyTex(facs[2]) ? '(' + polyTex(facs[1]) + ')^{2}' : '(' + polyTex(facs[1]) + ')(' + polyTex(facs[2]) + ')') + '$。',
      '所以 $' + ansTex + '$。'];
  };

  /* 1-10 勘根定理 */
  L1_SOL.rootLoc = function (p) {
    var vals = [], i;
    for (i = -3; i <= 3; i++) vals.push(polyEval(p.c, i));
    var tbl = vals.map(function (v, j) { return '$f(' + (j - 3) + ')=' + v + '$'; }).join('、');
    return ['勘根定理：連續的多項式函數如果在兩點的值一正一負，中間一定有根。所以先把 $-3$ 到 $3$ 的函數值全部算出來（用綜合除法比直接代入快）。',
      tbl + '。',
      '相鄰兩個值異號的地方是：' + p.ans.map(function (l) { return '$f(' + l + ')=' + vals[l + 3] + '$ 與 $f(' + (l + 1) + ')=' + vals[l + 4] + '$'; }).join('、') + '。',
      '所以必有實根的區間是 ' + p.ans.map(function (l) { return '$(' + l + ',' + (l + 1) + ')$'; }).join('、') + '。'];
  };

  /* 1-11 配方求頂點 */
  L1_SOL.vertex = function (p) {
    var a = p.a, b = p.b, c = p.c, h = F(p.ans.h[0], p.ans.h[1]), k = F(p.ans.k[0], p.ans.k[1]);
    return ['二次函數的對稱軸（頂點的 $x$ 坐標）是 $x=-\\dfrac{b}{2a}$：本題 $a=' + a + '$、$b=' + b + '$，所以 $x=-\\dfrac{' + pzT(b) + '}{2\\times ' + pzT(a) + '}=' + Fr.tex(h) + '$。',
      '頂點的 $y$ 坐標就是 $f$ 在這個 $x$ 的值，也可以用 $y=c-\\dfrac{b^{2}}{4a}$：本題 $c=' + c + '$、$b^{2}=' + (b * b) + '$、$4a=' + (4 * a) + '$，算得 $y=' + Fr.tex(k) + '$。',
      '$a=' + a + (a > 0 ? '\\gt 0$，開口向上，頂點是最低點' : '\\lt 0$，開口向下，頂點是最高點') + '，所以頂點 $\\left(' + Fr.tex(h) + ',' + Fr.tex(k) + '\\right)$，' + (a > 0 ? '最小值' : '最大值') + ' $' + Fr.tex(k) + '$。'];
  };

  /* 1-12 對稱軸的偽裝 */
  L1_SOL.axisCond = function (p) {
    var u = p.p, v = p.q, h = (u + v) / 2, b = p.ans[0], mn = p.ans[1];
    return ['$f(' + (u === 0 ? 't' : u + '+t') + ')=f(' + (v === 0 ? '-t' : v + '-t') + ')$ 對每一個 $t$ 都成立，表示這兩個位置的函數值永遠相等，它們一定對稱於同一條鉛直線。',
      '這兩個位置的正中間是 $x=\\dfrac{' + u + '+' + pzT(v) + '}{2}=' + h + '$（把 $t$ 想成離中心的距離），所以對稱軸是 $x=' + h + '$。',
      '首項係數是 $1$，對稱軸 $-\\dfrac{b}{2}=' + h + '$，所以 $b=' + b + '$。',
      '最小值就是頂點的 $y$：' + (h === 0 ? '$f(0)=' + mn + '$（就是常數項）' : '$f(' + h + ')=' + subT([1, b, p.c], h) + '=' + mn + '$') + '。所以 $b=' + b + '$，最小值 $' + mn + '$。'];
  };

  /* 1-13 二次函數的平移 */
  L1_SOL.shiftQuad = function (p) {
    var f = p.f, h1 = -f[1] / (2 * f[0]), k1 = polyEval(f, h1), a = f[0], g = p.ans;
    var h2 = h1 + p.h, k2 = k1 + p.k;
    return ['先配方找頂點：$y=' + polyTex(f) + '=' + (a === 1 ? '' : (a === -1 ? '-' : a)) + (h1 === 0 ? 'x^{2}' : '(x' + (h1 > 0 ? '-' + h1 : '+' + (-h1)) + ')^{2}') + (k1 === 0 ? '' : (k1 > 0 ? '+' + k1 : '-' + (-k1))) + '$，頂點是 $' + pairT(h1, k1) + '$。',
      '平移不會改變開口，只是把頂點搬家：' + (p.h > 0 ? '向右 $' + p.h + '$' : '向左 $' + (-p.h) + '$') + '、' + (p.k > 0 ? '向上 $' + p.k + '$' : '向下 $' + (-p.k) + '$') + '，新頂點是 $' + pairT(h2, k2) + '$。',
      '寫回標準式再展開：$y=' + (a === 1 ? '' : (a === -1 ? '-' : a)) + (h2 === 0 ? 'x^{2}' : '(x' + (h2 > 0 ? '-' + h2 : '+' + (-h2)) + ')^{2}') + (k2 === 0 ? '' : (k2 > 0 ? '+' + k2 : '-' + (-k2))) + '=' + polyTex(g) + '$，所以 $y=' + polyTex(g) + '$。'];
  };

  /* 1-14 判別式：兩交點距離 */
  L1_SOL.discrimDist = function (p) {
    var b = p.b, d = p.d, k = p.ans;
    return ['設兩個交點的 $x$ 坐標是 $\\alpha,\\beta$（也就是 $f(x)=0$ 的兩根），則 $\\overline{PQ}=|\\alpha-\\beta|$；由根與係數：$\\alpha+\\beta=' + (-b) + '$、$\\alpha\\beta=k$。',
      '把距離平方化成和與積：$(\\alpha-\\beta)^{2}=(\\alpha+\\beta)^{2}-4\\alpha\\beta=' + (b * b) + '-4k$，而題目說它等於 $' + d + '^{2}=' + (d * d) + '$。',
      '解 $' + (b * b) + '-4k=' + (d * d) + '$：$4k=' + (b * b - d * d) + '$，所以 $k=' + k + '$。'];
  };

  /* 1-15 區間最值 */
  L1_SOL.intervalMax = function (p) {
    var f = p.f, a = f[0], h = -f[1] / (2 * f[0]), k = polyEval(f, h), lo = p.lo, hi = p.hi;
    var inside = (lo <= h && h <= hi), vs = ['$f(' + lo + ')=' + polyEval(f, lo) + '$', '$f(' + hi + ')=' + polyEval(f, hi) + '$'];
    if (inside) vs.push('頂點 $f(' + h + ')=' + k + '$');
    return ['先配方：$f(x)=' + (a === 1 ? '' : (a === -1 ? '-' : a)) + (h === 0 ? 'x^{2}' : '(x' + (h > 0 ? '-' + h : '+' + (-h)) + ')^{2}') + (k === 0 ? '' : (k > 0 ? '+' + k : '-' + (-k))) + '$，對稱軸 $x=' + h + '$，開口向' + (a > 0 ? '上' : '下') + '。',
      '對稱軸' + (inside ? '落在區間 $' + lo + '\\le x\\le ' + hi + '$ 內，最值只可能出現在頂點或兩個端點' : '落在區間 $' + lo + '\\le x\\le ' + hi + '$ 外，函數在這一段上單調，最值只在兩個端點') + '：' + vs.join('、') + '。',
      '比大小：最大值 $M=' + p.ans[0] + '$，最小值 $m=' + p.ans[1] + '$。'];
  };

  /* 1-16 恆成立：判別式 */
  L1_SOL.alwaysPos = function (p) {
    var u = p.u, v = p.v, con = term(p.pp, 'm', true) + term(p.nn, '', false);
    var d4 = 'm^{2}' + term(-p.pp, 'm', false) + term(-p.nn, '', false);
    var strict = (p.rel === '>');
    return ['首項係數是 $1\\gt 0$，圖形開口向上；要讓它對每一個 $x$ 都' + (strict ? '大於 $0$（整條在 $x$ 軸上方，不能碰到）' : '大於或等於 $0$（可以碰到 $x$ 軸）') + '，只要判別式 ' + (strict ? '$\\lt 0$' : '$\\le 0$') + ' 就夠了。',
      '算判別式（一次項係數是偶數，用 $\\dfrac{D}{4}$ 比較快）：$\\dfrac{D}{4}=m^{2}-(' + con + ')=' + d4 + '$，所以要解 $' + d4 + (strict ? '\\lt ' : '\\le ') + '0$。',
      '分解：$' + d4 + '=(m' + (u > 0 ? '-' + u : '+' + (-u)) + ')(m' + (v > 0 ? '-' + v : '+' + (-v)) + ')$，開口向上的二次式' + (strict ? '小於 $0$ 就是在兩根之間（端點不取）' : '小於或等於 $0$ 就是在兩根之間（端點要取）') + '。',
      '所以 $' + u + (strict ? '\\lt m\\lt ' : '\\le m\\le ') + v + '$。'];
  };

  /* 1-17 三次函數的對稱中心 */
  L1_SOL.cubicCenter = function (p) {
    var f = p.f, h = p.ans[0], k = p.ans[1];
    return ['三次函數 $f(x)=ax^{3}+bx^{2}+cx+d$ 的圖形對稱中心，$x$ 坐標是 $-\\dfrac{b}{3a}$：本題 $a=' + f[0] + '$、$b=' + f[1] + '$，所以 $x=-\\dfrac{' + pzT(f[1]) + '}{3\\times ' + pzT(f[0]) + '}=' + h + '$。',
      '$y$ 坐標就是 $f(' + h + ')$：用綜合除法（係數列 $' + rowT(f) + '$，除以 $x' + (h > 0 ? '-' + h : '+' + (-h)) + '$）的餘式，$f(' + h + ')=' + k + '$。',
      '所以對稱中心是 $' + pairT(h, k) + '$。'];
  };

  /* 1-18 一次近似直線 */
  L1_SOL.linApprox = function (p) {
    var f = p.f, c = p.c, m = p.ans[0], n = p.ans[1], y0 = polyEval(f, c);
    var xc = 'x' + (c > 0 ? '-' + c : '+' + (-c));
    return ['一次近似就是把 $f$ 改寫成以 $(' + xc + ')$ 為單位的展開式 $c_{0}+c_{1}(' + xc + ')+c_{2}(' + xc + ')^{2}+\\cdots$，只留前兩項；$c_{0},c_{1}$ 用連續綜合除法求。',
      '係數列 $' + rowT(f) + '$ 除以 $' + xc + '$：餘式 $c_{0}=f(' + c + ')=' + y0 + '$；對商式再除一次 $' + xc + '$：餘式 $c_{1}=' + m + '$。',
      '所以近似直線是 $y=' + ((y0 === 0 ? '' : String(y0)) + coefT(m, '(' + xc + ')', y0 === 0) || '0') + '$，展開整理得 $y=' + polyTex([m, n]) + '$。'];
  };

  /* 1-19 二次不等式 */
  L1_SOL.quadIneq = function (p) {
    var f = p.f, a = f[0], u = p.factors[0][0], v = p.factors[1][0], rel = p.rel;
    var eq = (rel === '<=' || rel === '>=');
    return ['先分解成兩個一次式：$' + polyTex(f) + '=' + (a === 1 ? '' : (a === -1 ? '-' : a)) + factTex(u) + factTex(v) + '$，兩根是 $' + u + '$ 與 $' + v + '$。',
      (a > 0 ? '開口向上（首項係數 $' + a + '\\gt 0$）：兩根之間函數值為負、兩根之外為正。' : '開口向下（首項係數 $' + a + '\\lt 0$）：可以先兩邊同除以負數並把不等號反向，也可以直接記「兩根之間為正、兩根之外為負」。') + (eq ? '因為不等號含等號，兩個根本身也要算進解。' : '因為不等號不含等號，兩個根本身不能算進解。'),
      '所以解是 ' + setTex(p.ans) + '。'];
  };

  /* 1-20 已分解的三次不等式 */
  L1_SOL.cubicIneq = function (p) {
    var rs = p.roots.slice().sort(function (a, b) { return a - b; }), lead = p.lead, rel = p.rel;
    var eq = (rel === '<=' || rel === '>=');
    var sgn = [], s = lead;
    for (var i = 0; i < 4; i++) { sgn.push(s > 0 ? '正' : '負'); s = -s; }
    return ['三個根由小到大是 $' + rowT(rs) + '$，它們把數線切成四段：$x\\lt ' + rs[0] + '$、$' + rs[0] + '\\lt x\\lt ' + rs[1] + '$、$' + rs[1] + '\\lt x\\lt ' + rs[2] + '$、$x\\gt ' + rs[2] + '$。',
      '最右邊那一段的符號就是首項係數的符號（本題 $' + (lead > 0 ? '1' : '-1') + '$，所以是' + sgn[0] + '），每往左經過一個單根就變號一次，因此四段由右往左依序是' + sgn.join('、') + '。',
      '挑出符合 $' + REL[rel] + '0$ 的區段' + (eq ? '（三個根本身也要取）' : '（三個根本身不取）') + '，所以解是 ' + setTex(p.ans) + '。'];
  };

  /* 1-21 分式不等式 */
  L1_SOL.fracIneq = function (p) {
    var a = p.a, b = p.b, rel = p.rel, eq = (rel === '<=' || rel === '>=');
    var num = 'x' + (a > 0 ? '-' + a : (a < 0 ? '+' + (-a) : '')), den = 'x' + (b > 0 ? '-' + b : (b < 0 ? '+' + (-b) : ''));
    return ['兩個數相除的正負和相乘完全一樣，所以 $\\dfrac{' + num + '}{' + den + '}' + REL[rel] + '0$ 可以改成 $(' + num + ')(' + den + ')' + REL[rel] + '0$ 來解；但分母不能為 $0$，所以 $x\\ne ' + b + '$ 要先記起來。',
      '乘積的兩根是 $' + a + '$ 與 $' + b + '$，開口向上：兩根之間為負、兩根之外為正' + (eq ? '；含等號時分子的根 $x=' + a + '$ 可以取，但分母的根 $x=' + b + '$ 一定要挖掉' : '；兩個根都不取') + '。',
      '所以解是 ' + setTex(p.ans) + '。'];
  };
  var META_L1 = [
      ['degOps', '§1 次數的運算'], ['identCoef', '§1 恆等式：換基底'], ['prodCoef', '§1 乘積的指定項係數'], ['synthDiv', '§1 綜合除法'], ['hornerVal', '§1 秦九韶求值'],
      ['remThm', '§2 餘式定理反求係數'], ['rem2pts', '§2 除以二次式的餘式'], ['factorThm', '§2 因式定理求係數'], ['factorize', '§2 因式分解'], ['rootLoc', '§2 勘根定理'],
      ['vertex', '§3 配方求頂點'], ['axisCond', '§3 對稱軸的偽裝'], ['shiftQuad', '§3 二次函數的平移'], ['discrimDist', '§3 判別式與交點距離'],
      ['intervalMax', '§4 區間最值'], ['alwaysPos', '§4 恆成立'],
      ['cubicCenter', '§5 三次函數的對稱中心'], ['linApprox', '§5 一次近似直線'],
      ['quadIneq', '§6 二次不等式'], ['cubicIneq', '§6 三次不等式（已分解）'], ['fracIneq', '§6 分式不等式']
  ];
  var META_L2 = [
      ['remQuadTwo', '§2 兩個二次條件拼第三個'], ['remSqr', '§2 x^n 除以 (x±1)²'], ['congRem', '§2 同餘：(x−k)f(x) 型'], ['vieta3', '§2 三次的根與係數'], ['cubicAP', '§2 三根成等差'],
      ['quadFromCond', '§3 由條件求二次函數'], ['quadThreePts', '§3 三點求二次函數'], ['intervalParam', '§4 區間最值含參數'], ['alwaysPosCount', '§4 恆成立：首項可為 0'], ['lineBelowParab', '§4 拋物線恆在直線上方'], ['profit', '§4 定價與最大利潤'],
      ['cubicCenterPts', '§5 對稱中心＋兩點'], ['cubicShift', '§5 平移後的標準式'], ['linApproxVal', '§5 一次近似求近似值'],
      ['highIneq', '§6 高次不等式：奇偶重根'], ['ineqFromSol', '§6 由解反推三次不等式']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     係數全部是整數／Fraction；p 只放旗標，驗算器一律從題幹重算。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};
  function sg(n) { return n < 0 ? '(' + n + ')' : String(n); }                    /* 負數加括號 */
  function lin2(m, n) { return polyTex([m, n]); }                                /* mx+n（m 可為 0） */
  function lineThru(x1, y1, x2, y2) { var m = (y2 - y1) / (x2 - x1); return [m, y1 - m * x1]; }

  /* L3-1　一串 b 的次方加起來：把 b 當 x，用綜合除法算 f(b) */
  L3.hornerParam = function (r) {
    var b = r.pick([7, 9, 11, 12, 13]), n = r.pick([4, 5]), hs = [r.pick([1, 1, 2])], c = [hs[0]], i;
    for (i = 1; i < n; i++) { hs.push(r.int(-3, 3)); c.push(hs[i] - b * hs[i - 1]); }
    var k = r.int(-9, 9), R = k + b * hs[n - 1];
    var parts = c.map(function (ci, j) {
      if (ci === 0) return '';
      var e = n - j, pw = e === 1 ? String(b) : b + '^{' + e + '}';
      return (ci < 0 ? '-' : (j === 0 ? '' : '+')) + (Math.abs(ci) === 1 ? '' : Math.abs(ci) + '\\times ') + pw;
    }).join('');
    return { q: '若 ' + T(parts + '+k=' + R) + '，求 ' + T('k') + '。', a: T('k=' + k),
      h: '左邊就是 $f(' + b + ')$，其中 $f(x)=' + polyTex(c.concat([0])) + '+k$。不要硬算 $' + b + '^{' + n + '}$：用綜合除法除以 $x-' + b + '$，係數 $' + c.join(',\\ ') + ',\\ k$ 依序「乘 $' + b + '$ 再加」，最後一格就是 $f(' + b + ')$。',
      p: { b: b, c: c, R: R, ans: k } };
  };

  /* L3-2　αf+βg 除以 x−a 的餘式：只要 f(a)、g(a) */
  L3.remLinCombo = function (r) {
    var a = r.int(-3, 3), b; do { b = r.int(-3, 4); } while (b === a);
    var m = r.nz(-4, 4), n = r.int(-6, 6), rf = r.int(-6, 8), al = r.pick([2, 3, -1, 4, 1]), be = r.pick([3, 2, -2, 5, -1]);
    var v = r.int(0, 1), at = v === 0 ? a : b, div = polyTex(polyMul([1, -a], [1, -b])), ga = m * at + n, ans = al * rf + be * ga;
    var combo = term(al, 'f(x)', true) + term(be, 'g(x)', false);
    return { q: '設 ' + T('f(x)') + ' 與 ' + T('g(x)') + ' 為實係數多項式，以 ' + T(div) + ' 除 ' + T('g(x)') + ' 得餘式 ' + T(lin2(m, n)) + '，以 ' + T('x' + term(-at, '', false)) + ' 除 ' + T('f(x)') + ' 得餘式 ' + T(String(rf)) + '。求 ' + T(combo) + ' 除以 ' + T('x' + term(-at, '', false)) + ' 的餘式。',
      a: T(String(ans)),
      h: '$' + div + '=' + factTex(a) + factTex(b) + '$ 含有因式 $' + factTex(at) + '$，所以 $g(' + at + ')$ 就是餘式 $' + lin2(m, n) + '$ 在 $x=' + at + '$ 的值；而 $f(' + at + ')=' + rf + '$。所求 $=' + term(al, 'f(' + at + ')', true) + term(be, 'g(' + at + ')', false) + '$。',
      p: { a: a, b: b, v: v, ans: ans } };
  };

  /* L3-3　被除式有一大塊含 (x−r) 的因式：代 x=r 直接歸零 */
  L3.remFactorTrick = function (r) {
    var r1 = r.nz(-4, 5), r2; do { r2 = r.int(-4, 5); } while (r2 === r1);
    var quad = polyMul([1, -r1], [1, -r2]), A = r.int(12, 2030), e1 = r.int(21, 60), e2 = r.int(7, 20), Bc = r.int(2, 19), C = r.int(1, 9), pp = r.nz(-9, 9), qq = r.int(-9, 9);
    var big = A + 'x^{' + e1 + '}+' + Bc + 'x^{' + e2 + '}+' + C, ans = pp * r1 + qq;
    return { q: '設 ' + T('f(x)=(' + polyTex(quad) + ')(' + big + ')' + (pp > 0 ? '+' : '') + lin2(pp, qq)) + '，求 ' + T('f(x)') + ' 除以 ' + T('x' + term(-r1, '', false)) + ' 的餘式。', a: T(String(ans)),
      h: '餘式定理：所求 $=f(' + r1 + ')$。先看 $' + polyTex(quad) + '$ 能不能分解出 $' + factTex(r1) + '$——可以的話，前面那一大塊在 $x=' + r1 + '$ 時整個是 $0$，根本不必管 $x^{' + e1 + '}$，只剩 $' + lin2(pp, qq) + '$ 要代。',
      p: { r1: r1, r2: r2, ans: ans } };
  };

  /* L3-4　除以 (x−a)² 與 (x−b)² 的餘式（多選）：先取 f(a)、f(b)，再逐項判斷 */
  L3.remSquares = function (r) {
    var a, b, m1, n1, m2, n2, fa, fb, tries = 0, opts, truth, nT;
    do {
      a = r.int(-2, 2); b = a + r.pick([1, 1, 2]); m2 = r.nz(-3, 4); n2 = r.int(-5, 6); m1 = r.nz(-3, 4);
      var mode = r.int(0, 2);                                   /* 0：兩條餘式線在 x=a 同值；1：在 x=b 同值；2：都不同 */
      n1 = mode === 0 ? (m2 * a + n2) - m1 * a : mode === 1 ? (m2 * b + n2) - m1 * b : r.int(-5, 6);
      fa = m1 * a + n1; fb = m2 * b + n2;
      var L = lineThru(a, fa, b, fb), okL = L[0] === Math.round(L[0]) && L[1] === Math.round(L[1]);
      var w1 = r.int(0, 1), w2 = r.int(0, 1), w3 = r.int(0, 1);
      var s3 = w3 ? lin2(L[0], L[1]) : lin2(m2, n2);
      var t3 = w3 ? true : (m2 === L[0] && n2 === L[1]);
      opts = [T('f(' + a + ')=' + (w1 ? fa : fa + r.pick([-2, -1, 1, 2]))), T('f(x)') + ' 除以 ' + T('x' + term(-b, '', false)) + ' 的餘式為 ' + T(String(w2 ? fb : m1 * b + n1 === fb ? fb + 1 : m1 * b + n1)),
        T('f(x)') + ' 除以 ' + T(factTex(a) + factTex(b)) + ' 的餘式為 ' + T(s3),
        T('f(x)') + ' 除以 ' + T(factTex(a) + '^2' + factTex(b)) + ' 的餘式為 ' + T(lin2(m1, n1)),
        T('f(x)') + ' 除以 ' + T(factTex(a) + factTex(b) + '^2') + ' 的餘式為 ' + T(lin2(m2, n2))];
      truth = [!!w1, !!w2, t3, m1 * b + n1 === fb, m2 * a + n2 === fa];
      nT = truth.filter(Boolean).length;
    } while ((!okL || m1 === m2 && n1 === n2 || nT < 1 || nT > 4 || lin2(L[0], L[1]) === '0') && tries++ < 300);
    var ansT = truth.map(function (t, i) { return t ? '(' + (i + 1) + ')' : ''; }).join('');
    return { q: '若多項式 ' + T('f(x)') + ' 除以 ' + T(factTex(a) + '^2') + ' 的餘式為 ' + T(lin2(m1, n1)) + '，除以 ' + T(factTex(b) + '^2') + ' 的餘式為 ' + T(lin2(m2, n2)) + '，下列哪些正確？（可複選）<br>' + opts.map(function (o, i) { return '(' + (i + 1) + ') ' + o; }).join('　'),
      a: ansT,
      h: '除以 $' + factTex(a) + '^2$ 的餘式代 $x=' + a + '$ 仍是 $f(' + a + ')$：$f(' + a + ')=' + fa + '$、$f(' + b + ')=' + fb + '$。除以二次式 $' + factTex(a) + factTex(b) + '$ 的餘式是過這兩點的直線；除以三次式 $' + factTex(a) + '^2' + factTex(b) + '$ 的餘式是 $A' + factTex(a) + '^2+(' + lin2(m1, n1) + ')$，它「剛好就是 $' + lin2(m1, n1) + '$」的條件是 $A=0$，也就是 $' + lin2(m1, n1) + '$ 在 $x=' + b + '$ 的值要等於 $f(' + b + ')$。',
      p: { a: a, b: b, r1: [m1, n1], r2: [m2, n2], ans: truth.map(function (t) { return t ? 1 : 0; }) } };
  };

  /* L3-5　同一個 f 用兩種基底寫：令 t=x−h 展開，「沒有 t² 項」與「一次近似的斜率」各給一條 */
  L3.twoBasis = function (r) {
    var h = r.int(0, 3), u = r.pick([1, 2]), v; do { v = r.pick([1, 2, 3]); } while (v === u);
    var a = r.nz(-3, 3), c = r.int(-4, 5), d = r.int(-5, 6), bq = a * (v - u), m = c - a * u * u, fh = c * u + d, n = fh - m * h;
    var s1 = h - u, s3 = h + v;
    var lhs = 'a' + factTex(s1) + factTex(h) + factTex(s3) + '+b' + factTex(s1) + factTex(h) + '+c' + factTex(s1) + term(d, '', false);
    var rhs = 'p' + factTex(h) + '^3+q' + factTex(h) + '+r';
    return { q: '設 ' + T('f(x)=' + lhs + '=' + rhs) + '，已知 ' + T('y=f(x)') + ' 在 ' + T('x=' + h) + ' 附近的一次近似為 ' + T('y=' + lin2(m, n)) + '，求 ' + T('(a,b,c)') + '。',
      a: T('(a,b,c)=(' + a + ',' + bq + ',' + c + ')'),
      h: '右式是 $' + factTex(h) + '$ 的展開而且<b>缺二次項</b>；一次近似 $y=' + lin2(m, n) + '$ 給兩件事：$f(' + h + ')=' + fh + '$、一次項係數 $q=' + m + '$。令 $t=x' + term(-h, '', false) + '$，則 $x' + term(-s1, '', false) + '=t+' + u + '$、$x' + term(-s3, '', false) + '=t-' + v + '$，把左式展開成 $t$ 的多項式，再比較 $t^2$、$t$、常數三項。',
      p: { h: h, u: u, v: v, d: d, m: m, n: n, ans: [a, bq, c] } };
  };

  /* L3-6　f(g(x)) 除以 f(x+s)：除式先分解，只需代兩個值 */
  L3.composeRem = function (r) {
    var al, be, s, g, r1, r2, G1, G2, L, tries = 0, f;
    do {
      al = r.int(-4, 3); be = al + r.int(1, 5); s = r.nz(-3, 3); f = polyMul([1, -al], [1, -be]);
      g = r.int(0, 1) ? [1, 0, r.int(-4, 3), r.int(-3, 3)] : [1, r.int(-3, 3), r.int(-4, 4)];
      r1 = al - s; r2 = be - s; G1 = polyEval(f, polyEval(g, r1)); G2 = polyEval(f, polyEval(g, r2)); L = lineThru(r1, G1, r2, G2);
    } while ((L[0] !== Math.round(L[0]) || Math.abs(G1) > 3000 || Math.abs(G2) > 3000 || L[0] === 0) && tries++ < 500);      /* 餘式要真的是一次式 */
    var sT = 'x' + term(s, '', false);
    return { q: '設多項式 ' + T('f(x)=' + polyTex(f)) + '，求 ' + T('f(' + polyTex(g) + ')') + ' 除以 ' + T('f(' + sT + ')') + ' 的餘式。', a: T(lin2(L[0], L[1])),
      h: '先把除式算出來並分解：$f(' + sT + ')=' + polyTex(polyShift(f, s)) + '=' + factTex(r1) + factTex(r2) + '$。除式是二次，餘式是一次式（一條直線），只要知道被除式在 $x=' + r1 + '$ 與 $x=' + r2 + '$ 的值：先算裡面的 $' + polyTex(g) + '$，再代進 $f$。',
      p: { f: f, g: g, s: s, ans: L } };
  };

  /* L3-7　f(x±s)=f(x)+d：差值是常數 ⟹ f 只能是一次式 */
  L3.diffConst = function (r) {
    var s = r.pick([1, 1, 2, 3]), left = r.int(0, 1), m = r.nz(-4, 4), d = (left ? 1 : -1) * m * s, x0 = r.int(-2, 3), b = r.int(-6, 7), y0 = m * x0 + b;
    var up = d > 0, arg = 'x' + (left ? '+' : '-') + s;
    return { q: '將多項式函數 ' + T('y=f(x)') + ' 的圖形向' + (left ? '左' : '右') + '平移 ' + T(String(s)) + ' 單位，和 ' + T('y=f(x)') + ' 的圖形向' + (up ? '上' : '下') + '平移 ' + T(String(Math.abs(d))) + ' 單位，兩圖形恰好重合，即 ' + T('f(' + arg + ')=f(x)' + term(d, '', false)) + '；且 ' + T('f(' + x0 + ')=' + y0) + '。求多項式 ' + T('f(x)') + '。',
      a: T('f(x)=' + lin2(m, b)),
      h: '次數論證：若 $\\deg f=n\\ge2$，則 $f(' + arg + ')-f(x)$ 是 $n-1\\ge1$ 次，不可能恆等於常數 $' + d + '$，所以 $f$ 是一次式。設 $f(x)=mx+b$：$f(' + arg + ')-f(x)=' + (left ? '' : '-') + (s === 1 ? '' : s) + 'm=' + d + '$，再用 $f(' + x0 + ')=' + y0 + '$ 定 $b$。',
      p: { s: s, left: left, d: d, x0: x0, y0: y0, ans: [m, b] } };
  };

  /* L3-8　兩個括號都含 x²−2hx：換元 t=x²−2hx，但 t 的範圍要一起換（t ≥ −h²） */
  L3.substMin = function (r) {
    var h, A, Bc, C, S, t0, lo, inside, mn, tries = 0;
    do {
      h = r.int(1, 4) * r.sign(); A = r.int(-3, 8); Bc = A + r.int(2, 9); C = 2 * r.int(-6, 6) - ((A + Bc) % 2 === 0 ? 0 : 1);
      S = A + Bc + C; t0 = -S / 2; lo = -h * h; inside = t0 >= lo;
      mn = inside ? t0 * t0 + S * t0 + A * Bc : lo * lo + S * lo + A * Bc;
    } while ((S % 2 !== 0 || C === 0 || t0 === lo || Math.abs(mn) > 400) && tries++ < 500);
    var base = [1, -2 * h, 0], q1 = polyTex([1, -2 * h, A]), q2 = polyTex([1, -2 * h, Bc]), tail = polyTex([C, -2 * h * C, 0]);
    return { q: '設 ' + T('x') + ' 為實數，求 ' + T('f(x)=(' + q1 + ')(' + q2 + ')' + (C > 0 ? '+' : '') + tail) + ' 的最小值。', a: T(String(mn)),
      h: '令 $t=' + polyTex(base) + '=(x' + term(-h, '', false) + ')^2-' + h * h + '$，所以 $t\\ge-' + h * h + '$——<b>範圍要跟著換</b>。$f=(t' + term(A, '', false) + ')(t' + term(Bc, '', false) + ')' + term(C, 't', false) + '$ 是 $t$ 的二次式，頂點在 $t=' + t0 + '$：先看它在不在 $t\\ge-' + h * h + '$ 裡面，不在的話最小值發生在端點。',
      p: { h: h, A: A, B: Bc, C: C, inside: inside ? 1 : 0, ans: mn } };
  };

  /* L3-9　水平線截拋物線的弦長比：弦長只跟 (c−k)/a 有關，左右平移是障眼法 */
  L3.chordRatio = function (r) {
    var mn = r.pick([[3, 2], [2, 1], [3, 1], [4, 3], [5, 3], [5, 4], [4, 1]]), m = mn[0], n = mn[1], w = r.int(1, 3), c = r.int(-5, 20), H = r.int(7, 120), left = r.int(0, 1), down = r.int(0, 1);
    /* 向上平移 U：Γ2 的頂點高 k+U，弦變短（m>n）；向下平移：弦變長，比值反過來寫 n:m */
    var U = (m * m - n * n) * w, k = down ? c - n * n * w : c - m * m * w, ratio = down ? n + ':' + m : m + ':' + n;
    return { q: '將二次函數 ' + T('y=ax^2+k') + '（' + T('a\\gt 0') + '）的圖形 ' + T('\\Gamma_1') + ' 向' + (left ? '左' : '右') + '平移 ' + T(String(H)) + ' 單位、再向' + (down ? '下' : '上') + '平移 ' + T(String(U)) + ' 單位得 ' + T('\\Gamma_2') + '。若水平線 ' + T('y=' + c) + ' 與 ' + T('\\Gamma_1') + ' 交於 ' + T('A,B') + '、與 ' + T('\\Gamma_2') + ' 交於 ' + T('C,D') + '，且 ' + T('\\overline{AB}:\\overline{CD}=' + ratio) + '，求 ' + T('k') + '。',
      a: T('k=' + k),
      h: '$y=a(x-h)^2+k$ 被水平線 $y=c$ 截出的弦長是 $2\\sqrt{\\dfrac{c-k}{a}}$，與 $h$ 無關——左右平移 $' + H + '$ 只是障眼法。$\\Gamma_2$ 的頂點高度是 $k' + (down ? '-' : '+') + U + '$。把弦長比平方：$\\dfrac{' + c + '-k}{' + c + '-(k' + (down ? '-' : '+') + U + ')}=\\dfrac{' + (down ? n * n : m * m) + '}{' + (down ? m * m : n * n) + '}$。',
      p: { c: c, U: down ? -U : U, ratio: down ? [n, m] : [m, n], ans: k } };
  };

  /* L3-10　三個函數值相同：f(x)−v 有三個已知根，只剩首項係數 */
  L3.sameValuesCubic = function (r) {
    var rs = r.shuffle([-3, -2, -1, 0, 1, 2, 3, 4]).slice(0, 3).sort(function (x, y) { return x - y; }), a = r.pick([1, -1, 2, -2, 3, -3]), v = r.int(-5, 7), x0;
    do { x0 = r.int(-4, 5); } while (rs.indexOf(x0) >= 0);
    var prod = polyMul(polyMul([1, -rs[0]], [1, -rs[1]]), [1, -rs[2]]), f = polyAdd(polyScale(prod, a), [v]), y0 = polyEval(f, x0);
    return { q: '已知 ' + T('f(x)') + ' 為三次多項式，滿足 ' + T('f(' + rs[0] + ')=f(' + rs[1] + ')=f(' + rs[2] + ')=' + v) + '，且 ' + T('f(' + x0 + ')=' + y0) + '，求 ' + T('f(x)') + '（降冪排列）。', a: T('f(x)=' + polyTex(f)),
      h: '$f(x)' + term(-v, '', false) + '$ 在 $x=' + rs.join(',\\ ') + '$ 都是 $0$，又是三次式 ⟹ $f(x)' + term(-v, '', false) + '=a' + factTex(rs[0]) + factTex(rs[1]) + factTex(rs[2]) + '$，只剩 $a$ 要定：代 $x=' + x0 + '$。',
      p: { rs: rs, v: v, x0: x0, y0: y0, ans: f } };
  };

  /* L3-11　對稱中心在 x 軸上＋兩個截點：設 a(x−h)³+p(x−h) */
  L3.centerCubic = function (r) {
    var h, d1; do { h = r.nz(-3, 3); d1 = r.pick([1, 2, 3]); } while (Math.abs(h) === d1);
    var a = r.pick([1, -1, 2, -2]), side = r.sign(), x1 = h + side * d1, pc = -a * d1 * d1;
    var f = polyAdd(polyScale(polyShift([1, 0, 0, 0], -h), a), polyScale([1, -h], pc)), y0 = polyEval(f, 0);
    return { q: '已知三次函數 ' + T('y=f(x)') + ' 的圖形對稱中心為 ' + T(pt(h, 0)) + '，與 ' + T('x') + ' 軸有交點 ' + T(pt(x1, 0)) + '，與 ' + T('y') + ' 軸交於 ' + T(pt(0, y0)) + '，求 ' + T('f(x)') + '（降冪排列）。', a: T('f(x)=' + polyTex(f)),
      h: '對稱中心 $' + pt(h, 0) + '$ ⟹ $f(x)=a' + factTex(h) + '^3+p' + factTex(h) + '$（常數項 $k=0$）。代 $' + pt(x1, 0) + '$ 得 $p$ 與 $a$ 的關係，再代 $' + pt(0, y0) + '$ 定出 $a$。最後可以檢查：三個根應該對稱於 $x=' + h + '$。',
      p: { h: h, x1: x1, y0: y0, ans: f } };
  };

  /* L3-12　三個二次因式相乘的不等式：恆正的丟掉、負首項的翻號，數整數解 */
  L3.tripleQuadIneq = function (r) {
    var p1, p2, bq, cq, u, w, rel, ints, tries = 0, Q1, Q2, Q3;
    do {
      p1 = r.int(-6, 1); p2 = p1 + r.int(3, 8); Q1 = polyScale(polyMul([1, -p1], [1, -p2]), -1);
      bq = r.int(-2, 2); cq = Math.floor(bq * bq / 4) + r.int(1, 3); Q2 = [1, bq, cq];
      var a3 = r.pick([1, 1, 2]); u = r.int(-3, 3); w = -r.int(1, 7); Q3 = [a3, u, w]; rel = r.pick(['>', '>=']);
      ints = []; for (var x = -30; x <= 30; x++) { var val = polyEval(Q1, x) * polyEval(Q2, x) * polyEval(Q3, x); if (rel === '>' ? val > 0 : val >= 0) ints.push(x); }
    } while ((ints.length < 1 || ints.length > 9 || bq * bq - 4 * cq >= 0) && tries++ < 300);
    var qs = r.shuffle([Q1, Q3]).concat([Q2]), disc = u * u - 4 * Q3[0] * w, sq = Math.round(Math.sqrt(disc));
    return { q: '不等式 ' + T(qs.map(function (c) { return '(' + polyTex(c) + ')'; }).join('') + REL[rel] + '0') + ' 共有多少個整數解？', a: T(String(ints.length)) + ' 個（' + T('x=' + ints.join(',\\ ')) + '）',
      h: '$' + polyTex(Q2) + '$ 的判別式 $' + (bq * bq - 4 * cq) + '\\lt 0$、首項為正 ⟹ 恆正，直接刪掉。$' + polyTex(Q1) + '=-' + factTex(p1) + factTex(p2) + '$，把負號移走後不等號<b>反向</b>。剩下 $' + polyTex(Q3) + '=0$ 的兩根' + (sq * sq === disc ? '可以因式分解求出' : '是無理數，用公式解估到小數一位') + '，四個根排上數線、從最右邊標正負，再數整數。',
      p: { Q1: Q1, Q2: Q2, Q3: Q3, rel: rel, ans: ints } };
  };

  /* L3-13　由二次不等式的解知道 a 的正負與兩根：b、c 用 a 表示，代進三次式提出 ax */
  L3.ineqToCubic = function (r) {
    var al, be, mm, nn, S, P, D, sq, r1, r2, inner, rel2, tries = 0;
    do {
      al = r.int(-5, 3); be = al + r.int(1, 7); S = al + be; P = al * be; mm = r.pick([1, 2, 3, -1, -2]); nn = r.pick([1, 2, -1, -2, 3, -3]);
      D = mm * mm * S * S - 4 * nn * P; sq = Math.round(Math.sqrt(Math.max(D, 0)));
      r1 = (mm * S - sq) / 2; r2 = (mm * S + sq) / 2;
    } while ((P === 0 || D <= 0 || sq * sq !== D || r1 !== Math.round(r1) || r1 === 0 || r2 === 0 || r1 === r2 || Math.abs(r1) > 12 || Math.abs(r2) > 12 || (mm === 1 && nn === 1)) && tries++ < 2000);
    inner = r.int(0, 1) === 0; rel2 = r.pick(['<', '>', '<=', '>=']);
    /* 內側解 α<x<β 且不等號為 >0 ⟹ a<0；外側解 ⟹ a>0。三次式 = a·x·(x−r1)(x−r2)（b=−aS、c=aP） */
    var aSign = inner ? -1 : 1, sol = solveSign([{ r: 0, m: 1 }, { r: r1, m: 1 }, { r: r2, m: 1 }], aSign, rel2);
    var given = inner ? al + '\\lt x\\lt ' + be : 'x\\lt ' + al + '\\ \\text{或}\\ x\\gt ' + be;
    var cubic = 'ax^3' + term(mm, 'bx^2', false) + term(nn, 'cx', false);
    return { q: '不等式 ' + T('ax^2+bx+c\\gt 0') + ' 的解為 ' + T(given) + '，求不等式 ' + T(cubic + REL[rel2] + '0') + ' 的解。', a: setTex(sol),
      h: '解在兩根' + (inner ? '之間' : '之外') + '且不等號是 $\\gt 0$ ⟹ $a' + (inner ? '\\lt ' : '\\gt ') + '0$，而且 $ax^2+bx+c=a' + factTex(al) + factTex(be) + '$，所以 $b=' + term(-S, 'a', true) + (S === 0 ? '0' : '') + '$、$c=' + term(P, 'a', true) + '$。代進三次式後整個提出 $ax$，括號裡是 $x$ 的二次式，再因式分解；最後別忘了 $a$ 的正負會不會讓不等號反向。',
      p: { al: al, be: be, inner: inner ? 1 : 0, mm: mm, nn: nn, rel: rel2, ans: sol } };
  };

  /* L3-14　連鎖不等式：拆成兩個二次不等式取交集 */
  L3.chainIneq = function (r) {
    var q1, q2, p1, p2, b, c, pieces, tries = 0, strict;
    do {
      q1 = r.int(-6, 2); q2 = q1 + r.int(2, 8); p1 = r.int(-7, 3); p2 = p1 + r.int(1, 7); b = r.pick([0, 0, 0, 1, -1, 2, -2]); c = r.int(-9, 6);
      pieces = []; if (q1 < p1) pieces.push([q1, Math.min(q2, p1)]); if (p2 < q2) pieces.push([Math.max(q1, p2), q2]);
      pieces = pieces.filter(function (iv) { return iv[0] < iv[1]; });
    } while ((pieces.length === 0 || p1 === q1 || p1 === q2 || p2 === q1 || p2 === q2 || (p1 <= q1 && q2 <= p2) ||      /* 端點重合時 ≤ 版會多出孤立點，避開 */ (b + p1 + p2 === 0 && c - p1 * p2 === 0) || (b + q1 + q2 === 0 && c - q1 * q2 === 0) || (p1 === q1 && p2 === q2)) && tries++ < 500);
    strict = r.int(0, 1) === 0; var op = strict ? '\\lt ' : '\\le ';
    var Lw = lin2(b + p1 + p2, c - p1 * p2), Rw = lin2(b + q1 + q2, c - q1 * q2), mid = polyTex([1, b, c]);
    var ansT = pieces.map(function (iv) { return T(iv[0] + op + 'x' + op + iv[1]); }).join(' 或 ');
    return { q: '求不等式 ' + T(Lw + op + mid + op + Rw) + ' 的解。', a: ansT,
      h: '連鎖不等式＝兩個不等式<b>同時</b>成立，分開解再取交集。右半：$' + mid + op + Rw + '$ 移項得 $' + polyTex(polyMul([1, -q1], [1, -q2])) + op + '0$；左半：$' + Lw + op + mid + '$ 移項得 $' + polyTex(polyMul([1, -p1], [1, -p2])) + (strict ? '\\gt ' : '\\ge ') + '0$。兩個都因式分解，畫在同一條數線上取重疊的部分。',
      p: { q: [q1, q2], pq: [p1, p2], b: b, c: c, strict: strict ? 1 : 0, ans: pieces } };
  };

  /* L3-15　「>0 無實數解」＝「≤0 恆成立」：開口方向＋判別式，首項係數為 0 要另外查 */
  L3.noSolParam = function (r) {
    var p0, al, be, e, d1, r1, r2, ga, de, rel, tries = 0;
    do {
      p0 = r.int(-2, 4); al = r.pick([1, 2, 3]); e = r.pick([1, 2, 3, -1, -2, -3]); be = e - al * p0;
      d1 = r.pick([1, e * e, Math.abs(e)]); r1 = p0 - d1; r2 = p0 + e * e / d1; ga = al * al + 1; de = 2 * al * be + p0 * ga - (r1 + r2);
    } while ((Math.abs(de) > 40 || Math.abs(r2) > 15) && tries++ < 200);
    rel = r.pick(['>', '>=', '<', '<=']);
    var ans = rel === '>' ? 'm\\le ' + r1 : rel === '>=' ? 'm\\lt ' + r1 : rel === '<' ? 'm\\ge ' + r2 : 'm\\gt ' + r2;
    var lead = '(m' + term(-p0, '', false) + ')', midc = '(' + lin2(al, be).replace(/x/g, 'm') + ')', cst = lin2(ga, de).replace(/x/g, 'm');
    if (p0 === 0) lead = 'm';
    var midFull = be === 0 ? (2 * al) + 'm' : '2' + midc;      /* be=0：2·(al m) 直接寫成 (2al)m */
    var flip = { '>': '\\le ', '>=': '\\lt ', '<': '\\ge ', '<=': '\\gt ' }[rel], down = rel === '>' || rel === '>=';
    return { q: '設 ' + T('m') + ' 為實數，已知不等式 ' + T(lead + 'x^2+' + midFull + 'x+(' + cst + ')' + REL[rel] + '0') + ' 無實數解，求 ' + T('m') + ' 的範圍。', a: T(ans),
      h: '「$' + REL[rel] + '0$ 無實數解」⟺「$' + flip + '0$ 對所有 $x$ 成立」⟺ 開口向' + (down ? '下' : '上') + '（$m' + term(-p0, '', false) + (down ? '\\lt ' : '\\gt ') + '0$）且判別式 $' + (rel === '>' || rel === '<' ? '\\le ' : '\\lt ') + '0$。$m=' + p0 + '$ 時它是一次不等式，一定有解，不合。算 $\\dfrac D4=' + midc + '^2-' + lead + '(' + cst + ')$ 再與開口條件取交集。',
      p: { p0: p0, al: al, be: be, ga: ga, de: de, rel: rel, r1: r1, r2: r2 } };
  };

  var META_L3 = [['hornerParam', '一串 b 的次方：綜合除法求值'], ['remLinCombo', 'αf+βg 的餘式'], ['remFactorTrick', '被除式含除式的因式'], ['remSquares', '除以 (x−a)² 與 (x−b)² 的餘式（多選）'], ['twoBasis', '同一個 f 用兩種基底寫'], ['composeRem', 'f(g(x)) 除以 f(x+s)'], ['diffConst', 'f(x+s)=f(x)+d 的次數論證'], ['substMin', '換元求最小值（範圍要跟著換）'], ['chordRatio', '水平線截拋物線的弦長比'], ['sameValuesCubic', '三個函數值相同求三次式'], ['centerCubic', '對稱中心＋截點求三次式'], ['tripleQuadIneq', '三個二次因式相乘的整數解'], ['ineqToCubic', '由二次不等式的解反推再解三次'], ['chainIneq', '連鎖不等式'], ['noSolParam', '不等式無實數解求參數']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'hornerParam', 'L3-2': 'remLinCombo', 'L3-3': 'remFactorTrick', 'L3-4': 'remSquares', 'L3-5': 'twoBasis', 'L3-6': 'composeRem', 'L3-7': 'diffConst', 'L3-8': 'substMin', 'L3-9': 'chordRatio', 'L3-10': 'sameValuesCubic', 'L3-11': 'centerCubic', 'L3-12': 'tripleQuadIneq', 'L3-13': 'ineqToCubic', 'L3-14': 'chainIneq', 'L3-15': 'noSolParam' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：多項式乘法展開、十字交乘因式分解、一元二次方程式、配方求頂點（國中）；過兩點的直線（高一上 ch2）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  L0.expandProd = function (r) {
    var a = r.pick([1, 1, 2, 3]), b = r.nz(-5, 5), c = r.pick([1, 1, 2, -1]), d = r.nz(-5, 5), A = [a, b], B = [c, d], prod = polyMul(A, B);
    return { q: '展開 ' + T('(' + polyTex(A) + ')(' + polyTex(B) + ')') + '，並依降冪排列。', a: T(polyTex(prod)),
      h: '四項都要乘到：$' + polyTex([a, 0]) + '\\cdot ' + sg2(polyTex([c, 0])) + '$、$' + polyTex([a, 0]) + '\\cdot ' + sg(d) + '$、$' + sg(b) + '\\cdot ' + sg2(polyTex([c, 0])) + '$、$' + sg(b) + '\\cdot ' + sg(d) + '$，同次項再合併。多項式的乘法、除法都從這裡開始。',
      p: { A: A, B: B, ans: prod } };
  };
  function sg2(s) { return s.charAt(0) === '-' ? '(' + s + ')' : s; }
  L0.factorQuad = function (r) {
    var lead = r.pick([1, 1, 1, 2, 3]), p, q; do { p = r.nz(-7, 7); q = r.nz(-7, 7); } while (gcd(lead, p) !== 1);      /* (2x-4) 這種還能再提公因數的不要 */
    var f = polyMul([lead, -p], [1, -q]);
    var f1 = lead === 1 ? factTex(p) : '(' + polyTex([lead, -p]) + ')', ans = p === q && lead === 1 ? factTex(p) + '^2' : f1 + factTex(q);
    return { q: '因式分解 ' + T(polyTex(f)) + '。', a: T(ans),
      h: '十字交乘：' + (lead === 1 ? '找兩個數，相乘是常數項 $' + f[2] + '$、相加是一次項係數 $' + f[1] + '$。' : '首項 $' + lead + 'x^2$ 拆成 $' + lead + 'x$ 與 $x$，常數項 $' + f[2] + '$ 拆成兩數，交叉相乘再相加要等於一次項係數 $' + f[1] + '$。') + '分解完乘回去檢查。解二次、三次不等式都要先做這一步。',
      p: { lead: lead, p: p, q: q, f: f } };
  };
  L0.quadRoots = function (r) {
    var v = r.int(0, 1), a, b, c, ans, D;
    if (v === 0) { do { a = r.pick([1, 1, 2]); b = r.int(-7, 7); c = r.int(-6, 6); D = b * b - 4 * a * c; } while (D <= 0 || Math.round(Math.sqrt(D)) * Math.round(Math.sqrt(D)) === D || c === 0);
      var k = 1, rem = D; for (var t = 2; t * t <= rem; t++) while (rem % (t * t) === 0) { rem /= t * t; k *= t; }
      var g = gcd(gcd(b, k), 2 * a), nb = -b / g, nk = k / g, den = 2 * a / g;
      var num = (nb === 0 ? '' : String(nb)) + '\\pm' + (nk === 1 ? '' : nk) + '\\sqrt{' + rem + '}';
      ans = T('x=' + (den === 1 ? num : '\\dfrac{' + num + '}{' + den + '}'));
      return { q: '用公式解求方程式 ' + T(polyTex([a, b, c]) + '=0') + ' 的解。', a: ans,
        h: '公式解 $x=\\dfrac{-b\\pm\\sqrt{b^2-4ac}}{2a}$：這題 $a=' + a + '$、$b=' + b + '$、$c=' + c + '$，判別式 $b^2-4ac=' + D + '$；根號要化簡，能約分的也要約。',
        p: { v: v, f: [a, b, c], D: D } }; }
    a = r.pick([1, 1, 2, -1]); b = r.int(-6, 6); c = r.int(-6, 9); D = b * b - 4 * a * c;
    var word = D > 0 ? '兩個相異實根' : D === 0 ? '兩個相等實根（重根）' : '沒有實根';
    return { q: '判斷方程式 ' + T(polyTex([a, b, c]) + '=0') + ' 的實根情形（兩相異實根、重根、或沒有實根）。', a: word + '（判別式 ' + T('D=' + D) + '）',
      h: '只要看判別式 $D=b^2-4ac$ 的正負：這題 $D=' + sg(b) + '^2-4\\cdot ' + sg(a) + '\\cdot ' + sg(c) + '$。$D\\gt 0$ 兩相異實根、$D=0$ 重根、$D\\lt 0$ 沒有實根——本章「恆正」「與 $x$ 軸的交點個數」都靠它。',
      p: { v: v, f: [a, b, c], D: D } };
  };
  L0.vertexForm = function (r) {
    var a = r.pick([1, 1, -1, 2, -2]), h = r.nz(-4, 4), k = r.int(-7, 7), f = [a, -2 * a * h, a * h * h + k];
    return { q: '將 ' + T('y=' + polyTex(f)) + ' 配方成 ' + T('y=a(x-h)^2+k') + ' 的形式，並寫出頂點坐標。', a: T('y=' + (a === 1 ? '' : a === -1 ? '-' : a) + '(x' + term(-h, '', false) + ')^2' + term(k, '', false)) + '，頂點 ' + T(pt(h, k)),
      h: (a === 1 ? '' : '先把 $x^2$ 的係數 $' + a + '$ 提出來（只提前兩項）：$' + a + '(x^2' + term(-2 * h, 'x', false) + ')' + term(f[2], '', false) + '$；再') + '取一次項係數 $' + (-2 * h) + '$ 的一半 $' + (-h) + '$ 來配方，補進去的平方要記得扣回來' + (a === 1 ? '' : '（外面還有係數 $' + a + '$，扣的是 $' + a + '\\times' + h * h + '$）') + '。',
      p: { f: f, ans: [a, h, k] } };
  };
  L0.lineTwoPts = function (r) {
    var x1 = r.int(-4, 3), x2 = x1 + r.pick([1, 2, 3, 4]), m = r.nz(-4, 4), n = r.int(-6, 6), y1 = m * x1 + n, y2 = m * x2 + n;
    return { q: '求過 ' + T(pt(x1, y1)) + '、' + T(pt(x2, y2)) + ' 兩點的直線方程式（寫成 ' + T('y=mx+n') + '）。', a: T('y=' + polyTex([m, n])),
      h: '先算斜率 $m=\\dfrac{' + sg(y2) + '-' + sg(y1) + '}{' + sg(x2) + '-' + sg(x1) + '}$，再用點斜式代其中一點。本章「除以二次式的餘式」就是在找過兩點的直線。',
      p: { P: [x1, y1], Q: [x2, y2], ans: [m, n] } };
  };
  var META_L0 = [['expandProd', '多項式乘法展開'], ['factorQuad', '十字交乘因式分解'], ['quadRoots', '公式解與判別式'], ['vertexForm', '配方求頂點'], ['lineTwoPts', '過兩點的直線']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    expandProd: { txt: '多項式的乘法展開（國中）——長除法、比較係數、換基底全部建立在它上面', link: null },
    factorQuad: { txt: '十字交乘因式分解（國中）——解二次、三次不等式之前一定要先分解', link: null },
    quadRoots: { txt: '一元二次方程式的公式解與判別式（國中）——「恆正」「與 x 軸交幾點」都在看判別式', link: null },
    vertexForm: { txt: '二次函數配方求頂點（國中）——最大最小值、平移、對稱軸都從頂點式出發', link: null },
    lineTwoPts: { txt: '過兩點的直線方程式（高一上第二章 直線與圓）——除以二次式的餘式就是過兩點的直線', link: '../g10a-ch02/practice.html#L1' }
  };

  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  var CONTRAST = {
    'L1.synthDiv': { f: function (p) { return p.k > 0; }, why: '除以 $x-k$ 時綜合除法左邊寫 $k$；除以 $x+k$ 時要寫 $-k$（讓除式等於 $0$ 的那個數）。這個正負號是綜合除法最常錯的地方。' },
    'L1.remThm': { f: function (p) { return p.k > 0; }, why: '餘式定理代的是「讓除式為 $0$ 的數」：除以 $x-k$ 代 $k$、除以 $x+k$ 代 $-k$。代負數時偶次方與奇次方的正負要分開看。' },
    'L1.vertex': { f: function (p) { return p.ans.min; }, why: '$x^2$ 的係數為正，開口向上，頂點是最低點（最小值）；係數為負，開口向下，頂點是最高點（最大值）。配方的過程完全一樣。' },
    'L1.shiftQuad': { f: function (p) { return p.h > 0; }, keep: ['k'], why: '向右平移 $h$ 是把 $x$ 換成 $x-h$，向左才是 $x+h$：圖形往右，式子裡反而是減。上下平移直接加在整個式子後面。' },
    'L1.intervalMax': { f: function (p) { var h = -p.f[1] / (2 * p.f[0]); return h >= p.lo && h <= p.hi; }, why: '頂點在區間內：一個最值在頂點、另一個在離頂點較遠的端點；頂點在區間外：函數在區間上單調，最大最小都在端點。先畫對稱軸再說。' },
    'L1.alwaysPos': { f: function (p) { return p.rel; }, why: '「$\\gt 0$ 恆成立」圖形不能碰到 $x$ 軸，判別式要 $\\lt 0$，端點不取；「$\\ge 0$ 恆成立」可以剛好碰到，判別式 $\\le 0$，端點要取。' },
    'L2.cubicAP': { f: function (p) { return p.t; }, why: '三根成等差都先設 $d-e,\\ d,\\ d+e$，由三根和定出中間那一根、代回求 $k$；後面問的量不同，只是最後一步用三根去算不同的東西。' },
    'L1.quadIneq': { f: function (p) { return p.lead; }, why: '首項係數是負的，先兩邊同乘 $-1$ 讓開口向上——<b>不等號要反向</b>；之後「小於 $0$ 取兩根之間、大於 $0$ 取兩根之外」。' },
    'L1.cubicIneq': { f: function (p) { return p.rel.charAt(0); }, why: '同一條數線、同一組正負號：要 $\\lt 0$ 就取負的區間，要 $\\gt 0$ 就取正的區間。從最右邊（一定是正的）往左，每過一個單根就變號。' },
    'L1.fracIneq': { f: function (p) { return p.rel.indexOf('=') >= 0; }, why: '分式不等式可以改看分子乘分母的正負，但<b>分母不能為 $0$</b>：含等號時，分子的根要收、分母的根永遠不能收。' },
    'L2.vieta3': { f: function (p) { return p.type; }, why: '三根的對稱式都從 $\\alpha+\\beta+\\gamma$、$\\alpha\\beta+\\beta\\gamma+\\gamma\\alpha$、$\\alpha\\beta\\gamma$ 三個基本量出發；問法不同，只是組合的方式不同。' },
    'L2.highIneq': { f: function (p) { return p.rel.indexOf('=') >= 0; }, why: '偶次重根不變號。不含等號時，它若落在解的區間裡要<b>挖掉</b>；含等號時，它若落在解的區間外反而是一個<b>孤立的解</b>。' },
    'L2.ineqFromSol': { f: function (p) { return p.ans[0] > 0; }, why: '由解的形狀判斷首項係數的正負：解往右無限延伸且是 $\\ge 0$（或往左延伸且是 $\\le 0$）⟹ $a\\gt 0$，反之 $a\\lt 0$。再用常數項定出 $a$ 的大小。' },
    'L2.cubicShift': { f: function (p) { return p.dh > 0; }, why: '對稱中心跟著圖形一起平移：向右 $h$ 中心的 $x$ 坐標加 $h$，向左則減；$a$ 與 $p$（形狀）平移後不變。' },
    'L3.diffConst': { f: function (p) { return p.left; }, why: '向左平移 $s$ 是 $f(x+s)$、向右是 $f(x-s)$：設 $f(x)=mx+b$ 後，一個得到 $ms$、一個得到 $-ms$，斜率的正負就差在這裡。' },
    'L3.substMin': { f: function (p) { return p.inside; }, why: '換元後 $t$ 有範圍：頂點在範圍內，最小值就是頂點值；頂點在範圍外，最小值發生在範圍的端點。直接用頂點值作答是最常見的錯。' },
    'L3.chordRatio': { f: function (p) { return p.U > 0; }, why: '開口向上的拋物線，頂點越高，同一條水平線截出的弦越短：向上平移弦變短、向下平移弦變長，比值的大小順序跟著換。' },
    'L3.tripleQuadIneq': { f: function (p) { return p.rel; }, why: '含等號時，因式的整數根本身也是解，要多數進去；不含等號時不算。恆正的因式兩種情況都可以直接丟掉。' },
    'L3.ineqToCubic': { f: function (p) { return p.inner; }, why: '$ax^2+bx+c\\gt 0$ 的解在兩根之間 ⟹ 開口向下、$a\\lt 0$；在兩根之外 ⟹ $a\\gt 0$。後面提出 $ax$ 之後，$a$ 的正負決定不等號要不要反向。' },
    'L3.chainIneq': { f: function (p) { return p.ans.length; }, why: '取交集時，「兩根之間」的那一段可能被「兩根之外」切成一段或兩段：把四個根畫在同一條數線上就看得出來。' },
    'L3.noSolParam': { f: function (p) { return p.rel; }, why: '「$\\gt 0$ 無解」⟺「$\\le 0$ 恆成立」：開口向下且 $D\\le 0$；「$\\ge 0$ 無解」⟺「$\\lt 0$ 恆成立」：開口向下且 $D\\lt 0$。差一個等號，答案的端點就差在含不含。' }
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, polyTex: polyTex, polyMul: polyMul, solveSign: solveSign, setTex: setTex } };
}));
