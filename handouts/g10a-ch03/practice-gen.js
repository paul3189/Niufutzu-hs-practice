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
    var m = r.int(4, 7), n = r.int(2, m - 1);
    return { q: '設 ' + T('\\deg f(x)=' + m) + '、' + T('\\deg g(x)=' + n) + '。求下列各式的次數：<br>(1) ' + T('f(x)\\,g(x)') + '　(2) ' + T('f(x)+g(x)') + '　(3) ' + T('f\\big(g(x)\\big)') + '　(4) ' + T('f(x)') + ' 除以 ' + T('g(x)') + ' 的商式',
             a: '(1) ' + T(String(m + n)) + '　(2) ' + T(String(m)) + '　(3) ' + T(String(m * n)) + '　(4) ' + T(String(m - n)),
             h: '乘積次數相加；次數不同的和取大的；合成次數相乘；商式次數＝被除式－除式。',
             p: { m: m, n: n, ans: [m + n, m, m * n, m - n] } };
  };

  /* 1-2 恆等式：換基底的係數 */
  L1.identCoef = function (r) {
    var pr = r.pick([[1, 2], [1, 3], [2, 3], [-1, 1], [-1, 2], [1, -2]]), s1 = pr[0], s2 = pr[1];
    var a = r.nz(-4, 4), b = r.nz(-6, 6), c = r.nz(-9, 9);
    var poly = polyAdd(polyAdd(polyScale(polyMul([1, -s1], [1, -s2]), a), polyScale([1, -s1], b)), [c]);
    return { q: '設 ' + T(polyTex(poly) + '=a' + factTex(s1) + factTex(s2) + '+b' + factTex(s1) + '+c') + ' 對所有實數 ' + T('x') + ' 均成立，求 ' + T('(a,b,c)') + '。',
             a: T('(a,b,c)=' + pt(a, b) .replace(')', ',' + c + ')')),
             h: '代 $x=' + s1 + '$ 先得 $c$，再代 $x=' + s2 + '$ 得 $b$；比較 $x^2$ 係數得 $a$。',
             p: { s1: s1, s2: s2, poly: poly, ans: [a, b, c] } };
  };

  /* 1-3 乘積中指定項的係數與係數總和 */
  L1.prodCoef = function (r) {
    var A = [r.nz(-3, 3), r.int(-4, 4), r.int(-4, 4), r.nz(-3, 3)], B = [r.nz(-3, 3), r.int(-4, 4), r.nz(-4, 4)];
    var P = polyMul(A, B), k = r.pick([2, 3, 4]), coef = P[P.length - 1 - k], sum = polyEval(P, 1);
    return { q: '設 ' + T('f(x)=(' + polyTex(A) + ')(' + polyTex(B) + ')') + '。<br>(1) 求 ' + T('f(x)') + ' 中 ' + T('x^{' + k + '}') + ' 項的係數。　(2) 求 ' + T('f(x)') + ' 的所有係數總和。',
             a: '(1) ' + T(String(coef)) + '　(2) ' + T(String(sum)),
             h: '指定項只挑「次數相加＝' + k + '」的配對相乘；係數總和就是 $f(1)$。',
             p: { A: A, B: B, k: k, ans: [coef, sum] } };
  };

  /* 1-4 綜合除法：除以 x-k */
  L1.synthDiv = function (r) {
    var c = [r.nz(-3, 3), r.int(-6, 6), r.int(-6, 6), r.int(-6, 6)], k = r.nz(-3, 3), d = synth(c, k);
    return { q: '用綜合除法求 ' + T(polyTex(c)) + ' 除以 ' + T(factTex(k).replace(/[()]/g, '')) + ' 的商式與餘式。',
             a: '商式 ' + T(polyTex(d.q)) + '，餘式 ' + T(String(d.r)),
             h: '把 $' + k + '$ 寫在左邊，係數一路「乘 $' + k + '$ 再加」；最後一格是餘式，也等於 $f(' + k + ')$。',
             p: { c: c, k: k, ans: { q: d.q, r: d.r } } };
  };

  /* 1-5 秦九韶：數字題偽裝的多項式 */
  L1.hornerVal = function (r) {
    var b = r.pick([7, 8, 9, 11, 12, 13]), g = [r.nz(-3, 3), r.int(-5, 5), r.int(-5, 5), r.int(-5, 5)], rem = r.int(-20, 20);
    var c = polyAdd(polyMul(g, [1, -b]), [rem]);
    var terms = c.map(function (k, i) { var e = 4 - i; if (e === 0 || k === 0) return null; return (k < 0 ? '-' : (i ? '+' : '')) + Math.abs(k) + '\\times ' + b + (e === 1 ? '' : '^{' + e + '}'); }).filter(Boolean).join('');
    return { q: '求 ' + T(terms + (c[4] < 0 ? '-' : '+') + Math.abs(c[4])) + ' 的值。',
             a: T(String(rem)),
             h: '把 $' + b + '$ 看成 $x$，問的是 $f(' + b + ')$，用綜合除法除以 $x-' + b + '$，最後一格就是答案。',
             p: { b: b, c: c, ans: rem } };
  };

  /* 1-6 餘式定理反求係數 */
  L1.remThm = function (r) {
    var a = r.nz(-6, 6), k = r.nz(-3, 3), c = [1, r.int(-4, 4), a, r.nz(-5, 5), r.nz(-6, 6)];
    var R = polyEval(c, k);
    var q = 'x^{4}' + (c[1] ? term(c[1], 'x^{3}', false) : '') + '+ax^{2}' + (c[3] ? term(c[3], 'x', false) : '') + (c[4] ? term(c[4], '', false) : '');
    return { q: '設 ' + T('f(x)=' + q) + '。若 ' + T('f(x)') + ' 除以 ' + T(factTex(k).replace(/[()]/g, '')) + ' 的餘式為 ' + T(String(R)) + '，求 ' + T('a') + '。',
             a: T('a=' + a),
             h: '餘式定理：餘式 $=f(' + k + ')$，代入後是 $a$ 的一次方程式。',
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
    return { q: '將 ' + T(polyTex(c)) + ' 在有理數係數範圍內完全因式分解。',
             a: T(facs.map(function (f) { return '(' + polyTex(f) + ')'; }).join('')),
             h: '先用 $\\pm$（常數項的因數）$/$（首項係數的因數）試根，找到一個根就綜合除法降次。',
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
             h: '列表算 $f(-3),f(-2),\\dots,f(3)$，相鄰兩值異號的區間必有根（勘根定理）。',
             p: { c: c, ans: ivs } };
  };

  /* 1-11 配方求頂點 */
  L1.vertex = function (r) {
    var a = r.pick([1, -1, 2, -2, 3]), b = r.nz(-8, 8), c = r.int(-6, 6);
    var h = F(-b, 2 * a), k = Fr.sub(F(c), F(b * b, 4 * a));
    return { q: '求二次函數 ' + T('f(x)=' + polyTex([a, b, c])) + ' 圖形的頂點坐標，並說明它是最大值還是最小值。',
             a: '頂點 ' + T('\\left(' + Fr.tex(h) + ',' + Fr.tex(k) + '\\right)') + '，' + (a > 0 ? '最小值' : '最大值') + ' ' + T(Fr.tex(k)),
             h: '頂點 $x=-\\dfrac b{2a}$，$y$ 坐標直接代回；$a\\gt0$ 開口向上是最小值。',
             p: { a: a, b: b, c: c, ans: { h: fr2(h), k: fr2(k), min: a > 0 } } };
  };

  /* 1-12 對稱軸的偽裝：f(p+t)=f(q-t) */
  L1.axisCond = function (r) {
    var h = r.int(-4, 4), d = r.int(1, 4), p = h - d, q = h + d, c = r.int(-9, 9);
    var b = -2 * h, mn = c - h * h;
    return { q: '設 ' + T('f(x)=x^{2}+bx' + (c < 0 ? '-' : '+') + Math.abs(c)) + '，且對任意實數 ' + T('t') + ' 都有 ' + T('f(' + p + '+t)=f(' + q + '-t)') + '。求 ' + T('b') + ' 與 ' + T('f(x)') + ' 的最小值。',
             a: T('b=' + b) + '，最小值 ' + T(String(mn)),
             h: '$f(' + p + '+t)=f(' + q + '-t)$ 表示對稱軸在 $' + p + '$ 與 $' + q + '$ 的正中間 $x=' + h + '$，於是 $-\\frac b2=' + h + '$。',
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
             h: '兩根之差 $=\\dfrac{\\sqrt{D}}{|a|}=\\sqrt{b^2-4k}$，令它等於 $' + d + '$。',
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
    return { q: '求 ' + T('f(x)=' + polyTex(f)) + ' 在 ' + T(lo + '\\le x\\le ' + hi) + ' 上的最大值 ' + T('M') + ' 與最小值 ' + T('m') + '。',
             a: T('M=' + M) + '，' + T('m=' + m),
             h: '配方得頂點 $x=' + h + '$；軸在區間內時頂點是一端的極值、離軸最遠的端點是另一端；軸在區間外就只看兩端點。',
             p: { f: f, lo: lo, hi: hi, ans: [M, m] } };
  };

  /* 1-16 恆成立：判別式 */
  L1.alwaysPos = function (r) {
    var s = r.int(1, 4), n = s * s + s;
    return { q: '若對所有實數 ' + T('x') + '，' + T('x^{2}-2mx+(m+' + n + ')\\gt0') + ' 恆成立，求實數 ' + T('m') + ' 的範圍。',
             a: T(-s + '\\lt m\\lt ' + (s + 1)),
             h: '首項係數 $1\\gt0$ 已定，只需判別式 $4m^2-4(m+' + n + ')\\lt0$，分解 $m^2-m-' + n + '=(m+' + s + ')(m-' + (s + 1) + ')$。',
             p: { n: n, ans: [-s, s + 1] } };
  };

  /* 1-17 三次函數的對稱中心 */
  L1.cubicCenter = function (r) {
    var a = r.pick([1, -1, 2, -2]), h = r.nz(-3, 3), p = r.int(-6, 6), k = r.int(-9, 9);
    var f = polyAdd(polyAdd(polyScale(polyMul(polyMul([1, -h], [1, -h]), [1, -h]), a), polyScale([1, -h], p)), [k]);
    return { q: '求三次函數 ' + T('f(x)=' + polyTex(f)) + ' 圖形的對稱中心。',
             a: T(pt(h, k)),
             h: '對稱中心 $x=-\\dfrac{b}{3a}$（$b$ 是 $x^2$ 的係數），$y$ 坐標代回算 $f(' + h + ')$。',
             p: { f: f, ans: [h, k] } };
  };

  /* 1-18 一次近似直線 */
  L1.linApprox = function (r) {
    var f = [r.pick([1, -1, 2]), r.int(-4, 4), r.int(-5, 5), r.int(-6, 6)], c = r.nz(-2, 2);
    var y0 = polyEval(f, c), m = polyEval(polyDeriv(f), c), n = y0 - m * c;
    return { q: '求 ' + T('y=' + polyTex(f)) + ' 的圖形在 ' + T('x=' + c) + ' 附近的一次近似直線。',
             a: T('y=' + polyTex([m, n])),
             h: '用綜合除法連除 $x' + (c > 0 ? '-' + c : '+' + (-c)) + '$ 兩次，餘式依序是 $c_0,c_1$，近似直線 $y=c_0+c_1(x' + (c > 0 ? '-' + c : '+' + (-c)) + ')$。',
             p: { f: f, c: c, ans: [m, n] } };
  };

  /* 1-19 二次不等式 */
  L1.quadIneq = function (r) {
    var p = r.int(-4, 3), q = p + r.int(1, 5), a = r.pick([1, 1, -1, 2]), rel = r.pick(['<', '<=', '>', '>=']);
    var f = polyScale(polyMul([1, -p], [1, -q]), a), sol = solveSign([{ r: p, m: 1 }, { r: q, m: 1 }], a > 0 ? 1 : -1, rel);
    return { q: '解不等式 ' + T(polyTex(f) + REL[rel] + '0') + '。',
             a: setTex(sol),
             h: '先分解成 $' + (a === 1 ? '' : a) + factTex(p) + factTex(q) + '$；' + (a > 0 ? '開口向上' : '開口向下，先把負號除掉並反向') + '，「兩根之間為負、兩根之外為正」。',
             p: { f: f, factors: [[p, 1], [q, 1]], lead: a > 0 ? 1 : -1, rel: rel, ans: sol } };
  };

  /* 1-20 已分解的三次不等式 */
  L1.cubicIneq = function (r) {
    var rs = r.shuffle([r.int(-4, 4), r.int(-4, 4), r.int(-4, 4)]);
    while (rs[1] === rs[0]) rs[1] = r.int(-4, 4);
    while (rs[2] === rs[0] || rs[2] === rs[1]) rs[2] = r.int(-4, 4);
    var lead = r.pick([1, 1, -1]), rel = r.pick(['<', '<=', '>', '>=']);
    var sol = solveSign(rs.map(function (v) { return { r: v, m: 1 }; }), lead, rel);
    return { q: '解不等式 ' + T((lead < 0 ? '-' : '') + rs.map(factTex).join('') + REL[rel] + '0') + '。',
             a: setTex(sol),
             h: '三個根標在數線上，最右邊的區間符號＝首項係數的符號，往左每過一個單根就變號一次。',
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
    for (var tries = 0; tries < 30 && (fA - fC) % (A - C) !== 0; tries++) { m2 = r.nz(-4, 4); fC = fB + m2 * (C - B); }
    if ((fA - fC) % (A - C) !== 0) { m2 = m1; fC = fB + m2 * (C - B); }
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
    var d = r.nz(-3, 3), e = r.int(1, 3), rs = [d - e, d, d + e];
    var c = polyMul(polyMul([1, -rs[0]], [1, -rs[1]]), [1, -rs[2]]);
    return { q: '設 ' + T('x^{3}' + term(c[1], 'x^{2}', false) + term(c[2], 'x', false) + '+k=0') + ' 的三根成等差數列，求 ' + T('k') + ' 與三根之積。',
             a: T('k=' + c[3]) + '，三根之積 ' + T(String(-c[3])),
             h: '三根設 $d-e,d,d+e$，三根和 $3d=' + (3 * d) + '$ ⟹ $d=' + d + '$ 是一根，代入求 $k$；三根之積 $=-k$。',
             p: { c: c, ans: [c[3], -c[3], rs] } };
  };

  /* 2-6 由對稱軸、y 截距、與 x 軸兩交點距離求二次函數 */
  L2.quadFromCond = function (r) {
    var h = r.int(-3, 3), half = r.int(1, 3), a = r.pick([1, -1, 2, -2]);
    var p = h - half, q = h + half, f = polyScale(polyMul([1, -p], [1, -q]), a), c = f[2];
    return { q: '二次函數 ' + T('y=ax^{2}+bx+c') + ' 的圖形對稱軸為 ' + T('x=' + h) + '，與 ' + T('y') + ' 軸交於 ' + T(pt(0, c)) + '，與 ' + T('x') + ' 軸交於 ' + T('A,B') + ' 兩點且 ' + T('\\overline{AB}=' + (2 * half)) + '。求 ' + T('(a,b,c)') + '。',
             a: T('(a,b,c)=(' + f.join(',') + ')'),
             h: '兩根在對稱軸兩側各 $' + half + '$：$x=' + p + ',' + q + '$，設 $y=a' + factTex(p) + factTex(q) + '$，再用 $y$ 截距定 $a$。',
             p: { h: h, half: half, c: c, ans: f } };
  };

  /* 2-7 由三個函數值求二次函數（拉格朗日／聯立） */
  L2.quadThreePts = function (r) {
    var a = r.nz(-3, 3), b = r.int(-5, 5), c = r.int(-6, 6), xs = r.shuffle([-2, -1, 0, 1, 2, 3]).slice(0, 3).sort(function (u, v) { return u - v; });
    var f = [a, b, c], ys = xs.map(function (x) { return polyEval(f, x); });
    return { q: '已知二次函數 ' + T('f(x)') + ' 滿足 ' + xs.map(function (x, i) { return T('f(' + x + ')=' + ys[i]); }).join('、') + '，求 ' + T('f(x)') + '。',
             a: T('f(x)=' + polyTex(f)),
             h: '設 $f(x)=ax^2+bx+c$ 代三點聯立；或用 $f(x)=p' + factTex(xs[0]) + factTex(xs[1]) + '+q' + factTex(xs[0]) + '+r$ 由左到右逐個代入。',
             p: { xs: xs, ys: ys, ans: f } };
  };

  /* 2-8 區間最值含參數（開口方向兩解） */
  L2.intervalParam = function (r) {
    var h = r.int(-2, 3), w = r.pick([1, 2, 3]), lo = h - w, hi = h;      /* 軸在右端點 */
    var diff = w * w * r.pick([1, 2]), m = r.int(-6, 4), M = m + diff;
    var aP = diff / (w * w), bP = m + aP * h * h, aN = -aP, bN = M + aN * h * h;
    var fTex = 'f(x)=ax^{2}' + term(-2 * h, 'ax', false) + '+b';
    if (h === 0) fTex = 'f(x)=ax^{2}+b';
    return { q: '已知二次函數 ' + T(fTex) + ' 在區間 ' + T(lo + '\\le x\\le ' + hi) + ' 的最大值為 ' + T(String(M)) + '、最小值為 ' + T(String(m)) + '，求數對 ' + T('(a,b)') + ' 的所有可能值。',
             a: T('(a,b)=' + pt(aP, bP)) + ' 或 ' + T(pt(aN, bN)),
             h: '配方 $f(x)=a' + factTex(h) + '^2+(b' + (h ? '-' + (h * h) + 'a' : '') + ')$，對稱軸 $x=' + h + '$ 剛好是右端點 ⟹ 區間內單調，最值只在兩端點，分 $a\\gt0$、$a\\lt0$ 兩種。',
             p: { h: h, lo: lo, hi: hi, M: M, m: m, ans: [[aP, bP], [aN, bN]] } };
  };

  /* 2-9 恆成立：別漏掉首項係數為 0 */
  L2.alwaysPosCount = function (r) {
    var c = r.int(-4, 4), n = r.int(3, 9);
    var q = '(m' + (c ? (c > 0 ? '+' + c : '-' + (-c)) : '') + ')x^{2}+2(m' + (c ? (c > 0 ? '+' + c : '-' + (-c)) : '') + ')x+' + n + '\\gt0';
    return { q: '設對任何實數 ' + T('x') + '，不等式 ' + T(q) + ' 恆成立。求滿足條件的整數 ' + T('m') + ' 共有幾個。',
             a: T(String(n)) + ' 個（' + T(-c + '\\le m\\lt ' + (n - c)) + '）',
             h: '先看 $m' + (c ? (c > 0 ? '+' + c : '-' + (-c)) : '') + '=0$：式子變成 $' + n + '\\gt0$ 成立！再看 $\\gt0$ 且 $D\\lt0$：$4t^2-4nt\\lt0$ ⟹ $0\\lt t\\lt ' + n + '$（$t$ 為首項係數）。',
             p: { c: c, n: n, ans: { count: n, lo: -c, hi: n - c } } };
  };

  /* 2-10 拋物線恆在直線上方 */
  L2.lineBelowParab = function (r) {
    var p = r.nz(-5, 5), s = r.int(1, 4), q = r.int(-5, 5), c = q + s * s;
    return { q: '若拋物線 ' + T('y=x^{2}+bx' + (c < 0 ? '-' : '+') + Math.abs(c)) + ' 的圖形恆在直線 ' + T('y=' + polyTex([p, q])) + ' 的上方，求實數 ' + T('b') + ' 的範圍。',
             a: T((p - 2 * s) + '\\lt b\\lt ' + (p + 2 * s)),
             h: '相減：$x^2+(b-' + p + ')x+' + (s * s) + '\\gt0$ 恆成立 ⟹ $(b-' + p + ')^2-4\\cdot' + (s * s) + '\\lt0$。',
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
             h: '設 $f(x)=a(x' + (h ? (h > 0 ? '-' + h : '+' + (-h)) : '') + ')^3+p(x' + (h ? (h > 0 ? '-' + h : '+' + (-h)) : '') + ')' + (k ? (k > 0 ? '+' + k : '-' + (-k)) : '') + '$，代兩點解 $a,p$。',
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
    return { q: '已知 ' + T('f(x)=' + polyTex(f)) + '，求 ' + T('f(' + xs + ')') + ' 的近似值（四捨五入至小數點後第二位）。',
             a: T(ans.toFixed(2)),
             h: '在 $x=' + c + '$ 附近用一次近似 $f(' + c + ')+f\'(' + c + ')\\cdot(' + delta + ')$：綜合除法連除兩次得 $f(' + c + ')$ 與斜率。',
             p: { f: f, c: c, delta: delta, ans: ans } };
  };

  /* 2-15 高次不等式：奇偶重根 */
  L2.highIneq = function (r) {
    var rs = r.shuffle([-3, -2, -1, 0, 1, 2, 3, 4]).slice(0, 3), ms = r.shuffle([1, 2, r.pick([1, 3])]);
    var rel = r.pick(['<', '<=', '>', '>=']), lead = r.pick([1, 1, -1]);
    var factors = rs.map(function (v, i) { return { r: v, m: ms[i] }; }), sol = solveSign(factors, lead, rel);
    var tex = (lead < 0 ? '-' : '') + factors.map(function (f) { return factTex(f.r) + (f.m > 1 ? '^{' + f.m + '}' : ''); }).join('');
    return { q: '解不等式 ' + T(tex + REL[rel] + '0') + '。',
             a: setTex(sol),
             h: '偶次重根不變號（但等於 0 的點要看是「孤立解」還是「挖洞」），奇次重根照單根處理，從最右邊往左標正負。',
             p: { factors: factors.map(function (f) { return [f.r, f.m]; }), lead: lead, rel: rel, ans: sol } };
  };

  /* 2-16 由三次不等式的解反推係數 */
  L2.ineqFromSol = function (r) {
    var p = r.int(-4, 0), q = p + r.int(1, 3), s = q + r.int(1, 3), a = r.pick([1, -1, 2, -2]);
    var f = polyScale(polyMul(polyMul([1, -p], [1, -q]), [1, -s]), a), sol = solveSign([{ r: p, m: 1 }, { r: q, m: 1 }, { r: s, m: 1 }], a > 0 ? 1 : -1, '<=');
    return { q: '設 ' + T('a,b,c') + ' 為實數。若三次不等式 ' + T('ax^{3}+bx^{2}+cx' + (f[3] < 0 ? '-' : '+') + Math.abs(f[3]) + '\\le0') + ' 的解為「' + setTex(sol) + '」，求 ' + T('(a,b,c)') + '。',
             a: T('(a,b,c)=(' + f.slice(0, 3).join(',') + ')'),
             h: '解區間的端點 $' + p + ',' + q + ',' + s + '$ 就是三根：設 $a' + factTex(p) + factTex(q) + factTex(s) + '$，用常數項 $' + f[3] + '$ 定 $a$，並用「最右邊區間的正負」核對 $a$ 的符號。',
             p: { roots: [p, q, s], d: f[3], ans: f.slice(0, 3) } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['degOps', '§1 次數的運算'], ['identCoef', '§1 恆等式：換基底'], ['prodCoef', '§1 乘積的指定項係數'], ['synthDiv', '§1 綜合除法'], ['hornerVal', '§1 秦九韶求值'],
      ['remThm', '§2 餘式定理反求係數'], ['rem2pts', '§2 除以二次式的餘式'], ['factorThm', '§2 因式定理求係數'], ['factorize', '§2 因式分解'], ['rootLoc', '§2 勘根定理'],
      ['vertex', '§3 配方求頂點'], ['axisCond', '§3 對稱軸的偽裝'], ['shiftQuad', '§3 二次函數的平移'], ['discrimDist', '§3 判別式與交點距離'],
      ['intervalMax', '§4 區間最值'], ['alwaysPos', '§4 恆成立'],
      ['cubicCenter', '§5 三次函數的對稱中心'], ['linApprox', '§5 一次近似直線'],
      ['quadIneq', '§6 二次不等式'], ['cubicIneq', '§6 三次不等式（已分解）'], ['fracIneq', '§6 分式不等式']
    ],
    L2: [
      ['remQuadTwo', '§2 兩個二次條件拼第三個'], ['remSqr', '§2 x^n 除以 (x±1)²'], ['congRem', '§2 同餘：(x−k)f(x) 型'], ['vieta3', '§2 三次的根與係數'], ['cubicAP', '§2 三根成等差'],
      ['quadFromCond', '§3 由條件求二次函數'], ['quadThreePts', '§3 三點求二次函數'], ['intervalParam', '§4 區間最值含參數'], ['alwaysPosCount', '§4 恆成立：首項可為 0'], ['lineBelowParab', '§4 拋物線恆在直線上方'], ['profit', '§4 定價與最大利潤'],
      ['cubicCenterPts', '§5 對稱中心＋兩點'], ['cubicShift', '§5 平移後的標準式'], ['linApproxVal', '§5 一次近似求近似值'],
      ['highIneq', '§6 高次不等式：奇偶重根'], ['ineqFromSol', '§6 由解反推三次不等式']
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

  return { makeRng: makeRng, L1: L1, L2: L2, META: META, _util: { gcd: gcd, F: F, Fr: Fr, polyTex: polyTex, polyMul: polyMul, solveSign: solveSign, setTex: setTex } };
}));
