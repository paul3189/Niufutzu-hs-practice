/* ══════════════════════════════════════════════════════════════
   g10a-ch01 數與式・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）
     a：答案（HTML）
     h：一行提示（做不出來時看）
     p：產生這題用的參數（給 Node／sympy 獨立驗算用，頁面不顯示）
   所有答案都由程式用「精確算術」算出（分數、根式、整數），不用浮點。
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
    r.pick = function (arr) { return arr[Math.floor(r() * arr.length)]; };
    r.sign = function () { return r() < 0.5 ? -1 : 1; };
    r.shuffle = function (arr) { var a = arr.slice(); for (var i = a.length - 1; i > 0; i--) { var j = Math.floor(r() * (i + 1)), t = a[i]; a[i] = a[j]; a[j] = t; } return a; };
    return r;
  }

  /* ────────── 整數工具 ────────── */
  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }
  function isSquare(n) { var s = Math.round(Math.sqrt(n)); return s * s === n; }
  function isqrt(n) { return Math.floor(Math.sqrt(n) + 1e-9); }
  /* n = c²·r，r 無平方因數（r=1 表示完全平方） */
  function simpSqrt(n) {
    var c = 1, r = n;
    for (var k = 2; k * k <= r; k++) { while (r % (k * k) === 0) { r /= k * k; c *= k; } }
    return { c: c, r: r };
  }
  function factorPairs(n) {          /* n = a·b，a≤b */
    var out = []; for (var a = 1; a * a <= n; a++) if (n % a === 0) out.push([a, n / a]); return out;
  }

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
    neg: function (x) { return F(-x.n, x.d); },
    eq: function (x, y) { return x.n * y.d === y.n * x.d; },
    lt: function (x, y) { return x.n * y.d < y.n * x.d; },
    toNum: function (x) { return x.n / x.d; },
    tex: function (x, big) {
      if (x.d === 1) return String(x.n);
      var f = big === false ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };

  /* ────────── 根式 a + b√r 的排版 ────────── */
  function sqrtTex(n) {           /* √n 化簡後的 LaTeX，n 正整數 */
    var s = simpSqrt(n);
    if (s.r === 1) return String(s.c);
    return (s.c === 1 ? '' : s.c) + '\\sqrt{' + s.r + '}';
  }
  function surdTex(a, b, r) {     /* a + b√r（a,b 整數，r 無平方因數）*/
    var out = '';
    if (a !== 0) out += String(a);
    if (b !== 0) {
      var bb = Math.abs(b) === 1 ? '' : String(Math.abs(b));
      out += (b < 0 ? '-' : (a !== 0 ? '+' : '')) + bb + '\\sqrt{' + r + '}';
    }
    return out || '0';
  }
  /* (a+b√r)/d，整理成最簡（約分共同因數） */
  function surdFracTex(a, b, r, d) {
    var g = gcd(gcd(a, b), d); a /= g; b /= g; d /= g;
    if (d < 0) { a = -a; b = -b; d = -d; }
    var num = surdTex(a, b, r);
    if (d === 1) return num;
    return '\\dfrac{' + num + '}{' + d + '}';
  }

  /* ────────── 循環小數 ────────── */
  /* 0.[pre](rep)̄ → 分數；pre、rep 都是數字字串 */
  function repeatingToFrac(intPart, pre, rep) {
    var whole = pre + rep, k = pre.length, m = rep.length;
    var num = parseInt(whole || '0', 10) - parseInt(pre || '0', 10);
    var den = (Math.pow(10, m) - 1) * Math.pow(10, k);
    return Fr.add(F(intPart), F(num, den));
  }
  function repTex(intPart, pre, rep) {
    return String(intPart) + '.' + pre + '\\overline{' + rep + '}';
  }
  /* 分數的小數展開（純小數部分），回傳 {pre, rep} */
  function fracToRepeating(n, d) {
    n = n % d; var seen = {}, digits = '', pos = 0;
    while (n !== 0 && !(n in seen)) { seen[n] = pos++; n *= 10; digits += Math.floor(n / d); n %= d; }
    if (n === 0) return { pre: digits, rep: '' };
    return { pre: digits.slice(0, seen[n]), rep: digits.slice(seen[n]) };
  }

  /* ────────── 小工具 ────────── */
  function T(s) { return '$' + s + '$'; }
  function coefTex(c, v) { return c === 1 ? v : (c === -1 ? '-' + v : c + v); }   /* 3x, -x, x */
  function linTex(a, b) {        /* ax+b */
    var s = coefTex(a, 'x');
    if (b > 0) s += '+' + b; else if (b < 0) s += '-' + (-b);
    return s;
  }
  function absLin(a, b) { return '\\left|' + linTex(a, b) + '\\right|'; }
  function signed(b) { return b >= 0 ? '+' + b : '-' + (-b); }
  function ivTex(lo, hi, lc, rc) {   /* 區間 */
    return (lc ? '[' : '(') + lo + ',\\ ' + hi + (rc ? ']' : ')');
  }
  function fx(v) { return typeof v === 'number' ? (Number.isInteger(v) ? String(v) : Fr.tex(F(Math.round(v * 1e6), 1e6))) : Fr.tex(v); }

  /* ══════════════════════════════════════════════════════════
     L1 基礎（每型都是「一個觀念一個動作」）
     ══════════════════════════════════════════════════════════ */
  var L1 = {};

  /* 1-1 有理數／無理數判別 */
  L1.rational = function (r) {
    var pool = [
      function () { var n = r.int(-20, 20); return { tex: String(n), rat: true, why: '整數都是有理數' }; },
      function () { var a = r.int(1, 9), b = r.pick([2, 4, 5, 8, 10, 20, 25]); return { tex: '\\dfrac{' + a + '}{' + b + '}', rat: true, why: '分母只有質因數 2、5，是有限小數' }; },
      function () { var a = r.int(1, 9), b = r.pick([3, 6, 7, 9, 11, 12, 13]); return { tex: '\\dfrac{' + a + '}{' + b + '}', rat: true, why: '分數一定是有理數（化成小數是循環小數）' }; },
      function () { var p = String(r.int(1, 9)), q = String(r.int(1, 99)); return { tex: '0.' + p + '\\overline{' + q + '}', rat: true, why: '循環小數可以化成分數' }; },
      function () { var n = r.pick([4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144]); return { tex: '\\sqrt{' + n + '}', rat: true, why: T('\\sqrt{' + n + '}=' + isqrt(n)) + '，是整數' }; },
      function () { var n = r.pick([2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 15, 18, 20]); return { tex: '\\sqrt{' + n + '}', rat: false, why: n + ' 不是完全平方數，開根號是無理數' }; },
      function () { var n = r.pick([8, 27, 64, 125]); return { tex: '\\sqrt[3]{' + n + '}', rat: true, why: T('\\sqrt[3]{' + n + '}=' + Math.round(Math.cbrt(n))) + '，是整數' }; },
      function () { var n = r.pick([2, 3, 4, 5, 9, 10]); return { tex: '\\sqrt[3]{' + n + '}', rat: false, why: n + ' 不是完全立方數' }; },
      function () { var a = r.int(1, 5); return { tex: a + '\\pi', rat: false, why: T('\\pi') + ' 是無理數，乘非零有理數仍是無理數' }; },
      function () { var a = r.pick([2, 3, 5, 6, 7, 8]); return { tex: '\\sqrt{' + a + '}\\times\\sqrt{' + a + '}', rat: true, why: '等於 ' + T(String(a)) + '，兩個無理數的乘積可以是有理數' }; },
      function () { var a = r.pick([2, 3, 5]); return { tex: '(\\sqrt{' + a + '}+1)(\\sqrt{' + a + '}-1)', rat: true, why: '等於 ' + T(String(a - 1)) + '，平方差把根號消掉了' }; },
      function () { var a = r.pick([2, 3, 5]); return { tex: '\\sqrt{' + a + '}+1', rat: false, why: '無理數加有理數還是無理數' }; },
      function () { var a = r.int(2, 9); return { tex: '0.' + a + a + a + '\\ldots\\text{（不循環、無規律）}', rat: false, why: '無限不循環小數就是無理數' }; }
    ];
    var it = r.pick(pool)();
    return { q: '判斷 ' + T(it.tex) + ' 是<b>有理數</b>還是<b>無理數</b>。', a: (it.rat ? '<b>有理數</b>' : '<b>無理數</b>') + '　（' + it.why + '）',
             h: '先問：' + T(it.tex) + ' 能不能寫成「整數 ÷ 整數」？整數、有限小數、循環小數、能開盡的根號都可以；開不盡的根號、$\\pi$ 就不行。', p: { tex: it.tex, rat: it.rat } };
  };

  /* 1-2 純循環小數化分數 */
  L1.repPure = function (r) {
    var m = r.int(1, 2), rep = m === 1 ? String(r.int(1, 9)) : String(r.int(10, 98)).replace(/9$/, '8');
    if (m === 2 && rep[0] === rep[1]) rep = rep[0] + String((parseInt(rep[1], 10) + 1) % 10);
    var fr = repeatingToFrac(0, '', rep), nines = '9'.repeat(rep.length);
    return { q: '將循環小數 ' + T(repTex(0, '', rep)) + ' 化為最簡分數。', a: T(Fr.tex(fr)),
             h: '循環節是「' + rep + '」、長度 ' + rep.length + ' ⟹ 分母寫 ' + rep.length + ' 個 9：$\\dfrac{' + parseInt(rep, 10) + '}{' + nines + '}$，再約分。', p: { pre: '', rep: rep, n: fr.n, d: fr.d } };
  };

  /* 1-3 混循環小數化分數 */
  L1.repMixed = function (r) {
    var pre = String(r.int(1, 9)), rep = String(r.int(1, 9));
    if (r() < 0.4) rep = String(r.int(10, 99));
    if (rep.length === 2 && rep[0] === rep[1]) rep = rep[0] + String((parseInt(rep[1], 10) + 3) % 10);
    var fr = repeatingToFrac(0, pre, rep), whole = pre + rep, nines = '9'.repeat(rep.length), zeros = '0'.repeat(pre.length);
    return { q: '將循環小數 ' + T(repTex(0, pre, rep)) + ' 化為最簡分數。', a: T(Fr.tex(fr)),
             h: '混循環：分子＝「' + whole + '」－「' + pre + '」＝ ' + (parseInt(whole, 10) - parseInt(pre, 10)) + '；分母＝ ' + nines + zeros + '（' + rep.length + ' 個 9 後接 ' + pre.length + ' 個 0），再約分。',
             p: { pre: pre, rep: rep, n: fr.n, d: fr.d } };
  };

  /* 1-4 分數化小數：有限還是循環？ */
  L1.fracKind = function (r) {
    var d = r.pick([4, 5, 8, 16, 20, 25, 40, 6, 7, 9, 11, 12, 14, 15, 18, 21, 22, 30]);
    var n = r.int(1, d - 1); if (gcd(n, d) !== 1) n = 1;
    var t = d; while (t % 2 === 0) t /= 2; while (t % 5 === 0) t /= 5;
    var fin = t === 1, ex = fracToRepeating(n, d);
    var tex = fin ? '0.' + ex.pre : repTex(0, ex.pre, ex.rep);
    var pf = [], x = d; for (var q = 2; q <= x; q++) { var e = 0; while (x % q === 0) { x /= q; e++; } if (e) pf.push(e > 1 ? q + '^' + e : String(q)); }
    return { q: T('\\dfrac{' + n + '}{' + d + '}') + ' 化成小數是<b>有限小數</b>還是<b>循環小數</b>？並寫出它。',
             a: (fin ? '有限小數' : '循環小數') + '：' + T(tex),
             h: '分母 $' + d + '=' + pf.join('\\times') + '$：質因數只有 2、5 ⟹ 有限小數；有別的質因數（' + (fin ? '這裡沒有' : '這裡有 ' + t) + '）⟹ 一定循環。', p: { n: n, d: d, fin: fin } };
  };

  /* 1-5 數線上的內分點 */
  L1.divPoint = function (r) {
    var a = r.int(-9, 5), b = a + r.int(2, 12), m = r.int(1, 5), n = r.int(1, 5), g = gcd(m, n); m /= g; n /= g;
    var p = Fr.add(F(a), Fr.mul(F(b - a), F(m, m + n)));   /* AP:PB = m:n ⟹ P = A + m/(m+n)(B-A) */
    return { q: '數線上 ' + T('A(' + a + ')') + '、' + T('B(' + b + ')') + '，點 ' + T('P') + ' 在線段 ' + T('\\overline{AB}') + ' 上且 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '，求 ' + T('P') + ' 的坐標。',
             a: T('P\\left(' + Fr.tex(p) + '\\right)'),
             h: '分點公式「交叉配」：$P=\\dfrac{n\\cdot a+m\\cdot b}{m+n}=\\dfrac{' + n + '\\times(' + a + ')+' + m + '\\times(' + b + ')}{' + m + '+' + n + '}$——靠近 $B$ 的比例 $' + m + '$ 反而配給 $B$。', p: { a: a, b: b, m: m, n: n, pn: p.n, pd: p.d } };
  };

  /* 2-1 根式化簡 √n = c√r */
  L1.simpRoot = function (r) {
    var c = r.int(2, 7), rr = r.pick([2, 3, 5, 6, 7, 10]), n = c * c * rr;
    return { q: '化簡 ' + T('\\sqrt{' + n + '}') + '。', a: T(sqrtTex(n)),
             h: '把 ' + n + ' 拆成「完全平方數 × 剩下的」，完全平方數開出來放外面。', p: { n: n, c: c, r: rr } };
  };

  /* 2-2 同類根式加減 */
  L1.addRoots = function (r) {
    var rr = r.pick([2, 3, 5, 6]), c1 = r.int(2, 5), c2 = r.int(1, 4), c3 = r.int(1, 3);
    var n1 = c1 * c1 * rr, n2 = c2 * c2 * rr, n3 = c3 * c3 * rr, s2 = r.sign(), s3 = r.sign();
    var total = c1 + s2 * c2 + s3 * c3;
    var q = '\\sqrt{' + n1 + '}' + (s2 > 0 ? '+' : '-') + '\\sqrt{' + n2 + '}' + (s3 > 0 ? '+' : '-') + '\\sqrt{' + n3 + '}';
    return { q: '計算 ' + T(q) + '。', a: T(surdTex(0, total, rr)),
             h: '先各自化簡：$\\sqrt{' + n1 + '}=' + sqrtTex(n1) + '$、$\\sqrt{' + n2 + '}=' + sqrtTex(n2) + '$、$\\sqrt{' + n3 + '}=' + sqrtTex(n3) + '$，都是 $\\sqrt{' + rr + '}$ 的倍數，再把係數加減。', p: { r: rr, cs: [c1, s2 * c2, s3 * c3], total: total } };
  };

  /* 2-3 分母有理化（單項） */
  L1.ratSingle = function (r) {
    var a = r.int(1, 12), rr = r.pick([2, 3, 5, 6, 7]);
    var g = gcd(a, rr), num = a / g, den = rr / g;   /* a/√r = a√r / r */
    return { q: '將 ' + T('\\dfrac{' + a + '}{\\sqrt{' + rr + '}}') + ' 的分母有理化。',
             a: T(den === 1 ? surdTex(0, num, rr) : '\\dfrac{' + surdTex(0, num, rr) + '}{' + den + '}'),
             h: '分子分母同乘 $\\sqrt{' + rr + '}$。', p: { a: a, r: rr } };
  };

  /* 2-4 分母有理化（共軛） */
  L1.ratConj = function (r) {
    var k = r.pick([2, 3, 5, 6, 7]), b = r.int(1, 4), sgn = r.sign(), a = r.int(1, 6);
    /* a/(b + s√k) = a(b − s√k)/(b² − k)，避免 b²=k */
    if (b * b === k) b += 1;
    var den = b * b - k;
    return { q: '將 ' + T('\\dfrac{' + a + '}{' + b + (sgn > 0 ? '+' : '-') + '\\sqrt{' + k + '}}') + ' 的分母有理化。',
             a: T(surdFracTex(a * b, -sgn * a, k, den)),
             h: '分子分母同乘共軛 $' + b + (sgn > 0 ? '-' : '+') + '\\sqrt{' + k + '}$，分母變成 $' + b + '^2-' + k + '$。',
             p: { a: a, b: b, s: sgn, k: k } };
  };

  /* 2-5 雙重根號（可直接拆） */
  L1.doubleRoot = function (r) {
    var p = r.int(1, 7), q = r.int(p + 1, 9); if (isSquare(p * q)) q += 1;
    var sgn = r.sign();                         /* √(p+q ± 2√pq) = √q ± √p */
    var inner = p + q, rad = p * q;
    return { q: '化簡 ' + T('\\sqrt{' + inner + (sgn > 0 ? '+' : '-') + '2\\sqrt{' + rad + '}}') + '。',
             a: T(sqrtTex(q) + (sgn > 0 ? '+' : '-') + sqrtTex(p)),
             h: '找兩個數：和是 ' + inner + '、積是 ' + rad + '。$\\sqrt{(\\sqrt q\\pm\\sqrt p)^2}$，大的放前面。', p: { p: p, q: q, s: sgn } };
  };

  /* 2-6 整數部分與小數部分 */
  L1.intFrac = function (r) {
    var n = r.int(2, 60); while (isSquare(n)) n = r.int(2, 60);
    var k = isqrt(n);
    return { q: '設 ' + T('\\sqrt{' + n + '}') + ' 的整數部分為 ' + T('a') + '、小數部分為 ' + T('b') + '，求 ' + T('a') + ' 與 ' + T('b') + '。',
             a: T('a=' + k + ',\\ b=\\sqrt{' + n + '}-' + k),
             h: '找夾住 ' + n + ' 的兩個完全平方數：$' + k * k + '<' + n + '<' + (k + 1) * (k + 1) + '$ ⟹ $' + k + '<\\sqrt{' + n + '}<' + (k + 1) + '$；小數部分 ＝ 原數 − 整數部分。', p: { n: n, k: k } };
  };

  /* 2-7 算幾不等式直接型 */
  L1.amgm = function (r) {
    var v = r.int(0, 2);
    if (v === 2) {   /* xy = P（P 完全平方）⟹ x+y ≥ 2√P */
      var P = r.pick([4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144]), s = isqrt(P);
      return { q: '設 ' + T('x,y>0') + ' 且 ' + T('xy=' + P) + '，求 ' + T('x+y') + ' 的最小值，並求此時的 ' + T('(x,y)') + '。',
               a: '最小值 ' + T(String(2 * s)) + '，此時 ' + T('(x,y)=(' + s + ',' + s + ')'),
               h: '$x+y\\ge2\\sqrt{xy}=2\\sqrt{' + P + '}$，等號在 $x=y=\\sqrt{' + P + '}$。', p: { v: 2, P: P, min: 2 * s } };
    }
    var PAIRS = [[1, 1], [1, 4], [1, 9], [1, 16], [1, 25], [1, 36], [1, 49], [1, 64], [1, 100], [2, 2], [2, 8], [2, 18], [2, 32], [2, 50], [3, 3], [3, 12], [3, 27], [3, 48], [4, 1], [4, 4], [4, 9], [4, 16], [4, 25]];
    var pr = r.pick(PAIRS), c = pr[0], k = pr[1], ck = c * k;
    var minv = 2 * isqrt(ck), xe = F(isqrt(ck), c);      /* cx = k/x ⟹ x = √(k/c) = √(ck)/c */
    var expr = v === 0 ? coefTex(c, 'x') + '+\\dfrac{' + k + '}{x}' : '\\dfrac{' + coefTex(c, 'x^2') + '+' + k + '}{x}';
    return { q: '設 ' + T('x>0') + '，求 ' + T(expr) + ' 的最小值，並求此時的 ' + T('x') + '。',
             a: '最小值 ' + T(String(minv)) + '，此時 ' + T('x=' + Fr.tex(xe)),
             h: (v === 1 ? '先拆開：$\\dfrac{' + coefTex(c, 'x^2') + '+' + k + '}{x}=' + coefTex(c, 'x') + '+\\dfrac{' + k + '}{x}$。' : '') + '兩正數相加 $\\ge2\\sqrt{\\text{乘積}}$：$' + coefTex(c, 'x') + '\\cdot\\dfrac{' + k + '}{x}=' + ck + '$ 是定值；等號在 $' + coefTex(c, 'x') + '=\\dfrac{' + k + '}{x}$。', p: { v: v, c: c, k: k, min: minv, xn: xe.n, xd: xe.d } };
  };

  /* 3-1 去絕對值（已知大小） */
  L1.absSimp = function (r) {
    var k = r.int(1, 6), v = r.int(0, 6), c = r.int(-5, 6);
    if (v === 0) return { q: '已知 ' + T('a<b') + '，化簡 ' + T('|a-b|+|b-a+' + k + '|') + '。', a: T('2b-2a+' + k), h: '$a<b$ ⟹ $a-b<0$，所以 $|a-b|=b-a$（變號脫）；$b-a+' + k + '>0$ 直接脫，再相加。', p: { v: 0, k: k } };
    if (v === 1) return { q: '已知 ' + T('a<b') + '，化簡 ' + T('|a-b-' + k + '|-|b-a|') + '。', a: T(String(k)), h: '$a-b-' + k + '<0$ ⟹ 第一項 $=b-a+' + k + '$；$b-a>0$ ⟹ 第二項 $=b-a$，相減。', p: { v: 1, k: k } };
    if (v === 2) return { q: '已知 ' + T('a<b') + '，化簡 ' + T('|a-b|-|a-b-' + k + '|') + '。', a: T(String(-k)), h: '兩個都負：$|a-b|=b-a$、$|a-b-' + k + '|=b-a+' + k + '$，相減後 $a,b$ 都消掉。', p: { v: 2, k: k } };
    if (v === 3) return { q: '已知 ' + T('x<' + c) + '，化簡 ' + T(absLin(1, -c) + '+' + absLin(1, -c - k)) + '。', a: T(linTex(-2, 2 * c + k)), h: '$x<' + c + '$ ⟹ $' + linTex(1, -c) + '<0$，$' + linTex(1, -c - k) + '$ 更小也 $<0$，兩個都要「變號脫」：$(' + linTex(-1, c) + ')+(' + linTex(-1, c + k) + ')$。', p: { v: 3, k: k, c: c } };
    if (v === 4) return { q: '已知 ' + T('x>' + c) + '，化簡 ' + T(absLin(1, -c) + '-|' + linTex(-1, c - k) + '|') + '。', a: T(String(-k)), h: '$x>' + c + '$ ⟹ $' + linTex(1, -c) + '>0$ 直接脫；$' + linTex(-1, c - k) + '=-(' + linTex(1, k - c) + ')<0$，脫掉變成 $' + linTex(1, k - c) + '$。', p: { v: 4, k: k, c: c } };
    if (v === 5) return { q: '已知 ' + T(c + '<x<' + (c + k)) + '，化簡 ' + T(absLin(1, -c) + '+' + absLin(1, -c - k)) + '。', a: T(String(k)), h: '$x$ 在 $' + c + '$ 與 $' + (c + k) + '$ 之間：$' + absLin(1, -c) + '=' + linTex(1, -c) + '$（正）、$' + absLin(1, -c - k) + '=' + linTex(-1, c + k) + '$（負要變號），相加 $x$ 消掉。', p: { v: 5, k: k, c: c } };
    return { q: '已知 ' + T('a<b') + '，化簡 ' + T('\\sqrt{(a-b)^2}+|b-a|') + '。', a: T('2b-2a'), h: '$\\sqrt{(a-b)^2}=|a-b|$，不是 $a-b$！$a<b$ ⟹ $|a-b|=b-a$，兩項都是 $b-a$。', p: { v: 6, k: k } };
  };

  /* 3-2 絕對值方程式 |x-a|=b */
  L1.absEq = function (r) {
    var a = r.int(-6, 6), b = r.int(1, 7);
    return { q: '解方程式 ' + T('|x' + signed(-a).replace('+0', '') + '|=' + b) + '。'.replace('|x+0|', '|x|'),
             a: T('x=' + (a + b) + '\\ \\text{或}\\ x=' + (a - b)),
             h: '「與 $' + a + '$ 的距離是 $' + b + '$」⟹ 往左往右各走 $' + b + '$。', p: { a: a, b: b } };
  };

  /* 3-3 絕對值不等式 |x-a|<b 或 >b */
  L1.absIneq = function (r) {
    var a = r.int(-5, 5), b = r.int(1, 6), less = r() < 0.5;
    var s = '|x' + (a === 0 ? '' : signed(-a)) + '|' + (less ? '<' : '>') + b;
    return { q: '解不等式 ' + T(s) + '。',
             a: T(less ? (a - b) + '<x<' + (a + b) : 'x<' + (a - b) + '\\ \\text{或}\\ x>' + (a + b)),
             h: '讀成「$x$ 與 $' + a + '$ 的距離' + (less ? '小於' : '大於') + ' $' + b + '$」：從 $' + a + '$ 往左右各走 $' + b + '$ 到 $' + (a - b) + '$ 與 $' + (a + b) + '$，' + (less ? '取夾在中間的一段。' : '取兩邊外面。'), p: { a: a, b: b, less: less } };
  };

  /* 3-4 兩定點距離和的最小值 */
  L1.absSum2 = function (r) {
    var a = r.int(-6, 3), b = a + r.int(1, 9);
    var tex = '|x' + (a === 0 ? '' : signed(-a)) + '|+|x' + (b === 0 ? '' : signed(-b)) + '|';
    return { q: '求 ' + T(tex) + ' 的最小值。',
             a: '最小值 ' + T(String(b - a)) + '（當 ' + T(a + '\\le x\\le ' + b) + ' 時）',
             h: '$' + tex + '$ 是「$x$ 到 $' + a + '$ 與到 $' + b + '$ 的距離和」；畫數線，$x$ 落在 $' + a + '$ 與 $' + b + '$ 之間時距離和最小，就是兩點的距離。', p: { a: a, b: b, min: b - a } };
  };

  /* 4-1 指數律化簡 */
  function powT(b, e) { return e === 0 ? '1' : e === 1 ? b : b + '^{' + e + '}'; }   /* b^0 寫 1、b^1 寫 b */
  function powTail(b, e) { return e === 0 ? '=1' : e === 1 ? '=' + b : ''; }
  L1.expLaw = function (r) {
    var base = r.pick(['a', 'x', '2', '3']), v = r.int(0, 2);
    var m = r.int(2, 6), n = r.int(2, 6), k = r.int(2, 3);
    var zero = '（任何非零數的 $0$ 次方都是 $1$）';
    if (v === 0) return { q: '化簡 ' + T(base + '^{' + m + '}\\cdot ' + base + '^{' + n + '}\\div ' + base + '^{' + k + '}') + '。', a: T(powT(base, m + n - k)), h: '同底相乘指數相加：$' + m + '+' + n + '$；再除以 $' + base + '^{' + k + '}$ 指數減 $' + k + '$。', p: { v: 0, base: base, m: m, n: n, k: k } };
    if (v === 1) return { q: '化簡 ' + T('\\left(' + base + '^{' + m + '}\\right)^{' + k + '}\\div ' + base + '^{' + n + '}') + '。', a: T(powT(base, m * k - n)), h: '次方的次方指數相乘：$' + m + '\\times' + k + '$；再除以 $' + base + '^{' + n + '}$ 指數減 $' + n + '$' + (m * k - n === 0 ? zero : '') + '。', p: { v: 1, base: base, m: m, n: n, k: k } };
    var p = r.int(1, 5), q = r.pick([2, 3, 4]); while (gcd(p, q) !== 1) p = r.int(1, 5);   /* 約分後根指數不能變 1 */
    return { q: '把 ' + T('\\sqrt[' + q + ']{' + powT(base, p) + '}') + ' 改寫成分數指數。', a: T(base + '^{' + (q === 1 ? String(p) : '\\frac{' + p + '}{' + q + '}') + '}'), h: '$\\sqrt[q]{a^p}=a^{p/q}$：根指數 $' + q + '$ 放分母、次方 $' + p + '$ 放分子' + (p === 1 ? '（$' + base + '$ 就是 $' + base + '$ 的 $1$ 次方）' : '') + '。', p: { v: 2, base: base, p: p, q: q } };
  };

  /* 4-2 同底指數比較大小 */
  L1.expCompare = function (r) {
    var base = r.pick([2, 3, 5, 10]), es = r.shuffle([r.int(-3, -1), r.int(0, 2), r.int(3, 6)]);
    var lbl = ['a', 'b', 'c'], items = lbl.map(function (L, i) { return L + '=' + base + '^{' + es[i] + '}'; });
    var order = [0, 1, 2].sort(function (i, j) { return es[j] - es[i]; }).map(function (i) { return lbl[i]; });
    return { q: '設 ' + T(items.join(',\\ ')) + '，由大到小排列。', a: T(order.join('>')), h: '底數 $' + base + '>1$ ⟹ 指數越大值越大：只要比 $a,b,c$ 的指數 $' + es.join(',\\ ') + '$（負指數是分數，最小）。', p: { base: base, es: es, order: order } };
  };

  /* 4-3 科學記號 */
  L1.sciNot = function (r) {
    var big = r() < 0.5, m = r.int(101, 999), e = big ? r.int(3, 9) : r.int(-8, -2);
    var val = big ? String(m) + '0'.repeat(e - 2) : '0.' + '0'.repeat(-e - 1) + String(m);
    return { q: '將 ' + T(val) + ' 寫成科學記號 ' + T('a\\times10^{n}') + '（' + T('1\\le a<10') + '）。',
             a: T((m / 100) + '\\times10^{' + e + '}'),
             h: (big ? '小數點原本在最後面，要移到第一個數字 ' + String(m)[0] + ' 後面：往左移 ' + e + ' 位 ⟹ $n=' + e + '$。' : '小數點要往右移 ' + (-e) + ' 位才到第一個非零數字 ' + String(m)[0] + ' 後面 ⟹ $n=' + e + '$（往右移是負的）。'), p: { m: m, e: e } };
  };

  /* 4-4 常用對數基本值 */
  L1.logBasic = function (r) {
    var v = r.int(0, 2);
    if (v === 0) { var k = r.int(-3, 6); return { q: '求 ' + T('\\log10^{' + k + '}') + '。', a: T(String(k)), h: '$\\log10^{n}$ 問的是「$10$ 的幾次方」，這裡 $10$ 的次方就寫在上面：' + k + '。', p: { v: 0, k: k } }; }
    if (v === 1) { var n = r.pick([100, 1000, 10000, 0.1, 0.01, 0.001]); var ans = Math.round(Math.log10(n)); return { q: '求 ' + T('\\log ' + n) + '。', a: T(String(ans)), h: '先把 $' + n + '$ 寫成 $10$ 的幾次方：$' + n + '=10^{' + ans + '}$。', p: { v: 1, n: n, ans: ans } }; }
    var a = r.pick([2, 3, 5, 7]), e = r.int(1, 4), la = { 2: 0.3010, 3: 0.4771, 5: 0.6990, 7: 0.8451 }[a];
    return { q: '已知 ' + T('\\log' + a + '\\approx' + la.toFixed(4)) + '，求 ' + T('\\log(' + a + '\\times10^{' + e + '})') + '。', a: T((e + la).toFixed(4)), h: '$\\log(ab)=\\log a+\\log b$：$\\log' + a + '+\\log10^{' + e + '}=' + la.toFixed(4) + '+' + e + '$。', p: { v: 2, a: a, e: e, ans: e + la } };
  };

  /* 4-5 位數 */
  L1.digits = function (r) {
    var base = r.pick([2, 3, 5, 7]), n, lg = { 2: 0.3010, 3: 0.4771, 5: 0.6990, 7: 0.8451 }[base], v, d, m, tries = 0;
    do { n = r.int(10, 60); v = Math.round(n * lg * 10000) / 10000; m = v - Math.floor(v); } while ((m < 0.005 || m > 0.995) && tries++ < 60);
    d = Math.floor(v) + 1;
    return { q: '已知 ' + T('\\log' + base + '\\approx' + lg.toFixed(4)) + '，問 ' + T(base + '^{' + n + '}') + ' 是幾位數？',
             a: T(String(d)) + ' 位數（' + T('\\log' + base + '^{' + n + '}=' + n + '\\times' + lg.toFixed(4) + '=' + v.toFixed(2)) + '）',
             h: '$\\log' + base + '^{' + n + '}=' + n + '\\times' + lg.toFixed(4) + '$，先算出這個值；位數 ＝ 它的整數部分 $+1$。', p: { base: base, n: n, lg: lg, d: d } };
  };

  /* ══════════════════════════════════════════════════════════
     L2 中等（段考主流題型；每型仍可無限出題）
     ══════════════════════════════════════════════════════════ */
  var L2 = {};

  /* 2-1 循環小數的四則 */
  L2.repArith = function (r) {
    var rep1 = String(r.int(1, 8)), pre2 = String(r.int(1, 9)), rep2 = String(r.int(1, 8));
    var x = repeatingToFrac(0, '', rep1), y = repeatingToFrac(0, pre2, rep2);
    var op = r.pick(['+', '-']), res = op === '+' ? Fr.add(x, y) : Fr.sub(x, y);
    return { q: '計算 ' + T(repTex(0, '', rep1) + op + repTex(0, pre2, rep2)) + '，以最簡分數表示。', a: T(Fr.tex(res)),
             h: '先各自化成分數：$' + repTex(0, '', rep1) + '=\\dfrac{' + rep1 + '}{9}$、$' + repTex(0, pre2, rep2) + '=\\dfrac{' + pre2 + rep2 + '-' + pre2 + '}{90}$，再通分運算。', p: { rep1: rep1, pre2: pre2, rep2: rep2, op: op, n: res.n, d: res.d } };
  };

  /* 2-2 小數點後第 n 位 */
  L2.nthDigit = function (r) {
    var d = r.pick([7, 13, 21, 27, 37, 41, 11, 33, 99]), n = r.int(1, d - 1); if (gcd(n, d) !== 1) n = 1;
    var ex = fracToRepeating(n, d), N = r.pick([100, 2024, 2025, 500, 1001, 2026]);
    var k = ex.pre.length, m = ex.rep.length, digit;
    if (N <= k) digit = ex.pre[N - 1]; else digit = ex.rep[(N - k - 1) % m];
    return { q: T('\\dfrac{' + n + '}{' + d + '}') + ' 化成小數後，小數點後第 ' + T(String(N)) + ' 位的數字是多少？',
             a: T(String(digit)) + '　（' + T(repTex(0, ex.pre, ex.rep)) + '，循環節長 ' + m + '，' + (N - k) + ' 除以 ' + m + ' 餘 ' + ((N - k) % m) + '）',
             h: '先把 $\\dfrac{' + n + '}{' + d + '}$ 除出循環節（分母 ' + d + ' 的循環節長 ' + m + '），再算 $' + N + '\\div' + m + '$ 的餘數對回循環節；餘 0 就是最後一位。', p: { n: n, d: d, N: N, digit: parseInt(digit, 10) } };
  };

  /* 2-3 有理化＋係數比較：1/(b+√k) + (c+d√k) = p+q√k */
  L2.coefCompare = function (r) {
    var k = r.pick([2, 3, 5, 7]), b = r.int(1, 4); if (b * b === k) b++;
    var s = r.sign(), den = b * b - k;              /* 1/(b+s√k) = (b - s√k)/den */
    var c = r.int(-4, 4), d = r.int(-3, 3);
    var p = Fr.add(F(b, den), F(c)), q = Fr.add(F(-s, den), F(d));
    return { q: '設 ' + T('a,b') + ' 為有理數，且 ' + T('\\dfrac{1}{' + b + (s > 0 ? '+' : '-') + '\\sqrt{' + k + '}}' + (c !== 0 || d !== 0 ? '+' + (c === 0 ? '' : '(' + c + ')') + (d === 0 ? '' : (c === 0 ? '' : '+') + '(' + surdTex(0, d, k) + ')') : '') + '=a+b\\sqrt{' + k + '}') + '，求 ' + T('(a,b)') + '。',
             a: T('(a,b)=\\left(' + Fr.tex(p, false) + ',\\ ' + Fr.tex(q, false) + '\\right)'),
             h: '先有理化，整理成「有理部分 + 無理部分」，再兩邊比較（前提：$a,b$ 有理且 $\\sqrt{' + k + '}$ 無理）。', p: { k: k, b: b, s: s, c: c, d: d, pn: p.n, pd: p.d, qn: q.n, qd: q.d } };
  };

  /* 2-4 整數／小數部分再運算：1/b - 1/a 之類 */
  L2.intFracOp = function (r) {
    var n = r.int(2, 50); while (isSquare(n)) n = r.int(2, 50);
    var k = isqrt(n), den = n - k * k, v = r.int(0, 2), sq = simpSqrt(n);   /* √n = sq.c√sq.r，答案要化到最簡 */
    var head = '設 ' + T('\\sqrt{' + n + '}') + ' 的整數部分為 ' + T('a') + '、小數部分為 ' + T('b') + '，求 ';
    if (v === 0) {   /* 1/b − 1/a = (√n+k)/den − 1/k = (k√n + k² − den)/(k·den) */
      var num0 = k * k - den, nums = k, D = k * den;
      return { q: head + T('\\dfrac1b-\\dfrac1a') + '。', a: T(surdFracTex(num0, nums * sq.c, sq.r, D)), h: '$a=' + k + '$、$b=\\sqrt{' + n + '}-' + k + '$，$\\dfrac1b=\\dfrac{1}{\\sqrt{' + n + '}-' + k + '}$ 要乘共軛有理化，分母變成 $' + n + '-' + k * k + '=' + den + '$。', p: { n: n, k: k, v: 0 } };
    }
    if (v === 1) return { q: head + T('ab+b^2') + '。', a: T(surdTex(n, -k * sq.c, sq.r)), h: '$ab+b^2=b(a+b)$，而 $a+b$ 就是原數 $\\sqrt{' + n + '}$：$(\\sqrt{' + n + '}-' + k + ')\\sqrt{' + n + '}$。', p: { n: n, k: k, v: 1 } };
    /* b² + 2ab = b(b+2a) = (√n−k)(√n+k) = n − k² */
    return { q: head + T('b^2+2ab') + '。', a: T(String(den)), h: '$b^2+2ab=b(b+2a)=(\\sqrt{' + n + '}-' + k + ')(\\sqrt{' + n + '}+' + k + ')$，平方差，根號會消掉。', p: { n: n, k: k, v: 2 } };
  };

  /* 2-5 雙重根號（要先提 2） */
  L2.doubleRoot2 = function (r) {
    var p = r.int(1, 6), q = r.int(p + 1, 9); if (isSquare(p * q)) q++;
    var sgn = r.sign(), inner = p + q, rad = 4 * p * q;   /* √(p+q ± √(4pq)) */
    return { q: '化簡 ' + T('\\sqrt{' + inner + (sgn > 0 ? '+' : '-') + '\\sqrt{' + rad + '}}') + '。',
             a: T(sqrtTex(q) + (sgn > 0 ? '+' : '-') + sqrtTex(p)),
             h: '先把 $\\sqrt{' + rad + '}$ 寫成 $2\\sqrt{' + (p * q) + '}$，再找和 ' + inner + '、積 ' + (p * q) + '。', p: { p: p, q: q, s: sgn } };
  };

  /* 2-6 x+1/x 對稱式 */
  L2.symm = function (r) {
    var pairs = [[2, 1], [3, 1], [5, 1], [6, 1], [7, 1], [3, 2], [5, 2], [6, 2], [7, 2], [5, 3], [7, 3], [10, 3], [7, 5], [6, 5], [11, 2], [10, 7]];
    var fam = r.int(0, 2), A = 0, B = 0, aa = 0, s, xTex, hint;
    if (fam < 2) {   /* x = (√A∓√B)/(√A±√B)，1/x 就是分子分母對調，x+1/x = 2(A+B)/(A−B) */
      var pr = r.pick(pairs); A = pr[0]; B = pr[1]; s = F(2 * (A + B), A - B);
      xTex = fam === 0 ? '\\dfrac{' + sqrtTex(A) + '-' + sqrtTex(B) + '}{' + sqrtTex(A) + '+' + sqrtTex(B) + '}' : '\\dfrac{' + sqrtTex(A) + '+' + sqrtTex(B) + '}{' + sqrtTex(A) + '-' + sqrtTex(B) + '}';
      hint = '$\\dfrac1x$ 恰是分子分母對調，$x+\\dfrac1x=\\dfrac{(' + sqrtTex(A) + '-' + sqrtTex(B) + ')^2+(' + sqrtTex(A) + '+' + sqrtTex(B) + ')^2}{' + A + '-' + B + '}=' + Fr.tex(s, false) + '$';
    } else {         /* x = a − √(a²−1)，1/x = a + √(a²−1)，x+1/x = 2a */
      aa = r.int(2, 8); s = F(2 * aa); xTex = aa + '-' + sqrtTex(aa * aa - 1);
      hint = '$\\dfrac1x=\\dfrac{1}{' + xTex + '}$ 有理化後是 $' + aa + '+' + sqrtTex(aa * aa - 1) + '$（共軛），所以 $x+\\dfrac1x=' + 2 * aa + '$';
    }
    var s2 = Fr.sub(Fr.mul(s, s), F(2)), s3 = Fr.sub(Fr.mul(Fr.mul(s, s), s), Fr.mul(F(3), s)), s4 = Fr.sub(Fr.mul(s2, s2), F(2));
    var which = r.int(0, 2), ask = ['x^2+\\dfrac1{x^2}', 'x^3+\\dfrac1{x^3}', 'x^4+\\dfrac1{x^4}'][which], ans = [s2, s3, s4][which];
    var rule = ['$x^2+\\frac1{x^2}=(x+\\frac1x)^2-2$', '$x^3+\\frac1{x^3}=(x+\\frac1x)^3-3(x+\\frac1x)$', '$x^4+\\frac1{x^4}=(x^2+\\frac1{x^2})^2-2$，先算 $x^2+\\frac1{x^2}$'][which];
    return { q: '設 ' + T('x=' + xTex) + '，求 ' + T(ask) + '。',
             a: T(Fr.tex(ans)) + '　（' + T('x+\\dfrac1x=' + Fr.tex(s, false)) + '）',
             h: hint + '；再用 ' + rule + '。',
             p: { fam: fam, A: A, B: B, aa: aa, which: which, sn: s.n, sd: s.d, an: ans.n, ad: ans.d } };
  };

  /* 2-7 算幾：條件式 × 目標式 */
  L2.amgmCond = function (r) {
    var v = r.int(0, 4);
    if (v === 0) {   /* a/x + b/y = 1 ⟹ xy ≥ 4ab，x=2a, y=2b */
      var a = r.int(1, 6), b = r.int(1, 6);
      return { q: '設 ' + T('x,y>0') + ' 且 ' + T('\\dfrac{' + a + '}{x}+\\dfrac{' + b + '}{y}=1') + '，求 ' + T('xy') + ' 的最小值及此時的 ' + T('(x,y)') + '。',
               a: '最小值 ' + T(String(4 * a * b)) + '，' + T('(x,y)=(' + 2 * a + ',' + 2 * b + ')'),
               h: '$1=\\dfrac{' + a + '}x+\\dfrac{' + b + '}y\\ge2\\sqrt{\\dfrac{' + a * b + '}{xy}}$，平方後 $xy\\ge' + 4 * a * b + '$；等號在 $\\dfrac{' + a + '}x=\\dfrac{' + b + '}y=\\dfrac12$。', p: { v: 0, a: a, b: b, min: 4 * a * b } };
    }
    if (v === 1) {   /* x + y = S ⟹ xy 最大 (S/2)² */
      var S = 2 * r.int(2, 12);
      return { q: '設 ' + T('x,y>0') + ' 且 ' + T('x+y=' + S) + '，求 ' + T('xy') + ' 的最大值。', a: '最大值 ' + T(String(S * S / 4)) + '（' + T('x=y=' + S / 2) + '）',
               h: '$\\sqrt{xy}\\le\\dfrac{x+y}{2}=\\dfrac{' + S + '}{2}$，兩邊平方；等號在 $x=y$。', p: { v: 1, S: S, max: S * S / 4 } };
    }
    if (v === 2) {   /* x + y = S ⟹ 1/x + 1/y 最小 4/S */
      var S2 = 2 * r.int(2, 12), m2 = F(4, S2);
      return { q: '設 ' + T('x,y>0') + ' 且 ' + T('x+y=' + S2) + '，求 ' + T('\\dfrac1x+\\dfrac1y') + ' 的最小值。', a: '最小值 ' + T(Fr.tex(m2)) + '（' + T('x=y=' + S2 / 2) + '）',
               h: '$\\dfrac1x+\\dfrac1y=\\dfrac{x+y}{xy}=\\dfrac{' + S2 + '}{xy}$，$xy$ 最大（$=' + S2 * S2 / 4 + '$）時它最小。', p: { v: 2, S: S2, minn: m2.n, mind: m2.d } };
    }
    if (v === 3) {   /* x + c·y = S ⟹ xy 最大 S²/(4c)，x=S/2, y=S/(2c) */
      var c = r.pick([2, 3, 4]), S3 = 2 * c * r.int(1, 6), mx = F(S3 * S3, 4 * c);
      return { q: '設 ' + T('x,y>0') + ' 且 ' + T('x+' + c + 'y=' + S3) + '，求 ' + T('xy') + ' 的最大值及此時的 ' + T('(x,y)') + '。', a: '最大值 ' + T(Fr.tex(mx)) + '，' + T('(x,y)=\\left(' + S3 / 2 + ',' + Fr.tex(F(S3, 2 * c), false) + '\\right)'),
               h: '把 $x$ 與 $' + c + 'y$ 當成兩個正數：$x\\cdot ' + c + 'y\\le\\left(\\dfrac{x+' + c + 'y}{2}\\right)^2=' + S3 * S3 / 4 + '$，再除以 $' + c + '$；等號在 $x=' + c + 'y$。', p: { v: 3, c: c, S: S3, maxn: mx.n, maxd: mx.d } };
    }
    /* a/x + b/y = 1（a,b 完全平方）⟹ x + y ≥ (√a+√b)² */
    var A = r.pick([1, 4, 9, 16]), Bq = r.pick([1, 4, 9, 16]), sa = isqrt(A), sb = isqrt(Bq), mn = (sa + sb) * (sa + sb);
    return { q: '設 ' + T('x,y>0') + ' 且 ' + T('\\dfrac{' + A + '}{x}+\\dfrac{' + Bq + '}{y}=1') + '，求 ' + T('x+y') + ' 的最小值及此時的 ' + T('(x,y)') + '。',
             a: '最小值 ' + T(String(mn)) + '，' + T('(x,y)=(' + (A + sa * sb) + ',' + (Bq + sa * sb) + ')'),
             h: '乘上「$1$」：$x+y=(x+y)\\left(\\dfrac{' + A + '}x+\\dfrac{' + Bq + '}y\\right)=' + (A + Bq) + '+\\dfrac{' + coefTex(A, 'y') + '}{x}+\\dfrac{' + coefTex(Bq, 'x') + '}{y}\\ge' + (A + Bq) + '+2\\sqrt{' + A * Bq + '}$。', p: { v: 4, a: A, b: Bq, min: mn } };
  };

  /* 2-8 絕對值不等式三型 */
  L2.absIneq2 = function (r) {
    var v = r.int(0, 2);
    if (v === 0) {   /* c ≤ |ax+b| ≤ d */
      var a = r.pick([2, 3]), b = r.int(-5, 5), c = r.int(1, 4), d = c + r.int(2, 8);
      /* |ax+b| ≤ d ⟹ (−d−b)/a ≤ x ≤ (d−b)/a；≥ c ⟹ x ≤ (−c−b)/a 或 x ≥ (c−b)/a */
      var L1_ = F(-d - b, a), L2_ = F(-c - b, a), R1 = F(c - b, a), R2 = F(d - b, a);
      return { q: '解不等式 ' + T(c + '\\le' + absLin(a, b) + '\\le' + d) + '。',
               a: T(Fr.tex(L1_, false) + '\\le x\\le' + Fr.tex(L2_, false) + '\\ \\text{或}\\ ' + Fr.tex(R1, false) + '\\le x\\le' + Fr.tex(R2, false)),
               h: '拆成「$\\le d$」（夾中間）與「$\\ge c$」（兩外側）各解一次，再取交集。', p: { v: 0, a: a, b: b, c: c, d: d } };
    }
    if (v === 1) {   /* ||x−a|−b| ≤ c，取 c≥b 使左邊界自動成立 ⟹ |x−a| ≤ b+c */
      var a1 = r.int(-3, 4), b1 = r.int(1, 3), c1 = b1 + r.int(0, 3);
      return { q: '滿足 ' + T('\\big||x' + (a1 === 0 ? '' : signed(-a1)) + '|-' + b1 + '\\big|\\le' + c1) + ' 的實數 ' + T('x') + ' 所形成的區間，其長度為何？',
               a: T(String(2 * (b1 + c1))) + '　（' + T((a1 - b1 - c1) + '\\le x\\le' + (a1 + b1 + c1)) + '）',
               h: '由外往內脫：$-' + c1 + '\\le|x-a|-' + b1 + '\\le' + c1 + '$ ⟹ $|x-a|\\le' + (b1 + c1) + '$（左邊界 $\\ge' + (b1 - c1) + '$ 自動成立）。', p: { v: 1, a: a1, b: b1, c: c1, len: 2 * (b1 + c1) } };
    }
    /* |ax+b| ≤ |cx+d| ⟹ (ax+b)² ≤ (cx+d)² ⟹ ((a−c)x+(b−d))((a+c)x+(b+d)) ≤ 0 */
    var a2 = r.pick([2, 3, 4]), c2 = r.pick([1, 2]); if (a2 === c2) a2++;
    var b2 = r.int(-4, 4), d2 = r.int(-4, 4);
    if (b2 * c2 === a2 * d2) d2 += 1;                /* 兩根重合會退化成一個點，錯開 */
    var r1 = F(-(b2 - d2), a2 - c2), r2 = F(-(b2 + d2), a2 + c2);
    var lo = Fr.lt(r1, r2) ? r1 : r2, hi = Fr.lt(r1, r2) ? r2 : r1;
    return { q: '解不等式 ' + T(absLin(a2, b2) + '\\le' + absLin(c2, d2)) + '。',
             a: T(Fr.tex(lo, false) + '\\le x\\le' + Fr.tex(hi, false)),
             h: '兩邊都非負 ⟹ 直接平方；平方差分解成兩個一次式相乘 $\\le0$。', p: { v: 2, a: a2, b: b2, c: c2, d: d2, lon: lo.n, lod: lo.d, hin: hi.n, hid: hi.d } };
  };

  /* 2-9 分段：|x−a|+|x−b| ≤ k */
  L2.absSumIneq = function (r) {
    var a = r.int(-5, 2), b = a + r.int(1, 6), k = (b - a) + 2 * r.int(1, 5);   /* k > b−a，解 [ (a+b−k)/2, (a+b+k)/2 ] */
    var lo = F(a + b - k, 2), hi = F(a + b + k, 2);
    return { q: '解不等式 ' + T('|x' + (a === 0 ? '' : signed(-a)) + '|+|x' + (b === 0 ? '' : signed(-b)) + '|\\le' + k) + '。',
             a: T(Fr.tex(lo, false) + '\\le x\\le' + Fr.tex(hi, false)),
             h: '到 $' + a + '$、$' + b + '$ 的距離和 $\\le' + k + '$，而兩點距離只有 $' + (b - a) + '$：多出來的 $' + (k - b + a) + '$ 平分給兩邊，從兩點往外各走 $' + Fr.tex(F(k - b + a, 2), false) + '$。或分 $x<' + a + '$、$' + a + '\\le x\\le' + b + '$、$x>' + b + '$ 三段討論。', p: { a: a, b: b, k: k, lon: lo.n, lod: lo.d, hin: hi.n, hid: hi.d } };
  };

  /* 2-10 加權距離和最小值 */
  L2.absMedian = function (r) {
    var pts = r.shuffle([r.int(-6, -2), r.int(-1, 2), r.int(3, 7)]), w = [r.int(1, 3), r.int(1, 3), r.int(1, 3)];
    var tex = pts.map(function (p, i) { return (w[i] === 1 ? '' : w[i]) + '|x' + (p === 0 ? '' : signed(-p)) + '|'; }).join('+');
    /* 最小值：在加權中位數處；直接掃描 */
    var order = pts.map(function (p, i) { return [p, w[i]]; }).sort(function (u, v) { return u[0] - v[0]; });
    var tot = w[0] + w[1] + w[2], acc = 0, med = order[0][0];
    for (var i = 0; i < 3; i++) { acc += order[i][1]; if (2 * acc >= tot) { med = order[i][0]; break; } }
    var val = 0; for (var j = 0; j < 3; j++) val += w[j] * Math.abs(med - pts[j]);
    return { q: '求 ' + T(tex) + ' 的最小值。', a: '最小值 ' + T(String(val)) + '（在 ' + T('x=' + med) + ' 附近取到）',
             h: '把 $k|x-p|$ 看成「$p$ 這個點放了 $k$ 個人」：' + order.map(function (o) { return '$' + o[0] + '$ 放 ' + o[1] + ' 人'; }).join('、') + '，共 ' + tot + ' 人；從左邊累積，人數過半（$\\ge' + Fr.tex(F(tot, 2), false) + '$）的那個點就是最小值的位置。', p: { pts: pts, w: w, min: val, med: med } };
  };

  /* 2-11 反推參數：|ax+b|≤c 的解為 [p,q] */
  L2.absParam = function (r) {
    var p = r.int(-6, 2), q = p + r.int(2, 10), a = r.pick([2, 3, 4, -2, -3]);
    /* 中心 −b/a = (p+q)/2，半寬 c/|a| = (q−p)/2 */
    var b = F(-a * (p + q), 2), c = F(Math.abs(a) * (q - p), 2);
    return { q: '設 ' + T('b,c') + ' 為實數，若 ' + T('|' + coefTex(a, 'x') + '+b|\\le c') + ' 的解為 ' + T(p + '\\le x\\le' + q) + '，求 ' + T('(b,c)') + '。',
             a: T('(b,c)=\\left(' + Fr.tex(b, false) + ',\\ ' + Fr.tex(c, false) + '\\right)'),
             h: '解集的中心 $=-\\dfrac ba$、半寬 $=\\dfrac{c}{|a|}$；把 $' + p + ',' + q + '$ 的中點與半距離對上去。', p: { a: a, p: p, q: q, bn: b.n, bd: b.d, cn: c.n, cd: c.d } };
  };

  /* 2-12 整數解個數 */
  L2.absIntCount = function (r) {
    var a = r.pick([2, 3]), b = r.int(-7, 7), c = r.int(4, 13);   /* |ax+b|<c ⟹ (−c−b)/a < x < (c−b)/a */
    var lo = (-c - b) / a, hi = (c - b) / a, cnt = 0;
    for (var k = Math.ceil(lo - 1e-9); k <= Math.floor(hi + 1e-9); k++) if (k > lo && k < hi) cnt++;
    return { q: '滿足 ' + T(absLin(a, b) + '<' + c) + ' 的整數 ' + T('x') + ' 有幾個？', a: T(String(cnt)) + ' 個',
             h: '先解出開區間 $\\left(' + Fr.tex(F(-c - b, a), false) + ',\\ ' + Fr.tex(F(c - b, a), false) + '\\right)$，再數裡面的整數（端點不算）。', p: { a: a, b: b, c: c, cnt: cnt } };
  };

  /* 2-13 指數方程式（換元） */
  L2.expEq = function (r) {
    var base = r.pick([2, 3, 5, 10]), e1 = r.int(0, 4), e2 = r.int(0, 4); if (e1 === e2) e2 = (e1 + 1) % 5;
    var t1 = Math.pow(base, e1), t2 = Math.pow(base, e2), S = t1 + t2, P = t1 * t2, form = r.int(0, 1);
    var lead = form === 0 ? base * base + '^{x}' : base + '^{2x}';
    return { q: '解方程式 ' + T(lead + '-' + S + '\\cdot' + base + '^{x}+' + P + '=0') + '。',
             a: T('x=' + Math.min(e1, e2) + '\\ \\text{或}\\ x=' + Math.max(e1, e2)),
             h: '令 $t=' + base + '^x>0$，則 $' + lead + '=t^2$：$t^2-' + S + 't+' + P + '=0$，分解後把 $t$ 換回 $' + base + '$ 的次方。', p: { base: base, e1: e1, e2: e2, form: form } };
  };

  /* 2-14 a^x ± a^{-x} 升冪 */
  L2.expSymm = function (r) {
    var v = r.int(0, 3), s = v === 1 ? r.int(1, 9) : r.int(3, 12);
    if (v === 0) return { q: '已知 ' + T('a^x+a^{-x}=' + s) + '，求 ' + T('a^{2x}+a^{-2x}') + ' 與 ' + T('a^{3x}+a^{-3x}') + '。', a: T(String(s * s - 2)) + '、' + T(String(s * s * s - 3 * s)), h: '平方：$(a^x+a^{-x})^2=a^{2x}+2+a^{-2x}=' + s * s + '$；立方：$t^3-3t$，$t=' + s + '$。', p: { v: 0, s: s, a2: s * s - 2, a3: s * s * s - 3 * s } };
    if (v === 1) return { q: '已知 ' + T('a^x-a^{-x}=' + s) + '，求 ' + T('a^{2x}+a^{-2x}') + ' 與 ' + T('a^{x}+a^{-x}') + '（' + T('a>0') + '）。', a: T(String(s * s + 2)) + '、' + T(sqrtTex(s * s + 4)), h: '$(a^x-a^{-x})^2=a^{2x}-2+a^{-2x}=' + s * s + '$；$(a^x+a^{-x})^2=(a^x-a^{-x})^2+4=' + (s * s + 4) + '$，且兩正數之和為正。', p: { v: 1, s: s, a2: s * s + 2, sum2: s * s + 4 } };
    if (v === 2) return { q: '已知 ' + T('a>1') + '、' + T('x>0') + ' 且 ' + T('a^x+a^{-x}=' + s) + '，求 ' + T('a^{x}-a^{-x}') + '。', a: T(sqrtTex(s * s - 4)), h: '$(a^x-a^{-x})^2=(a^x+a^{-x})^2-4=' + (s * s - 4) + '$；$a>1$、$x>0$ ⟹ $a^x>1>a^{-x}$，差為正，取正根。', p: { v: 2, s: s, d2: s * s - 4 } };
    var m = s * s - 2;
    return { q: '已知 ' + T('a^{2x}+a^{-2x}=' + m) + '，求 ' + T('a^{x}+a^{-x}') + '。', a: T(String(s)), h: '$(a^x+a^{-x})^2=a^{2x}+2+a^{-2x}=' + m + '+2=' + s * s + '$，兩正數之和為正，開根號取正。', p: { v: 3, s: s, m: m } };
  };

  /* 2-15 位數與首位數字 */
  L2.digitsLead = function (r) {
    var base = r.pick([2, 3, 6, 7, 12]), n, lg = { 2: 0.3010, 3: 0.4771, 6: 0.7781, 7: 0.8451, 12: 1.0791 }[base];
    var LG = [0, 0, 0.3010, 0.4771, 0.6021, 0.6990, 0.7782, 0.8451, 0.9031, 0.9542, 1];
    var v, d, mant, lead, safe = false, tries = 0;
    /* 四位對數表有截斷誤差：尾數若離某個 log k 太近就重抽（段考出題也是這樣避開的） */
    while (!safe && tries++ < 60) {
      n = r.int(15, 80); v = Math.round(n * lg * 10000) / 10000; d = Math.floor(v) + 1; mant = Math.round((v - Math.floor(v)) * 10000) / 10000;
      safe = true;
      for (var j = 1; j <= 10; j++) if (Math.abs(mant - LG[j]) < 0.004) safe = false;
      if (mant < 0.004) safe = false;
    }
    lead = 1;
    for (var k = 9; k >= 1; k--) if (mant >= LG[k] - 1e-12) { lead = k; break; }
    var given = (base === 12 || base === 6) ? '\\log2\\approx0.3010,\\ \\log3\\approx0.4771' : '\\log' + base + '\\approx' + lg.toFixed(4);
    return { q: '已知 ' + T(given) + '（必要時可用 $\\log2,\\log3$ 推其他值），問 ' + T(base + '^{' + n + '}') + ' 是幾位數？最高位數字是幾？',
             a: T(String(d)) + ' 位數，最高位數字 ' + T(String(lead)) + '　（' + T('\\log=' + v.toFixed(4)) + '，尾數 ' + T(mant.toFixed(4)) + '）',
             h: '$\\log' + base + '^{' + n + '}=' + n + '\\times' + lg.toFixed(4) + '$：整數部分（首數）$+1$ 是位數；小數部分（尾數）落在 $\\log k$ 與 $\\log(k+1)$ 之間 ⟹ 最高位是 $k$（$\\log2=0.3010$、$\\log3=0.4771$、$\\log5=0.6990$、$\\log7=0.8451$）。', p: { base: base, n: n, lg: lg, d: d, lead: lead } };
  };

  /* 2-16 (1/k)^n 小數點後第幾位出現非零 */
  L2.decimalFirst = function (r) {
    var base = r.pick([2, 3, 5, 6, 7]), n, lg = { 2: 0.3010, 3: 0.4771, 5: 0.6990, 6: 0.7781, 7: 0.8451 }[base], v, m, tries = 0;
    do { n = r.int(10, 60); v = -Math.round(n * lg * 10000) / 10000; m = v - Math.floor(v); } while ((m < 0.005 || m > 0.995) && tries++ < 60);
    var pos = -Math.floor(v);   /* log = −k + m ⟹ 第 k 位 */
    return { q: '已知 ' + T(base === 6 ? '\\log2\\approx0.3010,\\ \\log3\\approx0.4771' : '\\log' + base + '\\approx' + lg.toFixed(4)) + '，問 ' + T('\\left(\\dfrac1{' + base + '}\\right)^{' + n + '}') + ' 化成小數後，從小數點後第幾位開始出現不為 0 的數字？',
             a: '第 ' + T(String(pos)) + ' 位（' + T('\\log=-' + (n * lg).toFixed(4) + '=-' + pos + '+' + (pos - n * lg).toFixed(4)) + '）',
             h: (base === 6 ? '$\\log6=\\log2+\\log3\\approx0.3010+0.4771=0.7781$；' : '') + '$\\log\\left(\\dfrac1{' + base + '}\\right)^{' + n + '}=-' + n + '\\times' + lg.toFixed(4) + '$，把它寫成「負整數 $+$ 正小數」（例：$-2.3=-3+0.7$），那個負整數的絕對值就是位置。', p: { base: base, n: n, pos: pos } };
  };

  /* 2-17 複利：至少幾年超過 k 倍 */
  L2.compound = function (r) {
    var LG1 = { 2: 0.0086, 3: 0.0128, 4: 0.0170, 5: 0.0212, 6: 0.0253, 7: 0.0294, 8: 0.0334, 10: 0.0414 };
    var LGK = { 2: 0.3010, 3: 0.4771, 5: 0.6990, 10: 1 };
    var DEP = { 5: 0.0223, 10: 0.0458, 15: 0.0706, 20: 0.0969, 25: 0.1249, 30: 0.1549 };   /* −log(1−d%) */
    var v = r.int(0, 2), rate, k, lg1, lgk, ratio, tries = 0;
    /* 表值四位小數：商若太接近整數，表值算出來的年數可能與精確值差一年 ⟹ 重抽 */
    var n, nExact;
    do {   /* 表值算出的 n 必須與精確值一致（k 倍數大時表值誤差會放大），否則重抽 */
      rate = v === 2 ? r.pick([5, 10, 15, 20, 25, 30]) : r.pick([2, 3, 4, 5, 6, 7, 8, 10]); k = r.pick([2, 3, 5, 10]);
      lg1 = v === 2 ? DEP[rate] : LG1[rate]; lgk = LGK[k];
      ratio = lgk / lg1; n = Math.floor(ratio) + 1;
      nExact = 1; if (v === 2) { while (Math.pow(1 - rate / 100, nExact) >= 1 / k - 1e-12) nExact++; } else { while (Math.pow(1 + rate / 100, nExact) <= k + 1e-12) nExact++; }
    } while ((Math.abs(ratio - Math.round(ratio)) < 0.12 || n !== nExact) && tries++ < 60);
    var lgkT = k === 10 ? '' : ',\\ \\log' + k + '\\approx' + lgk.toFixed(4);
    if (v === 0) return { q: '本金以年利率 ' + T(rate + '\\%') + ' 每年複利一次，至少要幾年本利和才會超過本金的 ' + T(String(k)) + ' 倍？（' + T('\\log1.' + (rate < 10 ? '0' + rate : rate) + '\\approx' + lg1.toFixed(4) + lgkT) + '）',
             a: T(String(n)) + ' 年（' + T('n>\\dfrac{' + lgk.toFixed(4) + '}{' + lg1.toFixed(4) + '}\\approx' + ratio.toFixed(2)) + '）',
             h: '$(1.' + (rate < 10 ? '0' + rate : rate) + ')^n>' + k + '$ 兩邊取 $\\log$：$n\\times' + lg1.toFixed(4) + '>' + lgk.toFixed(4) + '$，算出 $n$ 的下界後向上取整。', p: { v: 0, rate: rate, k: k, n: n } };
    if (v === 1) {
      var P0 = r.pick([10, 20, 50, 100]);
      return { q: '小美存入 ' + T(String(P0)) + ' 萬元，年利率 ' + T(rate + '\\%') + '、每年複利一次。至少幾年後本利和會超過 ' + T(String(P0 * k)) + ' 萬元？（' + T('\\log1.' + (rate < 10 ? '0' + rate : rate) + '\\approx' + lg1.toFixed(4) + lgkT) + '）',
               a: T(String(n)) + ' 年（' + T('n>\\dfrac{' + lgk.toFixed(4) + '}{' + lg1.toFixed(4) + '}\\approx' + ratio.toFixed(2)) + '）',
               h: '$' + P0 + '(1.' + (rate < 10 ? '0' + rate : rate) + ')^n>' + P0 * k + '$，先兩邊除以 $' + P0 + '$ 變成「超過 $' + k + '$ 倍」，再取 $\\log$：$n\\times' + lg1.toFixed(4) + '>' + lgk.toFixed(4) + '$。', p: { v: 1, rate: rate, k: k, n: n, P0: P0 } };
    }
    var dec = (100 - rate) / 100, pct = Fr.tex(F(100, k), false);
    return { q: '某機器每年價值減少 ' + T(rate + '\\%') + '。至少幾年後，它的價值會不到原來的 ' + T('\\dfrac1{' + k + '}') + '？（' + T('\\log' + dec + '\\approx-' + lg1.toFixed(4) + lgkT) + '）',
             a: T(String(n)) + ' 年（' + T('n>\\dfrac{' + lgk.toFixed(4) + '}{' + lg1.toFixed(4) + '}\\approx' + ratio.toFixed(2)) + '）',
             h: '每年剩 $' + dec + '$ 倍：$' + dec + '^n<\\dfrac1{' + k + '}$，取 $\\log$ 得 $-' + lg1.toFixed(4) + 'n<-' + lgk.toFixed(4) + '$，除以負數不等號反向。', p: { v: 2, rate: rate, k: k, n: n } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p 重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     ══════════════════════════════════════════════════════════ */
  function parT(n) { return n < 0 ? '(' + n + ')' : String(n); }                 /* 負數代入時加括號 */
  function numT(v) { return v.toFixed(4).replace(/\.?0+$/, ''); }               /* 12.0400 → 12.04 */
  var L1_H1 = {
    rational: '這是「有理數／無理數判別」：問它能不能寫成「整數 ÷ 整數」——整數、有限小數、循環小數、開得盡的根號都可以，開不盡的根號與 $\\pi$ 都不行。',
    repPure: '這是「純循環小數化分數」：循環節當分子，分母寫幾個 9（循環節幾位就幾個 9），最後約分。',
    repMixed: '這是「混循環小數化分數」：分子＝「全部數字」－「不循環部分」，分母＝幾個 9 後接幾個 0，最後約分。',
    fracKind: '這是「分數化小數判有限或循環」：先把分母質因數分解，只有 2、5 就是有限小數，出現別的質因數就一定循環。',
    divPoint: '這是「數線上的內分點」：用分點公式「交叉配」，兩個坐標各配上「對面那段」的比，加起來再除以比的總和。',
    simpRoot: '這是「根式化簡」：把根號裡的數拆成「完全平方數 × 剩下的」，完全平方數開出來放外面。',
    addRoots: '這是「同類根式加減」：先把每一項各自化簡成同一個根號的倍數，再把前面的係數加減。',
    ratSingle: '這是「分母有理化（單項）」：分子分母同乘分母那個根號，分母就變成整數，最後約分。',
    ratConj: '這是「分母有理化（共軛）」：分子分母同乘分母的共軛（中間符號相反），用平方差把根號消掉。',
    doubleRoot: '這是「雙重根號」：找兩個數，和等於外層的數、積等於內層根號裡的數，就能湊成完全平方再開根號。',
    intFrac: '這是「整數部分與小數部分」：找出夾住它的兩個相鄰完全平方數，整數部分就出來了；小數部分＝原數－整數部分。',
    amgm: '這是「算幾不等式直接型」：兩個正數相加 $\\ge 2\\sqrt{\\text{乘積}}$，先確認乘積是定值，等號在兩數相等時成立。',
    absSimp: '這是「去絕對值符號」：先判斷每個絕對值裡面是正還是負，正的直接脫、負的變號脫，再合併同類項。',
    absEq: '這是「絕對值方程式」：把 $|x-a|=b$ 讀成「$x$ 與 $a$ 的距離是 $b$」，從 $a$ 往左、往右各走一次。',
    absIneq: '這是「絕對值不等式」：讀成「距離小於（或大於）某數」，小於取中間一段、大於取兩邊外面。',
    absSum2: '這是「兩點距離和的最小值」：把式子讀成「$x$ 到兩個定點的距離和」，$x$ 落在兩點之間時最小。',
    expLaw: '這是「指數律化簡」：同底相乘指數相加、相除指數相減、次方的次方指數相乘、根號改成分數指數。',
    expCompare: '這是「同底指數比較」：底數大於 1 時，指數越大值越大，所以只要比較指數。',
    sciNot: '這是「科學記號」：把小數點移到第一個非零數字後面，移了幾位就是 10 的幾次方（往左移是正、往右移是負）。',
    logBasic: '這是「常用對數基本值」：$\\log$ 問的是「10 的幾次方」，先把數字寫成 10 的次方。',
    digits: '這是「求位數」：先取 $\\log$ 把次方拉下來變成乘法，位數＝所得值的整數部分加 1。'
  };
  var L1_SOL = {};
  L1_SOL.rational = function (p, it) {
    var why = String(it.a).replace(/<b>[^<]*<\/b>/, '').replace(/^[\s　]*（/, '').replace(/）\s*$/, '');
    return ['判準：能寫成「整數 ÷ 整數」的就是有理數——整數、有限小數、循環小數、開得盡的根號都可以；開不盡的根號、$\\pi$、無限不循環小數都不行。',
      '看 $' + p.tex + '$：' + why + '。',
      '所以 $' + p.tex + '$ 是' + (p.rat ? '有理數' : '無理數') + '。'];
  };
  L1_SOL.repPure = function (p) {
    var m = p.rep.length, N = parseInt(p.rep, 10), P10 = Math.pow(10, m), den = P10 - 1, g = gcd(N, den);
    return ['設 $x=0.\\overline{' + p.rep + '}$，循環節「' + p.rep + '」有 ' + m + ' 位，兩邊同乘 $10^{' + m + '}$：$' + P10 + 'x=' + N + '.\\overline{' + p.rep + '}$。',
      '兩式相減，小數部分消掉：$' + P10 + 'x-x=' + den + 'x=' + N + '$ ⟹ $x=\\dfrac{' + N + '}{' + den + '}$（分母是 ' + m + ' 個 9）。',
      g > 1 ? '約分：分子分母同除以 $' + g + '$，得 $\\dfrac{' + N + '}{' + den + '}=' + Fr.tex(F(p.n, p.d)) + '$。'
            : '$' + N + '$ 與 $' + den + '$ 互質，$\\dfrac{' + N + '}{' + den + '}$ 已是最簡分數。'];
  };
  L1_SOL.repMixed = function (p) {
    var k = p.pre.length, m = p.rep.length, whole = p.pre + p.rep, W = parseInt(whole, 10), Pn = parseInt(p.pre, 10);
    var num = W - Pn, den = (Math.pow(10, m) - 1) * Math.pow(10, k), g = gcd(num, den);
    return ['$0.' + p.pre + '\\overline{' + p.rep + '}$：不循環部分「' + p.pre + '」有 ' + k + ' 位、循環節「' + p.rep + '」有 ' + m + ' 位。',
      '分子＝「' + whole + '」－「' + p.pre + '」$=' + W + '-' + Pn + '=' + num + '$；分母＝' + m + ' 個 9 後接 ' + k + ' 個 0 $=' + den + '$，得 $\\dfrac{' + num + '}{' + den + '}$。',
      g > 1 ? '約分：分子分母同除以 $' + g + '$，得 $\\dfrac{' + num + '}{' + den + '}=' + Fr.tex(F(p.n, p.d)) + '$。'
            : '$' + num + '$ 與 $' + den + '$ 互質，$\\dfrac{' + num + '}{' + den + '}$ 已是最簡分數。'];
  };
  L1_SOL.fracKind = function (p) {
    var d = p.d, x = d, pf = [], e2 = 0, e5 = 0, t = d;
    for (var q = 2; q <= x; q++) { var e = 0; while (x % q === 0) { x /= q; e++; } if (e) pf.push(e > 1 ? q + '^' + e : String(q)); }
    while (t % 2 === 0) { t /= 2; e2++; } while (t % 5 === 0) { t /= 5; e5++; }
    var ex = fracToRepeating(p.n, d);
    var st = [pf.length === 1 && pf[0] === String(d) ? '分母 $' + d + '$ 本身是質數，質因數只有 $' + d + '$。' : '分母質因數分解：$' + d + '=' + pf.join('\\times') + '$。'];
    if (p.fin) {
      var kk = Math.max(e2, e5), P10 = Math.pow(10, kk), mul = P10 / d;
      st.push('質因數只有 2、5 ⟹ 分母可以湊成 $10^{' + kk + '}$，所以是<b>有限小數</b>。');
      st.push('$\\dfrac{' + p.n + '}{' + d + '}=\\dfrac{' + p.n + '\\times' + mul + '}{' + d + '\\times' + mul + '}=\\dfrac{' + (p.n * mul) + '}{' + P10 + '}=0.' + ex.pre + '$。');
    } else {
      st.push('分母有 2、5 以外的質因數 $' + t + '$ ⟹ 永遠湊不成 10 的次方，所以是<b>循環小數</b>。');
      st.push('長除法 $' + p.n + '\\div' + d + '$：' + (ex.pre ? '先出現不循環的「' + ex.pre + '」，接著' : '') + '餘數開始重複，循環節是「' + ex.rep + '」，得 $\\dfrac{' + p.n + '}{' + d + '}=0.' + ex.pre + '\\overline{' + ex.rep + '}$。');
    }
    return st;
  };
  L1_SOL.divPoint = function (p) {
    var num = p.n * p.a + p.m * p.b, den = p.m + p.n, fr = F(num, den), g = gcd(num, den);
    return ['內分點公式（交叉配）：$\\overline{AP}:\\overline{PB}=m:n$ 時，$P=\\dfrac{n\\cdot a+m\\cdot b}{m+n}$——$A$ 的坐標配 $n$、$B$ 的坐標配 $m$。',
      '這裡 $a=' + p.a + '$、$b=' + p.b + '$、$m=' + p.m + '$、$n=' + p.n + '$：$P=\\dfrac{' + p.n + '\\times' + parT(p.a) + '+' + p.m + '\\times' + parT(p.b) + '}{' + p.m + '+' + p.n + '}=\\dfrac{' + num + '}{' + den + '}$。',
      (fr.d === 1 ? '$\\dfrac{' + num + '}{' + den + '}=' + fr.n + '$，' : (g > 1 ? '約分（同除以 $' + g + '$）得 $' + Fr.tex(fr) + '$，' : '$\\dfrac{' + num + '}{' + den + '}$ 已是最簡，')) + '所以 $P\\left(' + Fr.tex(fr) + '\\right)$。'];
  };
  L1_SOL.simpRoot = function (p) {
    return ['找 $' + p.n + '$ 的最大完全平方因數：$' + p.n + '=' + (p.c * p.c) + '\\times' + p.r + '=' + p.c + '^2\\times' + p.r + '$。',
      '完全平方開出來放外面：$\\sqrt{' + p.n + '}=\\sqrt{' + p.c + '^2}\\times\\sqrt{' + p.r + '}=' + p.c + '\\sqrt{' + p.r + '}$。'];
  };
  L1_SOL.addRoots = function (p) {
    var cs = p.cs, r = p.r, ns = cs.map(function (c) { return c * c * r; });
    var sg = function (c, first) { return c < 0 ? '-' : (first ? '' : '+'); };
    var items = ns.map(function (n, i) { var c = Math.abs(cs[i]); return c === 1 ? '$\\sqrt{' + n + '}$ 已是最簡' : '$\\sqrt{' + n + '}=\\sqrt{' + (c * c) + '\\times' + r + '}=' + c + '\\sqrt{' + r + '}$'; });
    var mid = cs.map(function (c, i) { return sg(c, i === 0) + Math.abs(c) + '\\sqrt{' + r + '}'; }).join('');
    var sum = cs.map(function (c, i) { return sg(c, i === 0) + Math.abs(c); }).join('');
    return ['先各自化簡：' + items.join('、') + '，都是 $\\sqrt{' + r + '}$ 的倍數。',
      '原式 $=' + mid + '=(' + sum + ')\\sqrt{' + r + '}$。',
      '係數 $' + sum + '=' + p.total + '$，所以原式 $=' + surdTex(0, p.total, r) + '$。'];
  };
  L1_SOL.ratSingle = function (p) {
    var g = gcd(p.a, p.r), num = p.a / g, den = p.r / g, raw = '\\dfrac{' + surdTex(0, p.a, p.r) + '}{' + p.r + '}';
    var st = ['分子分母同乘 $\\sqrt{' + p.r + '}$：$\\dfrac{' + p.a + '}{\\sqrt{' + p.r + '}}=\\dfrac{' + surdTex(0, p.a, p.r) + '}{\\sqrt{' + p.r + '}\\times\\sqrt{' + p.r + '}}=' + raw + '$。'];
    if (g > 1) st.push('分子分母同除以 $' + g + '$：$' + raw + '=' + (den === 1 ? surdTex(0, num, p.r) : '\\dfrac{' + surdTex(0, num, p.r) + '}{' + den + '}') + '$。');
    else st.push('$' + p.a + '$ 與 $' + p.r + '$ 互質，不能再約，答案就是 $' + raw + '$。');
    return st;
  };
  L1_SOL.ratConj = function (p) {
    var a = p.a, b = p.b, k = p.k, s = p.s, den = b * b - k;
    var dT = b + (s > 0 ? '+' : '-') + '\\sqrt{' + k + '}', cT = b + (s > 0 ? '-' : '+') + '\\sqrt{' + k + '}';
    var numT2 = surdTex(a * b, -s * a, k), fin = surdFracTex(a * b, -s * a, k, den), raw = '\\dfrac{' + numT2 + '}{' + den + '}', g = gcd(a, den), tail;
    if (den === 1) tail = '分母是 $1$，所以原式 $=' + fin + '$。';
    else if (den > 0 && g === 1) tail = '所以原式 $=' + raw + '$，已是最簡。';
    else tail = '所以原式 $=' + raw + '$' + (den < 0 ? '，分母為負就分子分母同乘 $-1$' : '') + (g > 1 ? '，再約去公因數 $' + g + '$' : '') + '，得 $' + fin + '$。';
    return ['分母 $' + dT + '$ 的共軛是 $' + cT + '$（中間符號相反），分子分母同乘它：$\\dfrac{' + a + '}{' + dT + '}=\\dfrac{' + a + '(' + cT + ')}{(' + dT + ')(' + cT + ')}$。',
      '分母用平方差：$(' + dT + ')(' + cT + ')=' + b + '^2-(\\sqrt{' + k + '})^2=' + (b * b) + '-' + k + '=' + den + '$；分子展開：$' + a + '(' + cT + ')=' + numT2 + '$。',
      tail];
  };
  L1_SOL.doubleRoot = function (p) {
    var inner = p.p + p.q, rad = p.p * p.q, pm = p.s > 0 ? '+' : '-';
    var Q = '\\sqrt{' + p.q + '}', P = p.p === 1 ? '1' : '\\sqrt{' + p.p + '}', fin = sqrtTex(p.q) + pm + sqrtTex(p.p), pre = Q + pm + P;
    return ['找兩個數，和是 $' + inner + '$、積是 $' + rad + '$：$' + p.q + '+' + p.p + '=' + inner + '$、$' + p.q + '\\times' + p.p + '=' + rad + '$，所以是 $' + p.q + '$ 與 $' + p.p + '$。',
      '根號裡湊成完全平方：$' + inner + pm + '2\\sqrt{' + rad + '}=(' + Q + ')^2+(' + P + ')^2' + pm + '2\\cdot' + Q + '\\cdot' + P + '=(' + pre + ')^2$。',
      '開根號（大的放前面，結果才是正的）：$\\sqrt{(' + pre + ')^2}=' + pre + (fin === pre ? '' : '=' + fin) + '$。'];
  };
  L1_SOL.intFrac = function (p) {
    var k = p.k;
    return ['找夾住 $' + p.n + '$ 的相鄰完全平方數：$' + (k * k) + '\\lt ' + p.n + '\\lt ' + ((k + 1) * (k + 1)) + '$，即 $' + k + '^2\\lt ' + p.n + '\\lt ' + (k + 1) + '^2$。',
      '三邊開根號：$' + k + '\\lt\\sqrt{' + p.n + '}\\lt ' + (k + 1) + '$，所以整數部分 $a=' + k + '$。',
      '小數部分＝原數－整數部分：$b=\\sqrt{' + p.n + '}-' + k + '$。'];
  };
  L1_SOL.amgm = function (p) {
    if (p.v === 2) {
      var s = isqrt(p.P);
      return ['算幾不等式：$x,y\\gt 0$ 時 $\\dfrac{x+y}{2}\\ge\\sqrt{xy}$，即 $x+y\\ge2\\sqrt{xy}$。',
        '$xy=' + p.P + '$ 是定值：$x+y\\ge2\\sqrt{' + p.P + '}=2\\times' + s + '=' + p.min + '$。',
        '等號在 $x=y$ 時成立，配合 $xy=' + p.P + '$ 得 $x=y=' + s + '$；最小值 $' + p.min + '$，此時 $(x,y)=(' + s + ',' + s + ')$。'];
    }
    var c = p.c, k = p.k, ck = c * k, cx = coefTex(c, 'x'), st = [];
    if (p.v === 1) st.push('先把分式拆開：$\\dfrac{' + coefTex(c, 'x^2') + '+' + k + '}{x}=\\dfrac{' + coefTex(c, 'x^2') + '}{x}+\\dfrac{' + k + '}{x}=' + cx + '+\\dfrac{' + k + '}{x}$。');
    st.push('$' + cx + '$ 與 $\\dfrac{' + k + '}{x}$ 都是正數，且乘積 $' + cx + '\\cdot\\dfrac{' + k + '}{x}=' + ck + '$ 是定值，可用算幾不等式。');
    st.push('$' + cx + '+\\dfrac{' + k + '}{x}\\ge2\\sqrt{' + cx + '\\cdot\\dfrac{' + k + '}{x}}=2\\sqrt{' + ck + '}=2\\times' + isqrt(ck) + '=' + p.min + '$。');
    st.push('等號在 $' + cx + '=\\dfrac{' + k + '}{x}$ ⟹ $x^2=' + Fr.tex(F(k, c)) + '$ ⟹ $x=' + Fr.tex(F(p.xn, p.xd)) + '$（$x\\gt 0$ 取正）。');
    return st;
  };
  L1_SOL.absSimp = function (p) {
    var k = p.k, c = p.c, v = p.v;
    if (v === 0) return ['$a\\lt b$ ⟹ $a-b\\lt 0$，負的要變號脫：$|a-b|=-(a-b)=b-a$。',
      '$b-a\\gt 0$，再加 $' + k + '$ 還是正的，直接脫：$|b-a+' + k + '|=b-a+' + k + '$。',
      '相加：$(b-a)+(b-a+' + k + ')=2b-2a+' + k + '$。'];
    if (v === 1) return ['$a\\lt b$ ⟹ $a-b\\lt 0$，再減 $' + k + '$ 更小，變號脫：$|a-b-' + k + '|=-(a-b-' + k + ')=b-a+' + k + '$。',
      '$b-a\\gt 0$ 直接脫：$|b-a|=b-a$。',
      '相減：$(b-a+' + k + ')-(b-a)=' + k + '$。'];
    if (v === 2) return ['$a\\lt b$ ⟹ $a-b\\lt 0$，變號脫：$|a-b|=b-a$。',
      '$a-b-' + k + '$ 更小也是負的，變號脫：$|a-b-' + k + '|=b-a+' + k + '$。',
      '相減：$(b-a)-(b-a+' + k + ')=-' + k + '$，$a,b$ 都消掉了。'];
    if (v === 3) {
      var e1 = linTex(1, -c), e2 = linTex(1, -c - k), f1 = linTex(-1, c), f2 = linTex(-1, c + k);
      return ['$x\\lt ' + c + '$ ⟹ $' + e1 + '\\lt 0$，變號脫：$|' + e1 + '|=-(' + e1 + ')=' + f1 + '$。',
        '$x\\lt ' + c + '\\lt ' + (c + k) + '$ ⟹ $' + e2 + '\\lt 0$，也要變號脫：$|' + e2 + '|=' + f2 + '$。',
        '相加：$(' + f1 + ')+(' + f2 + ')=' + linTex(-2, 2 * c + k) + '$。'];
    }
    if (v === 4) {
      var g1 = linTex(1, -c), g2 = linTex(-1, c - k), g3 = linTex(1, k - c);
      return ['$x\\gt ' + c + '$ ⟹ $' + g1 + '\\gt 0$，直接脫：$|' + g1 + '|=' + g1 + '$。',
        '$' + g2 + '=-(' + g3 + ')$，而 $x\\gt ' + c + '$ ⟹ $' + g3 + '\\gt 0$，所以 $|' + g2 + '|=' + g3 + '$。',
        '相減：$(' + g1 + ')-(' + g3 + ')=-' + k + '$。'];
    }
    if (v === 5) {
      var j1 = linTex(1, -c), j2 = linTex(1, -c - k), j3 = linTex(-1, c + k);
      return ['$x\\gt ' + c + '$ ⟹ $' + j1 + '\\gt 0$，直接脫：$|' + j1 + '|=' + j1 + '$。',
        '$x\\lt ' + (c + k) + '$ ⟹ $' + j2 + '\\lt 0$，變號脫：$|' + j2 + '|=' + j3 + '$。',
        '相加：$(' + j1 + ')+(' + j3 + ')=' + k + '$，$x$ 消掉了。'];
    }
    return ['$\\sqrt{(a-b)^2}=|a-b|$（平方再開根號得到的是絕對值，不是 $a-b$）。',
      '$a\\lt b$ ⟹ $a-b\\lt 0$：$|a-b|=b-a$；而 $b-a\\gt 0$：$|b-a|=b-a$。',
      '相加：$(b-a)+(b-a)=2b-2a$。'];
  };
  L1_SOL.absEq = function (p) {
    var a = p.a, b = p.b, E = absLin(1, -a), inner = linTex(1, -a);
    return ['$' + E + '=' + b + '$ 讀成「$x$ 與 $' + a + '$ 的距離是 $' + b + '$」，所以 $' + inner + '=' + b + '$ 或 $' + inner + '=-' + b + '$。',
      '$' + inner + '=' + b + '$ ⟹ $x=' + a + '+' + b + '=' + (a + b) + '$；$' + inner + '=-' + b + '$ ⟹ $x=' + a + '-' + b + '=' + (a - b) + '$。'];
  };
  L1_SOL.absIneq = function (p) {
    var a = p.a, b = p.b, E = absLin(1, -a), inner = linTex(1, -a);
    if (p.less) return ['$' + E + '\\lt ' + b + '$ 讀成「$x$ 與 $' + a + '$ 的距離小於 $' + b + '$」，即 $-' + b + '\\lt ' + inner + '\\lt ' + b + '$。',
      '三邊同加 $' + a + '$：$' + a + '-' + b + '\\lt x\\lt ' + a + '+' + b + '$，即 $' + (a - b) + '\\lt x\\lt ' + (a + b) + '$。'];
    return ['$' + E + '\\gt ' + b + '$ 讀成「$x$ 與 $' + a + '$ 的距離大於 $' + b + '$」，即 $' + inner + '\\lt -' + b + '$ 或 $' + inner + '\\gt ' + b + '$。',
      '各自移項：$x\\lt ' + a + '-' + b + '=' + (a - b) + '$ 或 $x\\gt ' + a + '+' + b + '=' + (a + b) + '$。'];
  };
  L1_SOL.absSum2 = function (p) {
    var a = p.a, b = p.b, tex = absLin(1, -a) + '+' + absLin(1, -b);
    return ['$' + tex + '$ 是「$x$ 到 $' + a + '$ 的距離」加「$x$ 到 $' + b + '$ 的距離」。',
      '畫數線：$x$ 在 $' + a + '$ 與 $' + b + '$ 之間時，兩段距離剛好拼成 $' + a + '$ 到 $' + b + '$ 這一段；$x$ 跑到外面，距離和只會更大。',
      '最小值＝兩定點的距離 $' + b + '-' + parT(a) + '=' + p.min + '$，發生在 $' + a + '\\le x\\le ' + b + '$ 時。'];
  };
  L1_SOL.expLaw = function (p) {
    var B = p.base;
    if (p.v === 0) return ['同底相乘，指數相加：$' + B + '^{' + p.m + '}\\cdot ' + B + '^{' + p.n + '}=' + B + '^{' + p.m + '+' + p.n + '}=' + B + '^{' + (p.m + p.n) + '}$。',
      '同底相除，指數相減：$' + B + '^{' + (p.m + p.n) + '}\\div ' + B + '^{' + p.k + '}=' + B + '^{' + (p.m + p.n) + '-' + p.k + '}=' + B + '^{' + (p.m + p.n - p.k) + '}' + powTail(B, p.m + p.n - p.k) + '$。'];
    if (p.v === 1) return ['次方的次方，指數相乘：$\\left(' + B + '^{' + p.m + '}\\right)^{' + p.k + '}=' + B + '^{' + p.m + '\\times' + p.k + '}=' + B + '^{' + (p.m * p.k) + '}$。',
      '同底相除，指數相減：$' + B + '^{' + (p.m * p.k) + '}\\div ' + B + '^{' + p.n + '}=' + B + '^{' + (p.m * p.k) + '-' + p.n + '}=' + B + '^{' + (p.m * p.k - p.n) + '}' + powTail(B, p.m * p.k - p.n) + '$' + (p.m * p.k - p.n === 0 ? '（任何非零數的 $0$ 次方都是 $1$）' : '') + '。'];
    var ex = p.q === 1 ? String(p.p) : '\\frac{' + p.p + '}{' + p.q + '}';
    return ['根號改分數指數的規則：$\\sqrt[q]{a^{p}}=a^{\\frac{p}{q}}$，根指數放分母、次方放分子。',
      '這裡根指數是 $' + p.q + '$、次方是 $' + p.p + '$：$\\sqrt[' + p.q + ']{' + powT(B, p.p) + '}=' + B + '^{' + ex + '}$。'];
  };
  L1_SOL.expCompare = function (p) {
    var lbl = ['a', 'b', 'c'], es = p.es, idx = [0, 1, 2].sort(function (i, j) { return es[j] - es[i]; });
    return ['底數 $' + p.base + '\\gt 1$，指數越大值越大（負指數是分數，最小；指數 $0$ 就是 $1$）。',
      '只比指數：$a$ 的指數 $' + es[0] + '$、$b$ 的指數 $' + es[1] + '$、$c$ 的指數 $' + es[2] + '$，由大到小是 $' + idx.map(function (i) { return es[i]; }).join('\\gt ') + '$。',
      '所以 $' + idx.map(function (i) { return lbl[i]; }).join('\\gt ') + '$。'];
  };
  L1_SOL.sciNot = function (p) {
    var m = p.m, e = p.e, big = e > 0, val = big ? String(m) + '0'.repeat(e - 2) : '0.' + '0'.repeat(-e - 1) + String(m);
    var aT = String(m / 100), lead = String(m)[0];
    var s1 = '把小數點移到第一個非零數字 $' + lead + '$ 的後面：$' + val + '$ 變成 $' + aT + '$（符合 $1\\le ' + aT + '\\lt 10$）。';
    if (big) return [s1, '小數點原本在最右邊，往左移了 $' + e + '$ 位，等於除以 $10^{' + e + '}$，要補回來乘 $10^{' + e + '}$：$' + val + '=' + aT + '\\times10^{' + e + '}$。'];
    return [s1, '小數點往右移了 $' + (-e) + '$ 位，等於乘以 $10^{' + (-e) + '}$，要補回來乘 $10^{' + e + '}$（往右移是負指數）：$' + val + '=' + aT + '\\times10^{' + e + '}$。'];
  };
  L1_SOL.logBasic = function (p) {
    if (p.v === 0) return ['$\\log N$ 問的是「$10$ 的幾次方等於 $N$」，所以 $\\log10^{n}=n$。',
      '$10^{' + p.k + '}$ 已經是 $10$ 的次方，次方就是 $' + p.k + '$：$\\log10^{' + p.k + '}=' + p.k + '$。'];
    if (p.v === 1) return ['先把 $' + p.n + '$ 寫成 $10$ 的次方：$' + p.n + '=10^{' + p.ans + '}$' + (p.ans < 0 ? '（小於 $1$ 的是負次方）' : '') + '。',
      '$\\log ' + p.n + '=\\log10^{' + p.ans + '}=' + p.ans + '$。'];
    var la = { 2: 0.3010, 3: 0.4771, 5: 0.6990, 7: 0.8451 }[p.a];
    return ['乘積的對數＝對數相加：$\\log(' + p.a + '\\times10^{' + p.e + '})=\\log ' + p.a + '+\\log10^{' + p.e + '}$。',
      '$\\log10^{' + p.e + '}=' + p.e + '$，再代入 $\\log ' + p.a + '\\approx' + la.toFixed(4) + '$：$' + la.toFixed(4) + '+' + p.e + '=' + (la + p.e).toFixed(4) + '$。'];
  };
  L1_SOL.digits = function (p) {
    var v = Math.round(p.n * p.lg * 10000) / 10000, fl = Math.floor(v), vT = numT(v);
    return ['取 $\\log$ 把次方拉下來：$\\log ' + p.base + '^{' + p.n + '}=' + p.n + '\\log ' + p.base + '\\approx' + p.n + '\\times' + p.lg.toFixed(4) + '=' + vT + '$。',
      '$' + fl + '\\le ' + vT + '\\lt ' + (fl + 1) + '$ ⟹ $10^{' + fl + '}\\le ' + p.base + '^{' + p.n + '}\\lt 10^{' + (fl + 1) + '}$。',
      '$10^{' + fl + '}$ 是最小的 $' + (fl + 1) + '$ 位數，所以 $' + p.base + '^{' + p.n + '}$ 是 $' + (fl + 1) + '$ 位數（位數＝整數部分 $' + fl + '$ 加 $1$）。'];
  };

  var META_L1 = [
      ['rational', '§1 有理數／無理數判別'], ['repPure', '§1 純循環小數化分數'], ['repMixed', '§1 混循環小數化分數'],
      ['fracKind', '§1 分數化小數：有限還是循環'], ['divPoint', '§1 數線上的內分點'],
      ['simpRoot', '§2 根式化簡'], ['addRoots', '§2 同類根式加減'], ['ratSingle', '§2 分母有理化（單項）'],
      ['ratConj', '§2 分母有理化（共軛）'], ['doubleRoot', '§2 雙重根號（直接拆）'], ['intFrac', '§2 整數部分與小數部分'],
      ['amgm', '§2 算幾不等式（直接型）'],
      ['absSimp', '§3 去絕對值符號'], ['absEq', '§3 絕對值方程式'], ['absIneq', '§3 絕對值不等式'], ['absSum2', '§3 兩點距離和的最小值'],
      ['expLaw', '§4 指數律化簡'], ['expCompare', '§4 同底指數比較'], ['sciNot', '§4 科學記號'], ['logBasic', '§4 常用對數基本值'], ['digits', '§4 位數']
  ];
  var META_L2 = [
      ['repArith', '§1 循環小數的四則'], ['nthDigit', '§1 小數點後第 n 位'], ['coefCompare', '§1 有理化＋係數比較'],
      ['intFracOp', '§2 整數／小數部分再運算'], ['doubleRoot2', '§2 雙重根號（先提 2）'], ['symm', '§2 $x+\\frac1x$ 對稱式'], ['amgmCond', '§2 算幾：條件式×目標式'],
      ['absIneq2', '§3 絕對值不等式三型'], ['absSumIneq', '§3 距離和不等式'], ['absMedian', '§3 加權距離和最小值'], ['absParam', '§3 反推參數'], ['absIntCount', '§3 整數解個數'],
      ['expEq', '§4 指數方程式（換元）'], ['expSymm', '§4 $a^x\\pm a^{-x}$ 升冪'], ['digitsLead', '§4 位數與最高位數字'], ['decimalFirst', '§4 小數點後第幾位非零'], ['compound', '§4 複利幾年']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     答案全部精確（整數、分數、根式、log 的組合），p 給 Python 獨立驗算。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};
  function nonSquare(r, lo, hi) { var n = r.int(lo, hi); while (isSquare(n)) n = r.int(lo, hi); return n; }
  function pfTex(n) { var out = [], x = n; for (var q = 2; q <= x; q++) { var e = 0; while (x % q === 0) { x /= q; e++; } if (e) out.push(e > 1 ? q + '^' + e : String(q)); } return out.join('\\times'); }

  /* L3-1　有限小數＋循環小數：遠處的第 N 位只看循環那一項 */
  L3.farDigit = function (r) {
    var d1 = r.pick([8, 16, 40, 25, 125, 20, 32, 80]), a = r.int(1, d1 - 1); while (gcd(a, d1) !== 1) a = r.int(1, d1 - 1);
    var d2 = r.pick([7, 13, 27, 37, 41, 271, 101, 11, 33, 99, 111, 21]), b = r.int(1, d2 - 1); while (gcd(b, d2) !== 1) b = r.int(1, d2 - 1);
    var N = r.pick([100, 2024, 2025, 2026, 500, 1000, 111, 2020, 333]);
    var ex1 = fracToRepeating(a, d1), ex2 = fracToRepeating(b, d2), m = ex2.rep.length, k = ex1.pre.length;
    var digit = parseInt(ex2.rep[(N - 1) % m], 10);   /* d2 與 10 互質 ⟹ 純循環 */
    return { q: '將 ' + T('\\dfrac{' + a + '}{' + d1 + '}+\\dfrac{' + b + '}{' + d2 + '}') + ' 化為小數，求小數點後第 ' + T(String(N)) + ' 位的數字。',
      a: T(String(digit)), h: '$\\dfrac{' + a + '}{' + d1 + '}=0.' + ex1.pre + '$ 只有 ' + k + ' 位；$\\dfrac{' + b + '}{' + d2 + '}=0.\\overline{' + ex2.rep + '}$（週期 ' + m + '）。第 ' + N + ' 位遠在有限小數之後（進位只會往左傳），所以只看循環那一項：$' + N + '=' + m + '\\times' + Math.floor((N - 1) / m) + '+' + ((N - 1) % m + 1) + '$，取週期的第 ' + ((N - 1) % m + 1) + ' 個數字。',
      p: { a: a, d1: d1, b: b, d2: d2, N: N, digit: digit } };
  };

  /* L3-2　帶分數開根號：N + 1/m² 的分子是完全平方 (m²±1)² */
  L3.sqrtMixedDigit = function (r) {
    var m = r.pick([7, 11, 13, 21, 27, 37, 41, 33, 99, 101, 111, 9, 3]), sgn = r.sign(), Nw = m * m + 2 * sgn;
    var K = r.pick([50, 100, 111, 2024, 2025, 500, 77, 1000]);
    var frac = sgn > 0 ? F(1, m) : F(m - 1, m), ip = sgn > 0 ? m : m - 1;   /* √ = m ± 1/m */
    var ex = fracToRepeating(frac.n, frac.d), digit = parseInt(ex.rep[(K - 1) % ex.rep.length], 10);
    return { q: '求 ' + T('\\sqrt{' + Nw + '\\dfrac{1}{' + m * m + '}}') + ' 化為小數後，小數點後第 ' + T(String(K)) + ' 位的數字。',
      a: T(String(digit)), h: '$' + Nw + '\\dfrac1{' + m * m + '}=\\dfrac{' + Nw + '\\times' + m * m + '+1}{' + m * m + '}=\\dfrac{' + (Nw * m * m + 1) + '}{' + m * m + '}$，分子 $=(' + (m * m + sgn) + ')^2$、分母 $=' + m + '^2$，所以 $\\sqrt{\\cdot}=\\dfrac{' + (m * m + sgn) + '}{' + m + '}=' + (sgn > 0 ? m + '+\\dfrac1{' + m + '}' : m + '-\\dfrac1{' + m + '}=' + (m - 1) + '+\\dfrac{' + (m - 1) + '}{' + m + '}') + '$；再看 $' + Fr.tex(frac) + '=0.\\overline{' + ex.rep + '}$（週期 ' + ex.rep.length + '）的第 ' + K + ' 位。',
      p: { m: m, sgn: sgn, N: Nw, K: K, ip: ip, digit: digit } };
  };

  /* L3-3　有理係數比較：(A+B√k)x + (y−c)(C−D√k) = E+F√k */
  L3.coefCompareLin = function (r) {
    var k = r.pick([2, 3, 5, 6, 7]), A = r.int(1, 9), B = r.int(1, 3), C = r.int(1, 6), Dd = r.int(1, 3), c = r.int(1, 5);
    var x = r.int(-5, 6), y = r.int(-5, 8); if (x === 0) x = 2; if (y === c) y = c + 3;
    var E = A * x + C * (y - c), Fv = B * x - Dd * (y - c);
    return { q: '設 ' + T('x,y') + ' 為有理數，且 ' + T('(' + surdTex(A, B, k) + ')x+(y-' + c + ')(' + surdTex(C, -Dd, k) + ')=' + surdTex(E, Fv, k)) + '，求 ' + T('(x,y)') + '。',
      a: T('(x,y)=(' + x + ',\\ ' + y + ')'), h: '把左式整理成「有理部分」＋「無理部分」$\\sqrt{' + k + '}$：有理部分 $' + coefTex(A, 'x') + '+' + (C === 1 ? '' : C) + '(y-' + c + ')=' + E + '$，無理部分 $' + coefTex(B, 'x') + '-' + (Dd === 1 ? '' : Dd) + '(y-' + c + ')=' + Fv + '$（前提：$x,y$ 有理而 $\\sqrt{' + k + '}$ 無理），解聯立。',
      p: { k: k, A: A, B: B, C: C, D: Dd, c: c, x: x, y: y, E: E, F: Fv } };
  };

  /* L3-4　雙重根號＋有理係數：x√(a1²+b1²k+2a1b1√k) − y√(a2²+b2²k−2a2b2√k) = E+F√k */
  L3.doubleRootCoef = function (r) {
    var k = r.pick([2, 3, 5, 6, 7]), a1 = r.int(1, 4), b1 = r.int(1, 3), a2 = r.int(1, 3), b2 = r.int(1, 3);
    while (a2 * a2 >= b2 * b2 * k) b2++;                       /* 第二個根號要 b2√k > a2，開出來是 b2√k − a2 */
    var rt2 = (b2 === 1 ? '' : b2) + '\\sqrt{' + k + '}-' + a2;
    var x = r.int(1, 5), y = r.int(1, 5);
    var E = a1 * x + a2 * y, Fv = b1 * x - b2 * y;             /* x(a1+b1√k) − y(b2√k − a2) */
    var in1 = (a1 * a1 + b1 * b1 * k) + '+' + (2 * a1 * b1) + '\\sqrt{' + k + '}', in2 = (a2 * a2 + b2 * b2 * k) + '-' + (2 * a2 * b2) + '\\sqrt{' + k + '}';
    return { q: '設 ' + T('x,y') + ' 為有理數，' + T('x\\sqrt{' + in1 + '}-y\\sqrt{' + in2 + '}=' + surdTex(E, Fv, k)) + '，求 ' + T('(x,y)') + '。',
      a: T('(x,y)=(' + x + ',\\ ' + y + ')'), h: '先拆雙重根號：$\\sqrt{' + in1 + '}=\\sqrt{(' + (a1 * a1) + '+' + (b1 * b1 * k) + ')+2\\sqrt{' + (a1 * a1 * b1 * b1 * k) + '}}=' + surdTex(a1, b1, k) + '$；$\\sqrt{' + in2 + '}=' + rt2 + '$（大減小）。代入後有理、無理部分各自相等：$' + coefTex(a1, 'x') + '+' + coefTex(a2, 'y') + '=' + E + '$、$' + coefTex(b1, 'x') + '-' + coefTex(b2, 'y') + '=' + Fv + '$。',
      p: { k: k, a1: a1, b1: b1, a2: a2, b2: b2, x: x, y: y, E: E, F: Fv } };
  };

  /* L3-5　根式相減比大小：√(m+d)−√m 有理化成 d/(√(m+d)+√m)，分子相同比分母 */
  L3.surdDiffOrder = function (r) {
    var d = r.int(1, 6), ms = [], guard = 0;
    while (ms.length < 3 && guard++ < 200) { var m = r.int(2, 40); if (isSquare(m) || isSquare(m + d) || ms.indexOf(m) >= 0) continue; ms.push(m); }
    if (ms.length < 3) ms = [5, 11, 23];
    var lbl = ['a', 'b', 'c'], items = ms.map(function (m, i) { return lbl[i] + '=\\sqrt{' + (m + d) + '}-\\sqrt{' + m + '}'; });
    var order = [0, 1, 2].sort(function (i, j) { return ms[i] - ms[j]; }).map(function (i) { return lbl[i]; });   /* m 越小值越大 */
    return { q: '設 ' + T(items.join(',\\ ')) + '，比較 ' + T('a,b,c') + ' 的大小（由大到小）。', a: T(order.join('\\gt ')),
      h: '$\\sqrt{m+' + d + '}-\\sqrt m=\\dfrac{' + d + '}{\\sqrt{m+' + d + '}+\\sqrt m}$：三個分子都是 $' + d + '$，分母是 $' + ms.map(function (m) { return '\\sqrt{' + (m + d) + '}+\\sqrt{' + m + '}'; }).join('$、$') + '$，分母大的值小。', p: { d: d, ms: ms, order: order } };
  };

  /* L3-6　二次方程 ÷ x 得 x∓1/x，再算對稱式 */
  L3.symmFromQuad = function (r) {
    var fam = r.int(0, 2), b = fam === 2 ? r.int(3, 8) : r.int(1, 6), ask = r.int(0, 3);
    var s = fam === 0 ? b : fam === 1 ? -b : b;                 /* fam 0/1：x−1/x = s；fam 2：x+1/x = s */
    var eq = fam === 0 ? 'x^2-' + coefTex(b, 'x') + '-1=0' : fam === 1 ? 'x^2+' + coefTex(b, 'x') + '-1=0' : 'x^2-' + coefTex(b, 'x') + '+1=0';
    var p2 = fam === 2 ? s * s - 2 : s * s + 2;                 /* x²+1/x² */
    var p3 = fam === 2 ? s * s * s - 3 * s : s * s * s + 3 * s;   /* x³±1/x³（fam 2 為 +，其餘為 −）*/
    var p4 = p2 * p2 - 2;
    var cube = fam === 2 ? 'x^3+\\dfrac1{x^3}' : 'x^3-\\dfrac1{x^3}';
    var asks = ['x^2+\\dfrac1{x^2}', cube, fam === 2 ? 'x^3+x^2+\\dfrac1{x^2}+\\dfrac1{x^3}' : 'x^3+x^2+\\dfrac1{x^2}-\\dfrac1{x^3}', 'x^4+\\dfrac1{x^4}'];
    var ans = [p2, p3, p2 + p3, p4][ask], base = fam === 2 ? 'x+\\dfrac1x=' + s : 'x-\\dfrac1x=' + s;
    return { q: '設 ' + T('x>0') + ' 且 ' + T(eq) + '，求 ' + T(asks[ask]) + ' 之值。', a: T(String(ans)),
      h: '$x\\ne0$，兩邊除以 $x$：$' + base + '$。再用 $' + (fam === 2 ? 'x^2+\\frac1{x^2}=(x+\\frac1x)^2-2' : 'x^2+\\frac1{x^2}=(x-\\frac1x)^2+2') + '$' + (ask >= 1 && ask !== 3 ? '、$' + (fam === 2 ? 'x^3+\\frac1{x^3}=(x+\\frac1x)^3-3(x+\\frac1x)' : 'x^3-\\frac1{x^3}=(x-\\frac1x)^3+3(x-\\frac1x)') + '$' : '') + (ask === 3 ? '、$x^4+\\frac1{x^4}=(x^2+\\frac1{x^2})^2-2$' : '') + '。',
      p: { fam: fam, b: b, ask: ask, s: s, ans: ans } };
  };

  /* L3-7　乘積為定值、求線性式最小：px+qy = p(x−a)+q(y+b)+(pa−qb) */
  L3.amgmLinProduct = function (r) {
    var p = r.int(1, 5), q = r.int(1, 5), sroot = r.int(3, 12), a = r.int(1, 5), b = r.int(1, 5);
    var K = F(sroot * sroot, p * q), minv = 2 * sroot + p * a - q * b, xe = Fr.add(F(a), F(sroot, p)), ye = Fr.sub(F(sroot, q), F(b));
    var cond = '(x-' + a + ')(y' + (b === 0 ? '' : '+' + b) + ')=' + Fr.tex(K), tgt = coefTex(p, 'x') + '+' + coefTex(q, 'y');
    return { q: '設 ' + T('x>' + a) + '，' + T('y>' + (-b)) + '，且 ' + T(cond) + '，求 ' + T(tgt) + ' 的最小值，並求此時的 ' + T('(x,y)') + '。',
      a: '最小值 ' + T(String(minv)) + '，' + T('(x,y)=\\left(' + Fr.tex(xe, false) + ',\\ ' + Fr.tex(ye, false) + '\\right)'),
      h: '把目標拆成條件裡的兩個因式：$' + tgt + '=' + p + '(x-' + a + ')+' + q + '(y' + (b === 0 ? '' : '+' + b) + ')+(' + (p * a - q * b) + ')$，前兩項的乘積 $=' + p * q + '\\times' + Fr.tex(K, false) + '=' + sroot * sroot + '$ 是定值 ⟹ 前兩項之和 $\\ge2\\sqrt{' + sroot * sroot + '}=' + 2 * sroot + '$，等號在兩項都等於 $' + sroot + '$。',
      p: { p: p, q: q, a: a, b: b, Kn: K.n, Kd: K.d, s: sroot, min: minv, xn: xe.n, xd: xe.d, yn: ye.n, yd: ye.d } };
  };

  /* L3-8　平均成本最低：總維修費是等差級數和 kn²+(a−k)n，平均 = C/n + kn + (a−k) */
  L3.avgCostMin = function (r) {
    var k = r.pick([1, 1, 2, 3]), m = r.int(4, 15), C = k * m * m, a = k + r.pick([0, 0, 1, 2, 3, 5]);
    var fee = (2 * k) + 'n' + (a - 2 * k === 0 ? '' : signed(a - 2 * k)), minv = 2 * k * m + a - k;
    return { q: '某公司買一台機器花 ' + T(String(C)) + ' 萬元，第 ' + T('n') + ' 年的維修費為 ' + T('(' + fee + ')') + ' 萬元（第 1 年 ' + a + ' 萬、第 2 年 ' + (a + 2 * k) + ' 萬、第 3 年 ' + (a + 4 * k) + ' 萬、……）。若使用 ' + T('n') + ' 年後報廢，問使用幾年時「每年平均總花費」最低？最低是多少？',
      a: T(String(m)) + ' 年，每年平均 ' + T(String(minv)) + ' 萬元',
      h: '前 $n$ 年維修費總和是等差級數：$\\dfrac{n(' + a + '+' + fee + ')}{2}=' + coefTex(k, 'n^2') + (a - k === 0 ? '' : '+' + coefTex(a - k, 'n')) + '$；平均 $=\\dfrac{' + C + '}{n}+' + coefTex(k, 'n') + (a - k === 0 ? '' : signed(a - k)) + '$，典型的 $\\dfrac Kx+kx$，算幾等號在 $\\dfrac{' + C + '}{n}=' + coefTex(k, 'n') + '$，即 $n^2=' + m * m + '$。',
      p: { C: C, k: k, a: a, m: m, min: minv } };
  };

  /* L3-9　|x−a| = m|x−b|：內分點 (a+mb)/(m+1) 與外分點 (mb−a)/(m−1) */
  L3.absRatioPoints = function (r) {
    var a = r.int(-6, 4), b = a + r.int(1, 8), m = r.pick([2, 3, 4, 5]), v = r.int(0, 1);
    var x1 = F(a + m * b, m + 1), x2 = F(m * b - a, m - 1);   /* x1 內分點（在 a,b 之間）、x2 外分點（在 b 右側）*/
    var eq = absLin(1, -a) + '=' + m + absLin(1, -b);
    if (v === 0) return { q: '解方程式 ' + T(eq) + '。', a: T('x=' + Fr.tex(x1, false) + '\\ \\text{或}\\ x=' + Fr.tex(x2, false)),
      h: '$' + absLin(1, -a) + '=' + m + absLin(1, -b) + '$ ⟹ $' + linTex(1, -a) + '=\\pm' + m + '(' + linTex(1, -b) + ')$，兩個方程式各解一次。幾何意義：$P$ 到 $A(' + a + ')$ 的距離是到 $B(' + b + ')$ 的 $' + m + '$ 倍，內分點與外分點各一個。', p: { a: a, b: b, m: m, v: 0, x1n: x1.n, x1d: x1.d, x2n: x2.n, x2d: x2.d } };
    return { q: '數線上 ' + T('A(' + a + ')') + '、' + T('B(' + b + ')') + '，點 ' + T('P(x)') + ' 滿足 ' + T('\\overline{PA}=' + m + '\\overline{PB}') + '。求 ' + T('P') + ' 的所有可能坐標，並指出哪一個在線段 ' + T('\\overline{AB}') + ' 上。',
      a: T('x=' + Fr.tex(x1, false) + '\\ \\text{或}\\ x=' + Fr.tex(x2, false)) + '；在線段上的是 ' + T('x=' + Fr.tex(x1, false)) + '（' + T('\\overline{AB}') + ' 的 ' + T(m + ':1') + ' 內分點）',
      h: '$\\overline{PA}=' + m + '\\,\\overline{PB}$ 就是 $' + absLin(1, -a) + '=' + m + absLin(1, -b) + '$。內分點：$\\overline{AP}:\\overline{PB}=' + m + ':1$，$x=\\dfrac{1\\cdot(' + a + ')+' + m + '\\cdot' + parT(b) + '}{' + m + '+1}$；外分點在 $B$ 右側（離 $A$ 較遠），$x=\\dfrac{' + m + '\\cdot' + parT(b) + '-(' + a + ')}{' + m + '-1}$。', p: { a: a, b: b, m: m, v: 1, x1n: x1.n, x1d: x1.d, x2n: x2.n, x2d: x2.d } };
  };

  /* L3-10　恰有 k 個整數解 → 卡參數 t 的範圍 */
  L3.exactIntParam = function (r) {
    var v = r.int(0, 3), a = r.int(-5, 12), j = r.int(1, 4), c = r.int(1, 4), lo, hi, loInc, hiInc, k, ineq;
    if (v === 0) { k = 2 * j; lo = c + j - 1; hi = c + j; loInc = true; hiInc = false; ineq = c + '\\le' + absLin(1, -a) + '\\le t'; }        /* 每側恰 j 個 */
    else if (v === 1) { k = 2 * j + 1; lo = j; hi = j + 1; loInc = true; hiInc = false; ineq = absLin(1, -a) + '\\le t'; }
    else if (v === 2) { k = 2 * j + 1; lo = j; hi = j + 1; loInc = false; hiInc = true; ineq = absLin(1, -a) + '<t'; }
    else { k = 2 * j; lo = c + j; hi = c + j + 1; loInc = false; hiInc = true; ineq = c + '<' + absLin(1, -a) + '<t'; }
    var ansT = lo + (loInc ? '\\le ' : '<') + 't' + (hiInc ? '\\le ' : '<') + hi;
    var side = v === 0 ? '右側要含 $' + (a + c) + '$ 到 $' + (a + c + j - 1) + '$ 但不含 $' + (a + c + j) + '$' : v === 1 ? '右側要含 $' + (a + 1) + '$ 到 $' + (a + j) + '$ 但不含 $' + (a + j + 1) + '$' : v === 2 ? '右側要含 $' + (a + 1) + '$ 到 $' + (a + j) + '$（開區間，$' + (a + j + 1) + '$ 不能進來）' : '右側要含 $' + (a + c + 1) + '$ 到 $' + (a + c + j) + '$ 但不含 $' + (a + c + j + 1) + '$（兩端都是開的）';
    return { q: '若不等式 ' + T(ineq) + ' 恰有 ' + T(String(k)) + ' 個整數解，求 ' + T('t') + ' 的範圍。', a: T(ansT),
      h: '解集合關於 $x=' + a + '$ 對稱，整數解左右各半（' + (k % 2 ? '加上中間的 $x=' + a + '$' : '$x=' + a + '$ 本身不算') + '）：' + side + '，再把「$' + absLin(1, -a) + '$ 的上限 $t$」卡在兩個整數之間，注意端點能不能取。', p: { v: v, a: a, c: c, j: j, k: k, lo: lo, hi: hi, loInc: loInc, hiInc: hiInc } };
  };

  /* L3-11　|x−a|+|x−b| = k 解的個數：最小值 D=b−a 在整段取到 */
  L3.absSumEqCount = function (r) {
    var a = r.int(-8, 3), b = a + r.int(2, 12), D = b - a, v = r.int(0, 2), lhs = absLin(1, -a) + '+' + absLin(1, -b);
    if (v === 0) return { q: '關於 ' + T('x') + ' 的方程式 ' + T(lhs + '=k') + '，求：(1) 使方程式有解的最小 ' + T('k') + '；(2) 恰有兩個解時 ' + T('k') + ' 的範圍；(3) ' + T('k=' + D) + ' 時解的個數。',
      a: '(1) ' + T('k=' + D) + '　(2) ' + T('k>' + D) + '　(3) 無限多個（' + T(a + '\\le x\\le' + b) + ' 全部是解）',
      h: '$' + lhs + '$ 是到 $' + a + '$、$' + b + '$ 的距離和，圖形是「碗」：底部 $' + a + '\\le x\\le' + b + '$ 整段都等於 $' + D + '$，往兩側每走 1 就加 2。$k<' + D + '$ 無解、$k=' + D + '$ 無限多解、$k>' + D + '$ 恰兩解。', p: { v: 0, a: a, b: b, D: D } };
    if (v === 1) {
      var lo = r.int(1, D + 2), hi = lo + r.int(10, 60), cnt = hi >= D ? hi - Math.max(lo, D) + 1 : 0;
      return { q: '在 ' + T(lo + '\\le k\\le' + hi) + ' 的整數中，有幾個 ' + T('k') + ' 使方程式 ' + T(lhs + '=k') + ' 有解？', a: T(String(cnt)) + ' 個',
        h: '有解 $\\iff k\\ge' + D + '$（兩點距離）。在 $' + lo + '$ 到 $' + hi + '$ 的整數中，$\\ge' + D + '$ 的有 $' + hi + '-' + Math.max(lo, D) + '+1$ 個。', p: { v: 1, a: a, b: b, D: D, lo: lo, hi: hi, cnt: cnt } };
    }
    var K = D + r.pick([-2, -1, 0, 1, 2, 4, 6]), n = K < D ? 0 : K === D ? -1 : 2, sols = n === 2 ? [F(a + b - K, 2), F(a + b + K, 2)] : [];
    return { q: '方程式 ' + T(lhs + '=' + K) + ' 有幾個實數解？若是有限個，求出所有解。',
      a: n === 0 ? '無解（' + T(K + '<' + D) + '）' : n === -1 ? '無限多個解：' + T(a + '\\le x\\le' + b) : '恰 2 個解：' + T('x=' + Fr.tex(sols[0], false) + '\\ \\text{或}\\ x=' + Fr.tex(sols[1], false)),
      h: '距離和的最小值是兩點距離 $' + D + '$。$' + K + (K < D ? '<' : K === D ? '=' : '>') + D + '$ ⟹ ' + (n === 0 ? '碗底都到不了，無解。' : n === -1 ? '整段底部都是解。' : '兩側各一解：從兩點中點 $' + Fr.tex(F(a + b, 2), false) + '$ 往外各走 $\\dfrac{' + K + '}{2}$。'), p: { v: 2, a: a, b: b, D: D, K: K, n: n, sols: sols.map(function (f) { return [f.n, f.d]; }) } };
  };

  /* L3-12　連等式取 log（多選）：q²=pr ⟹ 2/b = 1/a + 1/c；r=pq ⟹ 1/c = 1/a + 1/b
     a,b,c 由共同值 k 決定、不能獨立給，所以題型是「選出正確的關係式」，每個選項用實際數值驗真偽 */
  var CHAIN_OPT = {
    0: [['ab+bc=2ac', function (a, b, c) { return a * b + b * c - 2 * a * c; }, true], ['\\dfrac1c=\\dfrac2b-\\dfrac1a', function (a, b, c) { return 1 / c - 2 / b + 1 / a; }, true], ['\\dfrac2b=\\dfrac1a+\\dfrac1c', function (a, b, c) { return 2 / b - 1 / a - 1 / c; }, true], ['b=\\dfrac{2ac}{a+c}', function (a, b, c) { return b - 2 * a * c / (a + c); }, true],
        ['ab+bc=ac', function (a, b, c) { return a * b + b * c - a * c; }, false], ['\\dfrac2c=\\dfrac2a+\\dfrac1b', function (a, b, c) { return 2 / c - 2 / a - 1 / b; }, false], ['b^2=ac', function (a, b, c) { return b * b - a * c; }, false], ['b=\\dfrac{a+c}{2}', function (a, b, c) { return b - (a + c) / 2; }, false], ['\\dfrac1b=\\dfrac1a+\\dfrac1c', function (a, b, c) { return 1 / b - 1 / a - 1 / c; }, false]],
    1: [['\\dfrac1c=\\dfrac1a+\\dfrac1b', function (a, b, c) { return 1 / c - 1 / a - 1 / b; }, true], ['ab=ac+bc', function (a, b, c) { return a * b - a * c - b * c; }, true], ['c=\\dfrac{ab}{a+b}', function (a, b, c) { return c - a * b / (a + b); }, true], ['\\dfrac1a=\\dfrac1c-\\dfrac1b', function (a, b, c) { return 1 / a - 1 / c + 1 / b; }, true],
        ['c=a+b', function (a, b, c) { return c - a - b; }, false], ['\\dfrac1a=\\dfrac1b+\\dfrac1c', function (a, b, c) { return 1 / a - 1 / b - 1 / c; }, false], ['c^2=ab', function (a, b, c) { return c * c - a * b; }, false], ['c=\\dfrac{a+b}{2}', function (a, b, c) { return c - (a + b) / 2; }, false], ['ab=2ac+2bc', function (a, b, c) { return a * b - 2 * a * c - 2 * b * c; }, false]]
  };
  L3.chainEqLog = function (r) {
    var fam = r.int(0, 1), u = r.pick([2, 3, 5, 7]), w = r.pick([2, 3, 5, 7]); while (w === u) w = r.pick([2, 3, 5, 7]);
    var p, q, rr;
    if (fam === 0) { p = u * u; q = u * w; rr = w * w; } else { if (u > w) { var tmp = u; u = w; w = tmp; } p = u; q = w; rr = u * w; }
    /* 取 k = p（a = 1）算出 b、c 的真實值，逐一驗證選項 */
    var a = 1, b = Math.log(p) / Math.log(q), c = Math.log(p) / Math.log(rr), pool = CHAIN_OPT[fam];
    var trues = r.shuffle(pool.filter(function (o) { return o[2] && Math.abs(o[1](a, b, c)) < 1e-9; })).slice(0, r.int(2, 3));
    var falses = r.shuffle(pool.filter(function (o) { return !o[2] && Math.abs(o[1](a, b, c)) > 1e-6; })).slice(0, 5 - trues.length);
    var opts = r.shuffle(trues.concat(falses)), ans = [];
    opts.forEach(function (o, i) { if (o[2]) ans.push(i + 1); });
    var chain = p + '^a=' + q + '^b=' + rr + '^c';
    var why = fam === 0 ? '因為 $' + q + '^2=' + p + '\\times' + rr + '$，$\\log' + q + '=\\dfrac{\\log' + p + '+\\log' + rr + '}{2}$，所以 $\\dfrac1b=\\dfrac12\\left(\\dfrac1a+\\dfrac1c\\right)$' : '因為 $' + rr + '=' + p + '\\times' + q + '$，$\\log' + rr + '=\\log' + p + '+\\log' + q + '$，所以 $\\dfrac1c=\\dfrac1a+\\dfrac1b$';
    return { q: '設 ' + T('a,b,c') + ' 為正數且 ' + T(chain) + '，選出正確的選項：<br>' + opts.map(function (o, i) { return '(' + (i + 1) + ') ' + T(o[0]); }).join('　'),
      a: '(' + ans.join(')(') + ')', h: '令共同值為 $k$，取 $\\log$：$a\\log' + p + '=b\\log' + q + '=c\\log' + rr + '=\\log k$ ⟹ $\\dfrac1a=\\dfrac{\\log' + p + '}{\\log k}$、$\\dfrac1b=\\dfrac{\\log' + q + '}{\\log k}$、$\\dfrac1c=\\dfrac{\\log' + rr + '}{\\log k}$；' + why + '，再同乘 $abc$ 或移項對每個選項。',
      p: { fam: fam, p: p, q: q, r: rr, opts: opts.map(function (o) { return o[0]; }), ans: ans } };
  };

  /* L3-13　b^{2x}+b^{−2x} 與 b^x+b^{−x} 同時出現：令 t = b^x+b^{−x} ≥ 2 */
  L3.expSymmEq = function (r) {
    var base = r.pick([10, 10, 2, 3]), u, xT;
    if (base === 10) { u = r.pick([2, 5, 20, 50, 4, 25]); xT = { 2: '\\log2', 5: '1-\\log2', 20: '1+\\log2', 50: '2-\\log2', 4: '2\\log2', 25: '2-2\\log2' }[u]; }
    else { var e = r.int(1, 3); u = Math.pow(base, e); xT = String(e); }
    var t0 = F(u * u + 1, u), t1 = r.pick([F(0), F(1), F(-1), F(1, 2), F(-2), F(3, 2)]), mul = r.pick([1, 1, 2]);
    var A = u * t1.d * mul;                                                     /* 清分母（u 與 t1 的分母都要除得掉）*/
    var sum = Fr.add(t0, t1), prod = Fr.mul(t0, t1);
    var B = Fr.mul(F(A), sum), Cc = Fr.add(Fr.mul(F(A), prod), F(2 * A));      /* A(t²−2) − B t + C = 0 */
    B = B.n; Cc = Cc.n;                                                         /* 已是整數 */
    var sq = base * base, big = sq + '^{x}+' + sq + '^{-x}', small = base + '^{x}+' + base + '^{-x}';
    var eqT = (A === 1 ? '' : A) + '\\left(' + big + '\\right)' + (B === 0 ? '' : (B > 0 ? '-' : '+') + (Math.abs(B) === 1 ? '' : Math.abs(B)) + '\\left(' + small + '\\right)') + (Cc === 0 ? '' : signed(Cc)) + '=0';
    return { q: '解方程式 ' + T(eqT) + '。' + (base === 10 ? '（答案以 $\\log2$ 表示）' : ''),
      a: T('x=' + xT + '\\ \\text{或}\\ x=' + (/[+-]/.test(xT) ? '-(' + xT + ')' : '-' + xT)),
      h: '令 $t=' + small + '$（$t\\ge2$），則 $' + big + '=t^2-2$，方程式變成 $' + A + 't^2-' + coefTex(B, 't') + (Cc - 2 * A === 0 ? '' : signed(Cc - 2 * A)) + '=0$，解得 $t=' + Fr.tex(t0, false) + '$（另一根 $' + Fr.tex(t1, false) + '<2$ 不合）。再令 $u=' + base + '^x>0$：$u+\\dfrac1u=' + Fr.tex(t0, false) + '$ ⟹ $u=' + u + '$ 或 $\\dfrac1{' + u + '}$。',
      p: { base: base, u: u, t1n: t1.n, t1d: t1.d, A: A, B: B, C: Cc, xT: xT } };
  };

  /* L3-14　半衰期：(1/2)^n < p% 取 log */
  L3.halfLife = function (r) {
    var base = r.pick([2, 2, 2, 3]), H = r.pick([5, 10, 20, 30, 50, 100, 25, 40]), v = r.int(0, 1);
    var P = r.pick([1, 2, 5, 10, 20, 0.1]), Lmap = { 1: 2, 2: 1.699, 5: 1.301, 10: 1, 20: 0.699, 0.1: 3 }, L = Lmap[P];
    var lg = base === 2 ? 0.3010 : 0.4771, ratio = L / lg, n = Math.floor(ratio) + 1;
    var pT = P === 0.1 ? '0.1' : String(P), given = base === 2 ? '\\log2\\approx0.3010' : '\\log3\\approx0.4771';
    var how = base === 2 ? '每 $' + H + '$ 年衰變為原來的一半' : '每 $' + H + '$ 年衰變為原來的 $\\dfrac13$';
    var q = v === 0 ? '某放射性物質' + how + '。至少經過幾年，剩餘量會少於原來的 ' + T(pT + '\\%') + '？（' + T(given) + '）'
      : '某放射性物質' + how + '。至少經過幾年，衰變掉的量會超過原來的 ' + T((100 - P) + '\\%') + '（即剩下不到 ' + T(pT + '\\%') + '）？（' + T(given) + '）';
    return { q: q, a: T(String(n)) + ' 個週期，即 ' + T(String(n * H)) + ' 年',
      h: '經 $n$ 個週期剩 $\\left(\\dfrac1' + base + '\\right)^n$，要 $<\\dfrac{' + pT + '}{100}$；兩邊取 $\\log$：$-n\\log' + base + '<-' + L + '$ ⟹ $n>\\dfrac{' + L + '}{' + lg + '}\\approx' + ratio.toFixed(2) + '$，取整數 $n=' + n + '$，再乘 $' + H + '$ 年。',
      p: { base: base, H: H, P: P, L: L, n: n, v: v } };
  };

  /* L3-15　計算機按 log：log 值落在區間 ⟺ 原數落在 10 的次方之間；按兩次套兩層 */
  L3.logCalcCount = function (r) {
    var mode = r.int(0, 3), q, ans, cnt;
    if (mode === 0) { var a = r.int(0, 4), b = a + r.int(1, 3); cnt = Math.pow(10, b) - Math.pow(10, a) - 1;
      q = '按出正整數 ' + T('M') + ' 再按一次 $\\log$ 鍵，所得數值介於 ' + T(String(a)) + ' 到 ' + T(String(b)) + ' 之間（不含兩端），這樣的 ' + T('M') + ' 有幾個？'; ans = T(String(cnt)) + ' 個';
      return { q: q, a: ans, h: '$' + a + '<\\log M<' + b + '\\iff10^{' + a + '}<M<10^{' + b + '}$，開區間內的整數有 $10^{' + b + '}-10^{' + a + '}-1$ 個。', p: { mode: 0, a: a, b: b, cnt: String(cnt) } }; }
    if (mode === 1) { var k = r.int(0, 6); cnt = 9 * Math.pow(10, k);
      q = '按出正整數 ' + T('M') + ' 再按一次 $\\log$ 鍵，所得數值的整數部分為 ' + T(String(k)) + '，這樣的 ' + T('M') + ' 有幾個？'; ans = T(String(cnt)) + ' 個';
      return { q: q, a: ans, h: '整數部分為 $' + k + '$ ⟺ $' + k + '\\le\\log M<' + (k + 1) + '\\iff10^{' + k + '}\\le M<10^{' + (k + 1) + '}$，就是所有 $' + (k + 1) + '$ 位數，有 $9\\times10^{' + k + '}$ 個。', p: { mode: 1, k: k, cnt: String(cnt) } }; }
    if (mode === 2) { var kind = r.int(0, 3);
      if (kind === 3) return { q: '按出正整數 ' + T('N') + ' 再按兩次 $\\log$ 鍵，所得數值的整數部分為 ' + T('1') + '，這樣的 ' + T('N') + ' 有幾個？', a: T('10^{100}-10^{10}') + ' 個', h: '整數部分為 $1$ ⟺ $1\\le\\log(\\log N)<2\\iff10\\le\\log N<100\\iff10^{10}\\le N<10^{100}$，有 $10^{100}-10^{10}$ 個。', p: { mode: 2, kind: 3, cnt: '10^{100}-10^{10}' } };
      if (kind === 0) return { q: '按出正整數 ' + T('N') + ' 再按兩次 $\\log$ 鍵，所得數值介於 ' + T('0') + ' 到 ' + T('1') + ' 之間（不含），這樣的 ' + T('N') + ' 有幾個？', a: T('10^{10}-11') + ' 個', h: '$0<\\log(\\log N)<1\\iff1<\\log N<10\\iff10<N<10^{10}$，開區間內的整數有 $10^{10}-10-1$ 個。', p: { mode: 2, kind: 0, cnt: '10^{10}-11' } };
      if (kind === 1) return { q: '按出正整數 ' + T('K') + ' 再按兩次 $\\log$ 鍵，所得數值介於 ' + T('-1') + ' 到 ' + T('0') + ' 之間（不含），這樣的 ' + T('K') + ' 有幾個？', a: T('8') + ' 個（' + T('K=2,3,\\dots,9') + '）', h: '$-1<\\log(\\log K)<0\\iff0.1<\\log K<1\\iff10^{0.1}<K<10$，而 $10^{0.1}\\approx1.26$，所以 $K=2$ 到 $9$。', p: { mode: 2, kind: 1, cnt: '8' } };
      return { q: '按出正整數 ' + T('N') + ' 再按兩次 $\\log$ 鍵，所得數值的整數部分為 ' + T('0') + '，這樣的 ' + T('N') + ' 有幾個？', a: T('10^{10}-10') + ' 個', h: '整數部分為 $0$ ⟺ $0\\le\\log(\\log N)<1\\iff1\\le\\log N<10\\iff10\\le N<10^{10}$，有 $10^{10}-10$ 個。', p: { mode: 2, kind: 2, cnt: '10^{10}-10' } }; }
    var n = r.pick([100, 1000, 400, 25, 5000, 2, 50, 10000, 300, 7, 80, 2024, 65000, 999]), lv = Math.log10(n), ip = Math.floor(lv), two = lv > 1 ? Math.floor(Math.log10(lv)) : null;
    q = '按出 ' + T(String(n)) + ' 再按一次 $\\log$ 鍵，所得數值的整數部分是多少？' + (two !== null ? '再按一次 $\\log$ 鍵呢？' : '');
    ans = T(String(ip)) + (two !== null ? '；再按一次得 ' + T(String(two)) : '');
    return { q: q, a: ans, h: '$\\log' + n + '$ 落在 $' + ip + '$ 與 $' + (ip + 1) + '$ 之間（$10^{' + ip + '}\\le' + n + '<10^{' + (ip + 1) + '}$）' + (two !== null ? '；再取一次 $\\log$：$\\log' + n + '\\approx' + lv.toFixed(2) + '$ 在 $10^{' + two + '}$ 與 $10^{' + (two + 1) + '}$ 之間。' : '。'), p: { mode: 3, n: n, ip: ip, two: two } };
  };

  var META_L3 = [['farDigit', '有限＋循環小數的第 N 位'], ['sqrtMixedDigit', '帶分數開根號後的第 N 位'], ['coefCompareLin', '展開後係數比較解 (x,y)'], ['doubleRootCoef', '雙重根號＋有理係數比較'], ['surdDiffOrder', '根式相減比大小（有理化）'], ['symmFromQuad', '二次方程 ÷ x 得對稱式'], ['amgmLinProduct', '乘積定值求線性式最小'], ['avgCostMin', '平均成本最低（算幾）'], ['absRatioPoints', '|x−a|=m|x−b| 的內外分點'], ['exactIntParam', '恰有 k 個整數解求參數'], ['absSumEqCount', '|x−a|+|x−b|=k 解的個數'], ['chainEqLog', '連等式取 log'], ['expSymmEq', 'b^{2x}+b^{−2x} 換元解方程'], ['halfLife', '半衰期／衰變取 log'], ['logCalcCount', '按 log 鍵落在區間的個數']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'farDigit', 'L3-2': 'sqrtMixedDigit', 'L3-3': 'coefCompareLin', 'L3-4': 'doubleRootCoef', 'L3-5': 'surdDiffOrder', 'L3-6': 'symmFromQuad', 'L3-7': 'amgmLinProduct', 'L3-8': 'avgCostMin', 'L3-9': 'absRatioPoints', 'L3-10': 'exactIntParam', 'L3-11': 'absSumEqCount', 'L3-12': 'chainEqLog', 'L3-13': 'expSymmEq', 'L3-14': 'halfLife', 'L3-15': 'logCalcCount' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：全部是國中內容——質因數分解、分數四則、平方根估計、一元一次不等式、乘法公式
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  L0.primeFactor = function (r) {
    var e2 = r.int(0, 3), e3 = r.int(0, 2), e5 = r.int(0, 1), e7 = r.int(0, 1);
    if (e2 + e3 + e5 + e7 < 2) e2 = 2;
    var n = Math.pow(2, e2) * Math.pow(3, e3) * Math.pow(5, e5) * Math.pow(7, e7);
    var parts = []; [[2, e2], [3, e3], [5, e5], [7, e7]].forEach(function (pe) { if (pe[1]) parts.push(pe[1] > 1 ? pe[0] + '^{' + pe[1] + '}' : String(pe[0])); });
    return { q: '將 ' + T(String(n)) + ' 做質因數分解。', a: T(n + '=' + parts.join('\\times')), h: '從最小的質數 $2$ 開始一直除：$' + n + '\\div2=' + (n % 2 === 0 ? n / 2 : '\\text{除不盡}') + '$……除不盡就換下一個質數 $3,5,7$。', p: { n: n, e: [e2, e3, e5, e7] } };
  };
  L0.fracOps = function (r) {
    var b = r.pick([2, 3, 4, 5, 6, 8]), d = r.pick([2, 3, 4, 5, 6, 9]), a = r.int(1, 7), c = r.int(1, 7), op = r.pick(['+', '-', '\\times', '\\div']);
    var x = F(a, b), y = F(c, d), res = op === '+' ? Fr.add(x, y) : op === '-' ? Fr.sub(x, y) : op === '\\times' ? Fr.mul(x, y) : Fr.div(x, y);
    var L = b * d / gcd(b, d);
    var hint = (op === '+' || op === '-') ? '先通分：分母 $' + b + '$、$' + d + '$ 的最小公倍數是 $' + L + '$，化成 $\\dfrac{' + a * (L / b) + '}{' + L + '}' + op + '\\dfrac{' + c * (L / d) + '}{' + L + '}$。' : op === '\\times' ? '分子乘分子、分母乘分母：$\\dfrac{' + a + '\\times' + c + '}{' + b + '\\times' + d + '}$，再約分。' : '除以一個分數 ＝ 乘它的倒數：$\\dfrac{' + a + '}{' + b + '}\\times\\dfrac{' + d + '}{' + c + '}$。';
    return { q: '計算 ' + T('\\dfrac{' + a + '}{' + b + '}' + op + '\\dfrac{' + c + '}{' + d + '}') + '，以最簡分數表示。', a: T(Fr.tex(res)), h: hint, p: { a: a, b: b, c: c, d: d, op: op, n: res.n, dd: res.d } };
  };
  L0.sqrtBetween = function (r) {
    var v = r.int(0, 2);
    if (v === 0) { var s = r.int(2, 20), n0 = s * s; return { q: '求 ' + T('\\sqrt{' + n0 + '}') + '。', a: T(String(s)), h: '找哪個整數的平方是 $' + n0 + '$：$' + s + '\\times' + s + '=' + n0 + '$。', p: { v: 0, n: n0, k: s } }; }
    var n = r.int(2, 200); while (isSquare(n)) n = r.int(2, 200);
    var k = isqrt(n);
    if (v === 1) return { q: T('\\sqrt{' + n + '}') + ' 介於哪兩個連續整數之間？', a: T(k + '<\\sqrt{' + n + '}<' + (k + 1)), h: '找夾住 $' + n + '$ 的兩個完全平方數：$' + k * k + '<' + n + '<' + (k + 1) * (k + 1) + '$，再同時開根號。', p: { v: 1, n: n, k: k } };
    return { q: '不用計算機，' + T('\\sqrt{' + n + '}') + ' 的整數部分是多少？', a: T(String(k)), h: '$' + k + '^2=' + k * k + '\\le' + n + '<' + (k + 1) * (k + 1) + '=' + (k + 1) + '^2$，所以整數部分是 $' + k + '$。', p: { v: 2, n: n, k: k } };
  };
  L0.linIneq = function (r) {
    var a = r.pick([2, 3, 4, 5, -2, -3, -4]), b = r.int(-9, 9), c = r.int(-9, 9), op = r.pick(['<', '>', '\\le', '\\ge']);
    var x = F(c - b, a), flip = a < 0, ops = { '<': '>', '>': '<', '\\le': '\\ge', '\\ge': '\\le' }, resOp = flip ? ops[op] : op;
    return { q: '解不等式 ' + T(linTex(a, b) + op + c) + '。', a: T('x' + resOp + Fr.tex(x, false)),
      h: '先移項：$' + coefTex(a, 'x') + op + (c - b) + '$，再除以 $' + a + '$' + (flip ? '——除以負數，不等號要<b>反向</b>' : '（正數，不等號方向不變）') + '。', p: { a: a, b: b, c: c, op: op, xn: x.n, xd: x.d, resOp: resOp } };
  };
  L0.mulFormula = function (r) {
    var kind = r.int(0, 2), a = r.int(1, 9), b = r.int(1, 9), sa = r.sign(), sb = r.sign();
    if (kind === 0) return { q: '展開 ' + T('(x' + signed(sa * a) + ')^2') + '。', a: T('x^2' + signed(2 * sa * a) + 'x+' + a * a), h: '$(x+m)^2=x^2+2mx+m^2$，這裡 $m=' + sa * a + '$：中間項 $2\\times(' + sa * a + ')x$，常數項 $(' + sa * a + ')^2$。', p: { kind: 0, m: sa * a } };
    if (kind === 1) return { q: '展開 ' + T('(x+' + a + ')(x-' + a + ')') + '。', a: T('x^2-' + a * a), h: '平方差：$(x+m)(x-m)=x^2-m^2$，$m=' + a + '$。', p: { kind: 1, m: a } };
    var m = sa * a, n = sb * b, s = m + n, pp = m * n;
    return { q: '展開 ' + T('(x' + signed(m) + ')(x' + signed(n) + ')') + '。', a: T('x^2' + (s === 0 ? '' : (s > 0 ? '+' : '-') + coefTex(Math.abs(s), 'x')) + signed(pp)), h: '$(x+m)(x+n)=x^2+(m+n)x+mn$：$m+n=' + s + '$、$mn=' + pp + '$。', p: { kind: 2, m: m, n: n } };
  };
  var META_L0 = [['primeFactor', '質因數分解'], ['fracOps', '分數四則與通分'], ['sqrtBetween', '平方根與完全平方數'], ['linIneq', '一元一次不等式'], ['mulFormula', '乘法公式展開']];
  /* 先備題型 → 該去哪裡複習（全部是國中內容，沒有本系統的前章可連） */
  var PREREQ = { primeFactor: { txt: '質因數分解（國中）——判斷分母只含 2、5、化簡根號都靠它', link: null }, fracOps: { txt: '分數的四則與通分（國中）——循環小數化分數之後還要會算', link: null }, sqrtBetween: { txt: '平方根的估計與完全平方數（國中）——整數部分、小數部分的基礎', link: null }, linIneq: { txt: '一元一次不等式（國中）——絕對值不等式拆開後就是它，除以負數要反向', link: null }, mulFormula: { txt: '乘法公式（國中）——有理化、雙重根號、對稱式全部用到', link: null } };

  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  var CONTRAST = {
    'L1.rational': { f: function (p) { return p.rat; }, why: '長得像的兩個數，一個能寫成「整數 ÷ 整數」一個不能：判準只看「能不能化成分數」，不看有沒有根號或小數點。' },
    'L1.repPure': { f: function (p) { return p.rep.length; }, why: '循環節長度決定分母有幾個 9：一位循環節分母 9、兩位分母 99。' },
    'L1.repMixed': { f: function (p) { return p.rep.length; }, why: '不循環的位數決定 0 的個數、循環節長度決定 9 的個數，兩題差的是 9 的個數。' },
    'L1.fracKind': { f: function (p) { return p.fin; }, why: '分母的質因數只有 2、5 才是有限小數；多了一個別的質因數就一定循環。' },
    'L1.divPoint': { f: function (p) { return p.m > p.n; }, keep: ['a', 'b'], why: '同一條線段，比例前後對調，分點就從靠近 $A$ 變成靠近 $B$——交叉配時權重要配給「另一端」。' },
    'L1.ratConj': { f: function (p) { return p.s; }, keep: ['k'], why: '分母是 $b+\\sqrt k$ 就乘 $b-\\sqrt k$，是 $b-\\sqrt k$ 就乘 $b+\\sqrt k$：共軛的符號相反，分母都變成 $b^2-k$。' },
    'L1.doubleRoot': { f: function (p) { return p.s; }, why: '同樣先找「和與積」，中間是加號就是 $\\sqrt q+\\sqrt p$、減號就是 $\\sqrt q-\\sqrt p$（大的在前，結果才是正的）。' },
    'L1.amgm': { f: function (p) { return p.v === 2; }, why: '「$x+\\frac kx$ 的最小值」與「$xy$ 固定求 $x+y$ 最小」是同一條算幾不等式，只是兩個正數換了名字。' },
    'L1.absSimp': { f: function (p) { return p.v; }, why: '脫絕對值前先判正負：條件不同，哪一項要變號就不同。' },
    'L1.absIneq': { f: function (p) { return p.less; }, keep: ['a', 'b'], why: '同樣的中心與距離：小於是「夾在中間」，大於是「兩邊外面」。' },
    'L1.expLaw': { f: function (p) { return p.v; }, why: '相乘是指數相加、次方的次方是指數相乘、根號是分數指數——三條指數律各管一種形狀。' },
    'L1.sciNot': { f: function (p) { return p.e > 0; }, why: '大數的小數點往左移、指數為正；小於 1 的數往右移、指數為負。移動的位數就是指數的絕對值。' },
    'L1.logBasic': { f: function (p) { return p.v; }, why: '$\\log$ 問的永遠是「$10$ 的幾次方」：$10^k$ 直接讀指數、乘積用 $\\log a+\\log b$ 拆開。' },
    'L2.coefCompare': { f: function (p) { return p.s; }, keep: ['k', 'b'], why: '分母的共軛符號相反，有理化後無理部分的正負跟著反，比較係數時 $b$ 的正負就不同。' },
    'L2.intFracOp': { f: function (p) { return p.v; }, keep: ['n'], why: '同一組 $a,b$，問法不同：$\\frac1b$ 要有理化，$ab+b^2$ 要提出 $b$，$b^2+2ab$ 是平方差。' },
    'L2.doubleRoot2': { f: function (p) { return p.s; }, why: '先把 $\\sqrt{4pq}$ 寫成 $2\\sqrt{pq}$，之後與直接拆的雙重根號一樣：加號和、減號差。' },
    'L2.symm': { f: function (p) { return p.which; }, why: '同一個 $x+\\frac1x$，二次用「平方減 2」、三次用「立方減 3 倍」、四次再套一次平方減 2。' },
    'L2.amgmCond': { f: function (p) { return p.v; }, why: '條件式與目標式的角色互換：和固定求積最大、積固定求和最小，都是同一條算幾不等式。' },
    'L2.absIneq2': { f: function (p) { return p.v; }, why: '夾層型拆成兩段區間、雙層絕對值由外往內脫、兩邊都有絕對值就平方——三種形狀三種招。' },
    'L2.absParam': { f: function (p) { return p.a > 0; }, why: '$a$ 的正負不影響中心 $-\\frac ba$ 與半寬 $\\frac{c}{|a|}$ 的公式，但反推 $b$ 時符號跟著變。' },
    'L2.expEq': { f: function (p) { return p.form; }, keep: ['base', 'e1', 'e2'], why: '$4^x$ 與 $2^{2x}$ 是同一個數：都令 $t=2^x$，$4^x=t^2$。' },
    'L2.expSymm': { f: function (p) { return p.v; }, why: '已知和求平方和是「平方減 2」，已知差求和要「平方加 4 再開根號」，開根號時要看正負。' },
    'L2.compound': { f: function (p) { return p.v; }, why: '複利成長是 $(1+r)^n>k$，折舊是 $(1-r)^n<\\frac1k$：取 $\\log$ 後一個除以正數、一個除以負數（不等號反向）。' },
    'L3.sqrtMixedDigit': { f: function (p) { return p.sgn; }, keep: ['m'], why: '$m^2+2$ 給 $m+\\frac1m$、$m^2-2$ 給 $m-\\frac1m$：整數部分差 1，循環節也不同（$\\frac1m$ 對 $\\frac{m-1}{m}$）。' },
    'L3.symmFromQuad': { f: function (p) { return p.fam; }, why: '常數項 $-1$ 除以 $x$ 後得 $x-\\frac1x$，常數項 $+1$ 得 $x+\\frac1x$；對稱式公式的正負號跟著換。' },
    'L3.absRatioPoints': { f: function (p) { return p.v; }, keep: ['m'], why: '同一種方程式，一個問所有解、一個問線段上的那一個：內分點在兩點之間，外分點在較近那一端的外側。' },
    'L3.exactIntParam': { f: function (p) { return p.v; }, why: '$\\le$ 與 $<$ 只差端點：閉區間卡 $t$ 時左端含、右端不含；開區間則相反。' },
    'L3.absSumEqCount': { f: function (p) { return p.v; }, keep: ['a', 'b'], why: '同一個碗形圖：問最小 $k$、問幾個整數 $k$ 有解、問某個 $k$ 的解，都從「底部 $=b-a$」出發。' },
    'L3.chainEqLog': { f: function (p) { return p.fam; }, why: '$q^2=pr$ 給 $\\frac2b=\\frac1a+\\frac1c$；$r=pq$ 給 $\\frac1c=\\frac1a+\\frac1b$——取 $\\log$ 後看三個數的乘法關係。' },
    'L3.expSymmEq': { f: function (p) { return p.base === 10; }, why: '底數 $10$ 的答案要寫成 $\\log2$ 的組合；底數 $2$、$3$ 時 $u$ 是整數次方，$x$ 直接是整數。' },
    'L3.halfLife': { f: function (p) { return p.base; }, keep: ['P'], why: '每期剩一半用 $\\log2$、剩三分之一用 $\\log3$：分母不同，所需週期數就不同。' },
    'L3.logCalcCount': { f: function (p) { return p.mode; }, why: '按一次 $\\log$ 卡 $10^a<M<10^b$；按兩次要先把「介於」翻成 $\\log N$ 的範圍，再翻成 $N$ 的範圍。' }
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, simpSqrt: simpSqrt, repeatingToFrac: repeatingToFrac, fracToRepeating: fracToRepeating } };
}));
