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
      function () { var a = r.int(1, 9); return { tex: '\\sqrt{' + a + '}\\times\\sqrt{' + a + '}', rat: true, why: '等於 ' + T(String(a)) + '，兩個無理數的乘積可以是有理數' }; },
      function () { var a = r.pick([2, 3, 5]); return { tex: '(\\sqrt{' + a + '}+1)(\\sqrt{' + a + '}-1)', rat: true, why: '等於 ' + T(String(a - 1)) + '，平方差把根號消掉了' }; },
      function () { var a = r.pick([2, 3, 5]); return { tex: '\\sqrt{' + a + '}+1', rat: false, why: '無理數加有理數還是無理數' }; },
      function () { var a = r.int(2, 9); return { tex: '0.' + a + a + a + '\\ldots\\text{（不循環、無規律）}', rat: false, why: '無限不循環小數就是無理數' }; }
    ];
    var it = r.pick(pool)();
    return { q: '判斷 ' + T(it.tex) + ' 是<b>有理數</b>還是<b>無理數</b>。', a: (it.rat ? '<b>有理數</b>' : '<b>無理數</b>') + '　（' + it.why + '）',
             h: '有理數＝可以寫成分數；整數、有限小數、循環小數、能開盡的根號都算。', p: { tex: it.tex, rat: it.rat } };
  };

  /* 1-2 純循環小數化分數 */
  L1.repPure = function (r) {
    var m = r.int(1, 2), rep = m === 1 ? String(r.int(1, 9)) : String(r.int(10, 98)).replace(/9$/, '8');
    if (m === 2 && rep[0] === rep[1]) rep = rep[0] + String((parseInt(rep[1], 10) + 1) % 10);
    var fr = repeatingToFrac(0, '', rep);
    return { q: '將循環小數 ' + T(repTex(0, '', rep)) + ' 化為最簡分數。', a: T(Fr.tex(fr)),
             h: '純循環：循環節當分子，分母寫幾個 9 就是循環節的長度，再約分。', p: { pre: '', rep: rep, n: fr.n, d: fr.d } };
  };

  /* 1-3 混循環小數化分數 */
  L1.repMixed = function (r) {
    var pre = String(r.int(1, 9)), rep = String(r.int(1, 9));
    if (r() < 0.4) rep = String(r.int(10, 99));
    if (rep.length === 2 && rep[0] === rep[1]) rep = rep[0] + String((parseInt(rep[1], 10) + 3) % 10);
    var fr = repeatingToFrac(0, pre, rep);
    return { q: '將循環小數 ' + T(repTex(0, pre, rep)) + ' 化為最簡分數。', a: T(Fr.tex(fr)),
             h: '混循環：分子＝「全部數字」－「不循環的部分」；分母＝幾個 9（循環節長度）後面接幾個 0（不循環長度）。',
             p: { pre: pre, rep: rep, n: fr.n, d: fr.d } };
  };

  /* 1-4 分數化小數：有限還是循環？ */
  L1.fracKind = function (r) {
    var d = r.pick([4, 5, 8, 16, 20, 25, 40, 6, 7, 9, 11, 12, 14, 15, 18, 21, 22, 30]);
    var n = r.int(1, d - 1); if (gcd(n, d) !== 1) n = 1;
    var t = d; while (t % 2 === 0) t /= 2; while (t % 5 === 0) t /= 5;
    var fin = t === 1, ex = fracToRepeating(n, d);
    var tex = fin ? '0.' + ex.pre : repTex(0, ex.pre, ex.rep);
    return { q: T('\\dfrac{' + n + '}{' + d + '}') + ' 化成小數是<b>有限小數</b>還是<b>循環小數</b>？並寫出它。',
             a: (fin ? '有限小數' : '循環小數') + '：' + T(tex),
             h: '最簡分數的分母若只含質因數 2 和 5 ⟹ 有限小數；否則一定循環。', p: { n: n, d: d, fin: fin } };
  };

  /* 1-5 數線上的內分點 */
  L1.divPoint = function (r) {
    var a = r.int(-9, 5), b = a + r.int(2, 12), m = r.int(1, 5), n = r.int(1, 5), g = gcd(m, n); m /= g; n /= g;
    var p = Fr.add(F(a), Fr.mul(F(b - a), F(m, m + n)));   /* AP:PB = m:n ⟹ P = A + m/(m+n)(B-A) */
    return { q: '數線上 ' + T('A(' + a + ')') + '、' + T('B(' + b + ')') + '，點 ' + T('P') + ' 在線段 ' + T('\\overline{AB}') + ' 上且 ' + T('\\overline{AP}:\\overline{PB}=' + m + ':' + n) + '，求 ' + T('P') + ' 的坐標。',
             a: T('P\\left(' + Fr.tex(p) + '\\right)'),
             h: '分點公式「交叉配」：$P=\\dfrac{n\\cdot a+m\\cdot b}{m+n}$——靠近哪一端，那一端的權重就大。', p: { a: a, b: b, m: m, n: n, pn: p.n, pd: p.d } };
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
             h: '每一項先化簡成 $c\\sqrt{' + rr + '}$，再把係數加減。', p: { r: rr, cs: [c1, s2 * c2, s3 * c3], total: total } };
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
    var n = r.pick([2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30]);
    var k = isqrt(n);
    return { q: '設 ' + T('\\sqrt{' + n + '}') + ' 的整數部分為 ' + T('a') + '、小數部分為 ' + T('b') + '，求 ' + T('a') + ' 與 ' + T('b') + '。',
             a: T('a=' + k + ',\\ b=\\sqrt{' + n + '}-' + k),
             h: '找夾住 ' + n + ' 的兩個完全平方數：$' + k * k + '<' + n + '<' + (k + 1) * (k + 1) + '$，小數部分 = 原數 − 整數部分。', p: { n: n, k: k } };
  };

  /* 2-7 算幾不等式直接型 */
  L1.amgm = function (r) {
    var k = r.pick([1, 4, 9, 16, 25, 36]), c = r.pick([1, 1, 2, 3]);
    /* cx + k/x（x>0）最小值 2√(ck)，取 ck 為平方數 */
    var ck = c * k; if (!isSquare(ck)) { c = 1; ck = k; }
    var minv = 2 * isqrt(ck), xe = F(isqrt(ck), c);      /* cx = k/x ⟹ x = √(k/c) */
    xe = F(isqrt(k * c), c);
    return { q: '設 ' + T('x>0') + '，求 ' + T(coefTex(c, 'x') + '+\\dfrac{' + k + '}{x}') + ' 的最小值，並求此時的 ' + T('x') + '。',
             a: '最小值 ' + T(String(minv)) + '，此時 ' + T('x=' + Fr.tex(xe)),
             h: '兩正數相加 $\\ge2\\sqrt{\\text{乘積}}$，乘積是 $' + ck + '$；等號在兩項相等時。', p: { c: c, k: k, min: minv, xn: xe.n, xd: xe.d } };
  };

  /* 3-1 去絕對值（已知大小） */
  L1.absSimp = function (r) {
    var a = r.int(2, 9), b = a + r.int(1, 8);       /* 用具體無理數大小：√a vs b? 改用 a<b 的變數 */
    var k = r.int(1, 5);
    /* 已知 a<b：|a-b| + |b-a+k| = (b-a) + (b-a+k) ；或 |a-b-k| - |b-a| = (b-a+k)-(b-a)=k */
    var v = r.int(0, 1);
    if (v === 0) return { q: '已知 ' + T('a<b') + '，化簡 ' + T('|a-b|+|b-a+' + k + '|') + '。', a: T('2b-2a+' + k), h: '$a<b$ ⟹ $a-b<0$，$b-a>0$，先判正負再脫括號。', p: { v: 0, k: k } };
    return { q: '已知 ' + T('a<b') + '，化簡 ' + T('|a-b-' + k + '|-|b-a|') + '。', a: T(String(k)), h: '$a-b-' + k + '<0$ ⟹ 絕對值 $=b-a+' + k + '$。', p: { v: 1, k: k } };
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
             h: less ? '$|\\,\\cdot\\,|<b$ 是「夾在中間」：$-b<\\cdot<b$。' : '$|\\,\\cdot\\,|>b$ 是「兩邊外面」。', p: { a: a, b: b, less: less } };
  };

  /* 3-4 兩定點距離和的最小值 */
  L1.absSum2 = function (r) {
    var a = r.int(-6, 3), b = a + r.int(1, 9);
    return { q: '求 ' + T('|x' + (a === 0 ? '' : signed(-a)) + '|+|x' + signed(-b) + '|') + ' 的最小值。',
             a: '最小值 ' + T(String(b - a)) + '（當 ' + T(a + '\\le x\\le ' + b) + ' 時）',
             h: '到兩點的距離和，最小就是兩點的距離，且 $x$ 在兩點之間時都達到。', p: { a: a, b: b, min: b - a } };
  };

  /* 4-1 指數律化簡 */
  L1.expLaw = function (r) {
    var base = r.pick(['a', 'x', '2', '3']), v = r.int(0, 2);
    var m = r.int(2, 6), n = r.int(2, 6), k = r.int(2, 3);
    if (v === 0) return { q: '化簡 ' + T(base + '^{' + m + '}\\cdot ' + base + '^{' + n + '}\\div ' + base + '^{' + k + '}') + '。', a: T(base + '^{' + (m + n - k) + '}'), h: '同底相乘指數相加、相除指數相減。', p: { v: 0, base: base, m: m, n: n, k: k } };
    if (v === 1) return { q: '化簡 ' + T('\\left(' + base + '^{' + m + '}\\right)^{' + k + '}\\div ' + base + '^{' + n + '}') + '。', a: T(base + '^{' + (m * k - n) + '}'), h: '次方的次方指數相乘。', p: { v: 1, base: base, m: m, n: n, k: k } };
    var p = r.int(1, 5), q = r.pick([2, 3, 4]); var g = gcd(p, q); p /= g; q /= g;
    return { q: '把 ' + T('\\sqrt[' + q + ']{' + base + '^{' + p + '}}') + ' 改寫成分數指數。', a: T(base + '^{' + (q === 1 ? String(p) : '\\frac{' + p + '}{' + q + '}') + '}'), h: '$\\sqrt[q]{a^p}=a^{p/q}$：根指數在分母、次方在分子。', p: { v: 2, base: base, p: p, q: q } };
  };

  /* 4-2 同底指數比較大小 */
  L1.expCompare = function (r) {
    var base = r.pick([2, 3, 5, 10]), es = r.shuffle([r.int(-3, -1), r.int(0, 2), r.int(3, 6)]);
    var lbl = ['a', 'b', 'c'], items = lbl.map(function (L, i) { return L + '=' + base + '^{' + es[i] + '}'; });
    var order = [0, 1, 2].sort(function (i, j) { return es[j] - es[i]; }).map(function (i) { return lbl[i]; });
    return { q: '設 ' + T(items.join(',\\ ')) + '，由大到小排列。', a: T(order.join('>')), h: '底數 $' + base + '>1$ ⟹ 指數越大值越大。', p: { base: base, es: es, order: order } };
  };

  /* 4-3 科學記號 */
  L1.sciNot = function (r) {
    var big = r() < 0.5, m = r.int(101, 999), e = big ? r.int(3, 9) : r.int(-8, -2);
    var val = big ? String(m) + '0'.repeat(e - 2) : '0.' + '0'.repeat(-e - 1) + String(m);
    return { q: '將 ' + T(val) + ' 寫成科學記號 ' + T('a\\times10^{n}') + '（' + T('1\\le a<10') + '）。',
             a: T((m / 100) + '\\times10^{' + e + '}'),
             h: '小數點移到「第一個非零數字」後面，往左移幾位 $n$ 就是幾、往右移就是負的。', p: { m: m, e: e } };
  };

  /* 4-4 常用對數基本值 */
  L1.logBasic = function (r) {
    var v = r.int(0, 2);
    if (v === 0) { var k = r.int(-3, 6); return { q: '求 ' + T('\\log10^{' + k + '}') + '。', a: T(String(k)), h: '$\\log10^k=k$。', p: { v: 0, k: k } }; }
    if (v === 1) { var n = r.pick([100, 1000, 10000, 0.1, 0.01, 0.001]); var ans = Math.round(Math.log10(n)); return { q: '求 ' + T('\\log ' + n) + '。', a: T(String(ans)), h: '先把它寫成 $10$ 的幾次方。', p: { v: 1, n: n, ans: ans } }; }
    var a = r.pick([2, 3, 5, 7]), e = r.int(1, 4), la = { 2: 0.3010, 3: 0.4771, 5: 0.6990, 7: 0.8451 }[a];
    return { q: '已知 ' + T('\\log' + a + '\\approx' + la.toFixed(4)) + '，求 ' + T('\\log(' + a + '\\times10^{' + e + '})') + '。', a: T((e + la).toFixed(4)), h: '$\\log(ab)=\\log a+\\log b$，而 $\\log10^{' + e + '}=' + e + '$。', p: { v: 2, a: a, e: e, ans: e + la } };
  };

  /* 4-5 位數 */
  L1.digits = function (r) {
    var base = r.pick([2, 3, 6, 7]), n, lg = { 2: 0.3010, 3: 0.4771, 6: 0.7781, 7: 0.8451 }[base], v, d, m, tries = 0;
    do { n = r.int(10, 60); v = Math.round(n * lg * 10000) / 10000; m = v - Math.floor(v); } while ((m < 0.005 || m > 0.995) && tries++ < 60);
    d = Math.floor(v) + 1;
    return { q: '已知 ' + T('\\log' + base + '\\approx' + lg.toFixed(4)) + '，問 ' + T(base + '^{' + n + '}') + ' 是幾位數？',
             a: T(String(d)) + ' 位數（' + T('\\log' + base + '^{' + n + '}=' + n + '\\times' + lg.toFixed(4) + '=' + v.toFixed(2)) + '）',
             h: '位數 ＝ $\\log$ 的整數部分 $+1$。', p: { base: base, n: n, lg: lg, d: d } };
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
             h: '先各自化成分數再運算；混循環的分母是 90。', p: { rep1: rep1, pre2: pre2, rep2: rep2, op: op, n: res.n, d: res.d } };
  };

  /* 2-2 小數點後第 n 位 */
  L2.nthDigit = function (r) {
    var d = r.pick([7, 13, 21, 27, 37, 41, 11, 33, 99]), n = r.int(1, d - 1); if (gcd(n, d) !== 1) n = 1;
    var ex = fracToRepeating(n, d), N = r.pick([100, 2024, 2025, 500, 1001, 2026]);
    var k = ex.pre.length, m = ex.rep.length, digit;
    if (N <= k) digit = ex.pre[N - 1]; else digit = ex.rep[(N - k - 1) % m];
    return { q: T('\\dfrac{' + n + '}{' + d + '}') + ' 化成小數後，小數點後第 ' + T(String(N)) + ' 位的數字是多少？',
             a: T(String(digit)) + '　（' + T(repTex(0, ex.pre, ex.rep)) + '，循環節長 ' + m + '，' + (N - k) + ' 除以 ' + m + ' 餘 ' + ((N - k) % m) + '）',
             h: '先除出循環節，用「第幾位 ÷ 節長」的餘數對回去；餘 0 就是循環節最後一位。', p: { n: n, d: d, N: N, digit: parseInt(digit, 10) } };
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
    var n = r.pick([5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20]), k = isqrt(n);
    /* 1/b = 1/(√n-k) = (√n+k)/(n-k²) */
    var den = n - k * k, v = r.int(0, 1);
    if (v === 0) {   /* 1/b − 1/a = (√n+k)/den − 1/k = (k√n + k² − den)/(k·den) */
      var num0 = k * k - den, nums = k, D = k * den;
      return { q: '設 ' + T('\\sqrt{' + n + '}') + ' 的整數部分為 ' + T('a') + '、小數部分為 ' + T('b') + '，求 ' + T('\\dfrac1b-\\dfrac1a') + '。',
               a: T(surdFracTex(num0, nums, n, D)), h: '$b=\\sqrt{' + n + '}-' + k + '$，$\\dfrac1b$ 要有理化。', p: { n: n, k: k, v: 0 } };
    }
    /* a·b + b² = b(a+b) = (√n−k)√n = n − k√n */
    return { q: '設 ' + T('\\sqrt{' + n + '}') + ' 的整數部分為 ' + T('a') + '、小數部分為 ' + T('b') + '，求 ' + T('ab+b^2') + '。',
             a: T(surdTex(n, -k, n)), h: '$ab+b^2=b(a+b)=b\\sqrt{' + n + '}$。', p: { n: n, k: k, v: 1 } };
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
    var pairs = [[2, 1], [3, 1], [5, 1], [3, 2], [5, 2], [6, 2], [7, 3], [5, 3]];
    var pr = r.pick(pairs), A = pr[0], B = pr[1];   /* x = (√A−√B)/(√A+√B)，x+1/x = 2(A+B)/(A−B) */
    var s = F(2 * (A + B), A - B);
    var s2 = Fr.sub(Fr.mul(s, s), F(2)), s3 = Fr.sub(Fr.mul(Fr.mul(s, s), s), Fr.mul(F(3), s));
    var which = r.int(0, 1);
    return { q: '設 ' + T('x=\\dfrac{' + sqrtTex(A) + '-' + sqrtTex(B) + '}{' + sqrtTex(A) + '+' + sqrtTex(B) + '}') + '，求 ' + T(which === 0 ? 'x^2+\\dfrac1{x^2}' : 'x^3+\\dfrac1{x^3}') + '。',
             a: T(Fr.tex(which === 0 ? s2 : s3)) + '　（' + T('x+\\dfrac1x=' + Fr.tex(s, false)) + '）',
             h: '$\\dfrac1x$ 恰是分子分母對調，$x+\\dfrac1x$ 有理化後很乾淨；再用 $x^2+\\frac1{x^2}=(x+\\frac1x)^2-2$、$x^3+\\frac1{x^3}=(x+\\frac1x)^3-3(x+\\frac1x)$。',
             p: { A: A, B: B, which: which, sn: s.n, sd: s.d, an: (which === 0 ? s2 : s3).n, ad: (which === 0 ? s2 : s3).d } };
  };

  /* 2-7 算幾：條件式 × 目標式 */
  L2.amgmCond = function (r) {
    var a = r.int(1, 4), b = r.int(1, 4), v = r.int(0, 1);
    if (v === 0) {   /* a/x + b/y = 1 ⟹ xy ≥ 4ab，x=2a, y=2b */
      return { q: '設 ' + T('x,y>0') + ' 且 ' + T('\\dfrac{' + a + '}{x}+\\dfrac{' + b + '}{y}=1') + '，求 ' + T('xy') + ' 的最小值及此時的 ' + T('(x,y)') + '。',
               a: '最小值 ' + T(String(4 * a * b)) + '，' + T('(x,y)=(' + 2 * a + ',' + 2 * b + ')'),
               h: '$1=\\dfrac ax+\\dfrac by\\ge2\\sqrt{\\dfrac{ab}{xy}}$，等號在 $\\dfrac ax=\\dfrac by=\\dfrac12$。', p: { v: 0, a: a, b: b, min: 4 * a * b } };
    }
    /* x + y = S ⟹ xy 最大 (S/2)²，S 偶數 */
    var S = 2 * r.int(2, 12);
    return { q: '設 ' + T('x,y>0') + ' 且 ' + T('x+y=' + S) + '，求 ' + T('xy') + ' 的最大值。', a: '最大值 ' + T(String(S * S / 4)) + '（' + T('x=y=' + S / 2) + '）',
             h: '$\\sqrt{xy}\\le\\dfrac{x+y}{2}$。', p: { v: 1, S: S, max: S * S / 4 } };
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
    return { q: '解不等式 ' + T('|x' + (a === 0 ? '' : signed(-a)) + '|+|x' + signed(-b) + '|\\le' + k) + '。',
             a: T(Fr.tex(lo, false) + '\\le x\\le' + Fr.tex(hi, false)),
             h: '兩點距離和 $\\le k$（$k>$ 兩點距離）⟹ 從兩點中點往外各 $\\frac k2$。或分三段討論。', p: { a: a, b: b, k: k, lon: lo.n, lod: lo.d, hin: hi.n, hid: hi.d } };
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
             h: '把 $k|x-p|$ 看成「$p$ 這個點放了 $k$ 個人」，最小值在累積人數過半的那個點（中位數）。', p: { pts: pts, w: w, min: val, med: med } };
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
    var base = r.pick([2, 3, 5]), e1 = r.int(0, 3), e2 = r.int(0, 3); if (e1 === e2) e2 = e1 + 1;
    var t1 = Math.pow(base, e1), t2 = Math.pow(base, e2), S = t1 + t2, P = t1 * t2;
    return { q: '解方程式 ' + T(base * base + '^{x}-' + S + '\\cdot' + base + '^{x}+' + P + '=0') + '。',
             a: T('x=' + Math.min(e1, e2) + '\\ \\text{或}\\ x=' + Math.max(e1, e2)),
             h: '令 $t=' + base + '^x>0$，則 $' + base * base + '^x=t^2$，變成二次方程式。', p: { base: base, e1: e1, e2: e2 } };
  };

  /* 2-14 a^x ± a^{-x} 升冪 */
  L2.expSymm = function (r) {
    var s = r.int(3, 7), v = r.int(0, 1);
    if (v === 0) return { q: '已知 ' + T('a^x+a^{-x}=' + s) + '，求 ' + T('a^{2x}+a^{-2x}') + ' 與 ' + T('a^{3x}+a^{-3x}') + '。', a: T(String(s * s - 2)) + '、' + T(String(s * s * s - 3 * s)), h: '平方：$(a^x+a^{-x})^2=a^{2x}+2+a^{-2x}$；立方：$t^3-3t$。', p: { v: 0, s: s, a2: s * s - 2, a3: s * s * s - 3 * s } };
    /* a^x − a^{-x} = s ⟹ a^x + a^{-x} = √(s²+4)，a^{2x}+a^{-2x} = s²+2 */
    return { q: '已知 ' + T('a^x-a^{-x}=' + s) + '，求 ' + T('a^{2x}+a^{-2x}') + ' 與 ' + T('a^{x}+a^{-x}') + '（' + T('a>0') + '）。', a: T(String(s * s + 2)) + '、' + T('\\sqrt{' + (s * s + 4) + '}'), h: '$(a^x-a^{-x})^2=a^{2x}-2+a^{-2x}$；$(a^x+a^{-x})^2=(a^x-a^{-x})^2+4$，且兩正數之和為正。', p: { v: 1, s: s, a2: s * s + 2, sum2: s * s + 4 } };
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
    var given = base === 12 ? '\\log2\\approx0.3010,\\ \\log3\\approx0.4771' : '\\log' + base + '\\approx' + lg.toFixed(4);
    return { q: '已知 ' + T(given) + '（必要時可用 $\\log2,\\log3$ 推其他值），問 ' + T(base + '^{' + n + '}') + ' 是幾位數？最高位數字是幾？',
             a: T(String(d)) + ' 位數，最高位數字 ' + T(String(lead)) + '　（' + T('\\log=' + v.toFixed(4)) + '，尾數 ' + T(mant.toFixed(4)) + '）',
             h: '首數 $+1$ 是位數；尾數落在 $\\log k$ 與 $\\log(k+1)$ 之間 ⟹ 最高位是 $k$。', p: { base: base, n: n, lg: lg, d: d, lead: lead } };
  };

  /* 2-16 (1/k)^n 小數點後第幾位出現非零 */
  L2.decimalFirst = function (r) {
    var base = r.pick([2, 3, 5, 6, 7]), n, lg = { 2: 0.3010, 3: 0.4771, 5: 0.6990, 6: 0.7781, 7: 0.8451 }[base], v, m, tries = 0;
    do { n = r.int(10, 60); v = -Math.round(n * lg * 10000) / 10000; m = v - Math.floor(v); } while ((m < 0.005 || m > 0.995) && tries++ < 60);
    var pos = -Math.floor(v);   /* log = −k + m ⟹ 第 k 位 */
    return { q: '已知 ' + T('\\log' + base + '\\approx' + lg.toFixed(4)) + '，問 ' + T('\\left(\\dfrac1{' + base + '}\\right)^{' + n + '}') + ' 化成小數後，從小數點後第幾位開始出現不為 0 的數字？',
             a: '第 ' + T(String(pos)) + ' 位（' + T('\\log=-' + (n * lg).toFixed(4) + '=-' + pos + '+' + (pos - n * lg).toFixed(4)) + '）',
             h: '把負的 $\\log$ 寫成「負整數 $+$ 正小數」，那個負整數的絕對值就是位置。', p: { base: base, n: n, pos: pos } };
  };

  /* 2-17 複利：至少幾年超過 k 倍 */
  L2.compound = function (r) {
    var rate, k, lg1, lgk, ratio, tries = 0;
    /* 表值四位小數：商若太接近整數，表值算出來的年數可能與精確值差一年 ⟹ 重抽 */
    do {
      rate = r.pick([3, 4, 5, 6, 8]); k = r.pick([2, 3, 5]);
      lg1 = { 3: 0.0128, 4: 0.0170, 5: 0.0212, 6: 0.0253, 8: 0.0334 }[rate]; lgk = { 2: 0.3010, 3: 0.4771, 5: 0.6990 }[k];
      ratio = lgk / lg1;
    } while (Math.abs(ratio - Math.round(ratio)) < 0.12 && tries++ < 40);
    var n = Math.floor(ratio) + 1;
    return { q: '本金以年利率 ' + T(rate + '\\%') + ' 每年複利一次，至少要幾年本利和才會超過本金的 ' + T(String(k)) + ' 倍？（' + T('\\log1.' + (rate < 10 ? '0' + rate : rate) + '\\approx' + lg1.toFixed(4) + ',\\ \\log' + k + '\\approx' + lgk.toFixed(4)) + '）',
             a: T(String(n)) + ' 年（' + T('n>\\dfrac{' + lgk.toFixed(4) + '}{' + lg1.toFixed(4) + '}\\approx' + (lgk / lg1).toFixed(2)) + '）',
             h: '$(1+r)^n>k$ 兩邊取 $\\log$：$n\\log(1+r)>\\log k$。', p: { rate: rate, k: k, n: n } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['rational', '§1 有理數／無理數判別'], ['repPure', '§1 純循環小數化分數'], ['repMixed', '§1 混循環小數化分數'],
      ['fracKind', '§1 分數化小數：有限還是循環'], ['divPoint', '§1 數線上的內分點'],
      ['simpRoot', '§2 根式化簡'], ['addRoots', '§2 同類根式加減'], ['ratSingle', '§2 分母有理化（單項）'],
      ['ratConj', '§2 分母有理化（共軛）'], ['doubleRoot', '§2 雙重根號（直接拆）'], ['intFrac', '§2 整數部分與小數部分'],
      ['amgm', '§2 算幾不等式（直接型）'],
      ['absSimp', '§3 去絕對值符號'], ['absEq', '§3 絕對值方程式'], ['absIneq', '§3 絕對值不等式'], ['absSum2', '§3 兩點距離和的最小值'],
      ['expLaw', '§4 指數律化簡'], ['expCompare', '§4 同底指數比較'], ['sciNot', '§4 科學記號'], ['logBasic', '§4 常用對數基本值'], ['digits', '§4 位數']
    ],
    L2: [
      ['repArith', '§1 循環小數的四則'], ['nthDigit', '§1 小數點後第 n 位'], ['coefCompare', '§1 有理化＋係數比較'],
      ['intFracOp', '§2 整數／小數部分再運算'], ['doubleRoot2', '§2 雙重根號（先提 2）'], ['symm', '§2 $x+\\frac1x$ 對稱式'], ['amgmCond', '§2 算幾：條件式×目標式'],
      ['absIneq2', '§3 絕對值不等式三型'], ['absSumIneq', '§3 距離和不等式'], ['absMedian', '§3 加權距離和最小值'], ['absParam', '§3 反推參數'], ['absIntCount', '§3 整數解個數'],
      ['expEq', '§4 指數方程式（換元）'], ['expSymm', '§4 $a^x\\pm a^{-x}$ 升冪'], ['digitsLead', '§4 位數與最高位數字'], ['decimalFirst', '§4 小數點後第幾位非零'], ['compound', '§4 複利幾年']
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
           _util: { gcd: gcd, F: F, Fr: Fr, simpSqrt: simpSqrt, repeatingToFrac: repeatingToFrac, fracToRepeating: fracToRepeating } };
}));
