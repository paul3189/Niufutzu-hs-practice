/* ══════════════════════════════════════════════════════════════
   g10b-ch03 數據分析・分級練習本　題目產生器
   ─────────────────────────────────────────────────────────────
   每個產生器：function (rng) → { q, a, h, p }
     q：題目（HTML，可含 KaTeX $…$）   a：答案（HTML）
     h：一行提示                         p：參數與結構化答案（給 verify_gen10b3.py 用 Fraction 獨立重算）
   答案一律精確：分數用 F()、根號用 sqrtTex()／sqrtFracTex()；能化成有限小數的分數用 dec() 印小數。
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
    abs: function (x) { return F(Math.abs(x.n), x.d); },
    toNum: function (x) { return x.n / x.d; },
    tex: function (x, small) {
      if (x.d === 1) return String(x.n);
      var f = small ? '\\frac' : '\\dfrac';
      return (x.n < 0 ? '-' : '') + f + '{' + Math.abs(x.n) + '}{' + x.d + '}';
    }
  };
  function fr2(f) { return [f.n, f.d]; }
  function T(s) { return '$' + s + '$'; }
  /* 有限小數就印小數（0.6、-1.75），否則印分數 */
  function dec(f) {
    if (f.d === 1) return String(f.n);
    for (var k = 1, p = 10; k <= 4; k++, p *= 10) {
      if (p % f.d === 0) {
        var v = f.n * (p / f.d), s = String(Math.abs(v));
        while (s.length <= k) s = '0' + s;
        return (v < 0 ? '-' : '') + s.slice(0, s.length - k) + '.' + s.slice(s.length - k).replace(/0+$/, '');
      }
    }
    return Fr.tex(f);
  }
  function simpSqrt(n) { var c = 1, r = n; for (var p = 2; p * p <= r; p++) { while (r % (p * p) === 0) { r /= p * p; c *= p; } } return [c, r]; }
  function sqrtTex(n) { if (n === 0) return '0'; var s = simpSqrt(n); if (s[1] === 1) return String(s[0]); return (s[0] === 1 ? '' : s[0]) + '\\sqrt{' + s[1] + '}'; }
  /* √(n/d)，n/d 為已約分的非負分數 → 化成 c√r/d 的形式 */
  function sqrtFracTex(f) {
    if (f.n === 0) return '0';
    var s = simpSqrt(f.n * f.d), c = s[0], r = s[1], d = f.d, g = gcd(c, d); c /= g; d /= g;
    var top = r === 1 ? String(c) : (c === 1 ? '' : c) + '\\sqrt{' + r + '}';
    return d === 1 ? top : '\\dfrac{' + top + '}{' + d + '}';
  }
  /* 答案同時給精確與近似：σ=√12=2√3≈3.46 */
  function sqrtBoth(f) {
    var ex = sqrtFracTex(f), v = Math.sqrt(Fr.toNum(f));
    if (Math.abs(v - Math.round(v * 1000) / 1000) < 1e-9 && ex.indexOf('sqrt') < 0) return ex;
    return ex + '\\approx' + (Math.round(v * 100) / 100);
  }
  function sumArr(a) { return a.reduce(function (s, v) { return s + v; }, 0); }
  function meanF(a) { return F(sumArr(a), a.length); }
  function varF(a) { var m = meanF(a), s = F(0); a.forEach(function (v) { var d = Fr.sub(F(v), m); s = Fr.add(s, Fr.mul(d, d)); }); return Fr.div(s, F(a.length)); }
  function pctF(sorted, k) {
    var n = sorted.length, t = F(n * k, 100);
    if (t.d === 1) return F(sorted[t.n - 1] + sorted[t.n], 2);
    return F(sorted[Math.ceil(t.n / t.d) - 1]);
  }
  function tOf(n, k) { return F(n * k, 100); }
  function listTex(a) { return a.join(',\\ '); }
  function pairsTex(x, y) { var s = []; for (var i = 0; i < x.length; i++) s.push('(' + x[i] + ',' + y[i] + ')'); return s.join(',\\ '); }
  function pctTex(v) { return v + '\\%'; }
  var SUBJ = ['國文', '英文', '數學', '物理', '化學', '歷史', '地理', '生物'];
  var NAMES = ['小明', '小華', '小美', '阿凱', '小芸', '小傑'];
  /* 五筆二維資料：dx=k·i（i=-2..2），dy=s·(m·i+c·e)，e=[-1,2,0,-2,1]（Σe=0、Σe·i=0、Σe²=10）
     ⟹ Sxx=10k²、Sxy=10mks、Syy=10s²(m²+c²)、r=m/√(m²+c²)：(m,c)=(±3,±4)→±3/5、(±4,±3)→±4/5、(±1,0)→±1 */
  function makeXY(r, allowPerfect) {
    var k = r.int(1, 3), s = r.pick([1, 1, 2]);
    var pc = r.pick(allowPerfect ? [[3, 4], [4, 3], [3, 4], [4, 3], [1, 0]] : [[3, 4], [4, 3]]);
    var m = pc[0] * r.sign(), c = pc[1] * r.sign();
    var I = [-2, -1, 0, 1, 2], E = [-1, 2, 0, -2, 1];
    var mx = r.int(6, 60), my = r.int(20, 70);
    var x = [], y = [];
    for (var j = 0; j < 5; j++) { x.push(mx + k * I[j]); y.push(my + s * (m * I[j] + c * E[j])); }
    var rr = F(m, Math.sqrt(m * m + c * c));            // 分母 5 或 1，恰為整數
    var slope = F(m * s, k), icpt = Fr.sub(F(my), Fr.mul(slope, F(mx)));
    return { x: x, y: y, r: rr, slope: slope, icpt: icpt, mx: mx, my: my, sxx: 10 * k * k, syy: 10 * s * s * (m * m + c * c), sxy: 10 * m * k * s };
  }
  function lineTex(a, b) {           // y = a x + b 的排版
    var s = 'y=';
    if (Fr.eq(a, F(1))) s += 'x'; else if (Fr.eq(a, F(-1))) s += '-x'; else s += dec(a) + 'x';
    if (b.n > 0) s += '+' + dec(b); else if (b.n < 0) s += dec(b);
    return s;
  }

  /* ── patch_gen_10b3 新增工具（優化 #7 提示用） ── */
  /* n/d 的分數：分母 1 就只印分子，負號提到分數外面 */
  function hxDiv(n, d) { return d === 1 ? String(n) : (n < 0 ? '-' : '') + '\\dfrac{' + Math.abs(n) + '}{' + d + '}'; }
  /* 連乘：等於 1 的因數直接省略（成長率 0% 的倍率） */
  function hxMulList(list) {
    var f = [], i;
    for (i = 0; i < list.length; i++) if (String(list[i]) !== '1') f.push(list[i]);
    return f.length ? f.join('\\times') : '1';
  }
  /* 每筆減去平均，得到偏差陣列 */
  function hxDev(arr, m) { return arr.map(function (v) { return v - m; }); }
  /* ── patch_gen_10b3 新增工具結束 ── */
  /* ═══════════════════════ L1 ═══════════════════════ */
  var L1 = {};

  /* ── §1-1 集中趨勢與加權平均 ── */
  L1.centralTrio = function (r) {
    var m = r.int(3, 12), data, tries = 0, pool = [];
    for (var v = 1; v <= 16; v++) if (v !== m) pool.push(v);
    do { data = [m, m, m].concat(r.shuffle(pool).slice(0, 4)); tries++; } while (sumArr(data) % 7 !== 0 && tries < 80);
    data = r.shuffle(data);
    var sorted = data.slice().sort(function (a, b) { return a - b; }), mu = meanF(data), me = sorted[3];
    return { q: '求資料 ' + T(listTex(data)) + ' 的算術平均數、中位數與眾數。',
             a: T('\\mu=' + dec(mu)) + '、' + T('Me=' + me) + '、' + T('Mo=' + m),
             h: '先由小到大排好：' + T(listTex(sorted)) + '；$7$ 筆的中位數是第 $4$ 筆，出現 $3$ 次的 ' + T(String(m)) + ' 是眾數，平均數 ' + T('=\\dfrac{' + sumArr(data) + '}{7}') + '。',
             p: { data: data, ans: { mu: fr2(mu), me: me, mo: m } } };
  };
  L1.weightedMean = function (r) {
    var n1 = r.pick([20, 24, 25, 30, 32, 36, 40]), n2 = r.pick([15, 16, 20, 24, 25, 30, 40]);
    var m1 = r.int(55, 90), m2 = r.int(55, 90); if (m1 === m2) m2 += 4;
    var mu = F(n1 * m1 + n2 * m2, n1 + n2);
    return { q: '甲班 ' + T(String(n1)) + ' 人的平均成績為 ' + T(String(m1)) + ' 分，乙班 ' + T(String(n2)) + ' 人的平均成績為 ' + T(String(m2)) + ' 分。求兩班合併後全部 ' + T(String(n1 + n2)) + ' 人的平均成績。',
             a: T('\\mu=\\dfrac{' + n1 + '(' + m1 + ')+' + n2 + '(' + m2 + ')}{' + (n1 + n2) + '}=' + dec(mu)) + ' 分',
             h: '權重是人數：總分 $=$ 人數 $\\times$ 平均，兩班總分相加再除以總人數；不是 $\\dfrac{' + m1 + '+' + m2 + '}{2}$。',
             p: { n1: n1, m1: m1, n2: n2, m2: m2, ans: fr2(mu) } };
  };
  L1.weightedScore = function (r) {
    var kind = r.int(0, 1), w, names, idx;
    if (kind === 0) { w = [40, 20, 20, 20]; names = ['平時成績', '第一次段考', '第二次段考', '第三次段考']; idx = 3; }
    else { w = [20, 20, 30, 30]; names = ['第一次期中考', '第二次期中考', '平時成績', '期末考']; idx = 3; }
    var target = r.pick([60, 65, 70, 75, 80]), s, need, tries = 0;
    do {
      s = []; for (var i = 0; i < 4; i++) s.push(i === idx ? 0 : r.int(45, 92));
      var known = 0; for (i = 0; i < 4; i++) if (i !== idx) known += w[i] * s[i];
      need = F(100 * target - known, w[idx]); tries++;
    } while ((Fr.toNum(need) <= 20 || Fr.toNum(need) > 100) && tries < 60);
    var ans = Math.ceil(Fr.toNum(need) - 1e-9);
    var parts = []; for (i = 0; i < 4; i++) parts.push(names[i] + ' ' + T(w[i] + '\\%'));
    var given = []; for (i = 0; i < 4; i++) if (i !== idx) given.push(names[i] + ' ' + T(String(s[i])) + ' 分');
    var kn = []; for (i = 0; i < 4; i++) if (i !== idx) kn.push(w[i] + '(' + s[i] + ')');
    return { q: '某科學期成績的計算方式：' + parts.join('、') + '。' + NAMES[r.int(0, 5)] + '目前' + given.join('、') + '。若學期成績要達到 ' + T(String(target)) + ' 分（含）以上，' + names[idx] + '至少要考幾分？（分數為整數）',
             a: '至少 ' + T(String(ans)) + ' 分' + (need.d === 1 ? '' : '（不等式解得 ' + T('\\ge' + dec(need)) + '，取整數）'),
             h: '已知的三項（權重乘分數）合計 ' + T(kn.join('+') + '=' + known) + '；學期成績 ' + T('\\ge' + target) + ' 就是 ' + T(known + '+' + w[idx] + 'x\\ge' + (100 * target)) + '，解出 $x$ 再取整數；權重加總要是 $100\\%$。',
             p: { w: w, s: s, idx: idx, target: target, ans: ans } };
  };
  L1.freqTable = function (r) {
    var base = r.pick([[1, 2, 3, 4, 5], [60, 70, 80, 90, 100], [0, 1, 2, 3, 4], [2, 4, 6, 8, 10]]);
    var vals = base.slice(0, 4), cnts = [], n;
    do { cnts = [r.int(1, 8), r.int(1, 8), r.int(1, 8), r.int(1, 8)]; n = sumArr(cnts); } while (n < 8);
    var data = []; for (var i = 0; i < 4; i++) for (var j = 0; j < cnts[i]; j++) data.push(vals[i]);
    var mu = meanF(data), me = pctF(data, 50);
    var rows = []; for (i = 0; i < 4; i++) rows.push(T(String(vals[i])) + ' 出現 ' + T(String(cnts[i])) + ' 次');
    var prods = [], cum = [], run = 0;
    for (i = 0; i < 4; i++) { prods.push(vals[i] * cnts[i]); run += cnts[i]; cum.push(run); }
    return { q: '某組資料共 ' + T(String(n)) + ' 筆：' + rows.join('、') + '。求此組資料的算術平均數與中位數。',
             a: T('\\mu=' + dec(mu)) + '、' + T('Me=' + dec(me)),
             h: '平均數 ' + T('=\\dfrac{\\sum(\\text{數值}\\times\\text{次數})}{' + n + '}=\\dfrac{' + prods.join('+') + '}{' + n + '}') + '；累積次數為 ' + T(listTex(cum)) + '，' + (n % 2 ? '第 ' + T(String((n + 1) / 2)) + ' 筆' : '第 ' + T(String(n / 2)) + '、' + T(String(n / 2 + 1)) + ' 筆的平均') + '就是中位數。',
             p: { vals: vals, cnts: cnts, ans: { mu: fr2(mu), me: fr2(me) } } };
  };
  L1.meanShift = function (r) {
    var kind = r.int(0, 1), n = r.pick([9, 11, 14, 15, 19, 20, 24]), mu = r.int(60, 80);
    if (kind === 0) {
      var v = mu + r.pick([-20, -15, -10, 10, 15, 20, 25]), mu2 = F(n * mu + v, n + 1);
      return { q: '某組資料共 ' + T(String(n)) + ' 筆，平均數為 ' + T(String(mu)) + '。若再加入一筆資料 ' + T(String(v)) + '，求新的 ' + T(String(n + 1)) + ' 筆資料的平均數。',
               a: T('\\mu\'=\\dfrac{' + n + '(' + mu + ')+' + v + '}{' + (n + 1) + '}=' + dec(mu2)),
               h: '用「總和」思考：原總和 $=n\\mu$，加上新的一筆再除以 $n+1$。',
               p: { kind: 0, n: n, mu: mu, v: v, ans: fr2(mu2) } };
    }
    var rem = [Math.min(100, mu + r.int(16, 30)), mu - r.int(16, 30)], mu3 = F(n * mu - rem[0] - rem[1], n - 2);
    return { q: T(String(n)) + ' 位評審的評分平均為 ' + T(String(mu)) + ' 分。依規定要剔除與平均相差最多的兩個分數 ' + T(String(rem[0])) + '、' + T(String(rem[1])) + '，再以其餘 ' + T(String(n - 2)) + ' 位的平均作為成績。求此成績。',
             a: T('\\dfrac{' + n + '(' + mu + ')-' + rem[0] + '-' + rem[1] + '}{' + (n - 2) + '}=' + dec(mu3)) + ' 分',
             h: '總分 $=' + n + '\\times' + mu + '$，扣掉被剔除的兩個分數，再除以剩下的人數。',
             p: { kind: 1, n: n, mu: mu, rem: rem, ans: fr2(mu3) } };
  };

  /* ── §1-2 百分位數 ── */
  L1.pctPosition = function (r) {
    var n = r.int(20, 60), k = r.pick([10, 15, 20, 25, 30, 32, 35, 40, 45, 60, 65, 70, 75, 80, 85, 90]);
    var t = tOf(n, k), pos, ans;
    if (t.d === 1) { pos = [t.n, t.n + 1]; ans = '$t=' + t.n + '$ 是整數 ⟹ 取第 $' + t.n + '$、$' + (t.n + 1) + '$ 筆的平均'; }
    else { var c = Math.ceil(t.n / t.d); pos = [c]; ans = '$t=' + dec(t) + '$ 不是整數 ⟹ 無條件進位，取第 $' + c + '$ 筆'; }
    return { q: '某班 ' + T(String(n)) + ' 位同學的成績已由小到大排好。第 ' + T(String(k)) + ' 百分位數 ' + T('P_{' + k + '}') + ' 應取第幾筆資料（或哪兩筆的平均）？',
             a: ans, h: '先算 $t=\\dfrac{nk}{100}=\\dfrac{' + n + '\\times' + k + '}{100}$：整數 ⟹ 第 $t$、$t+1$ 筆平均；非整數 ⟹ 進位取第 $\\lceil t\\rceil$ 筆。',
             p: { n: n, k: k, ans: { t: fr2(t), pos: pos } } };
  };
  L1.pctData = function (r) {
    var n = r.pick([10, 12, 15, 16, 20]), data = [];
    for (var i = 0; i < n; i++) data.push(r.int(40, 99));
    data.sort(function (a, b) { return a - b; });
    var ks = r.shuffle([10, 20, 25, 30, 40, 60, 70, 75, 80, 90]).slice(0, 2).sort(function (a, b) { return a - b; });
    var v1 = pctF(data, ks[0]), v2 = pctF(data, ks[1]);
    return { q: '某組資料共 ' + T(String(n)) + ' 筆，已由小到大排列：' + T(listTex(data)) + '。求 ' + T('P_{' + ks[0] + '}') + ' 與 ' + T('P_{' + ks[1] + '}') + '。',
             a: T('P_{' + ks[0] + '}=' + dec(v1)) + '、' + T('P_{' + ks[1] + '}=' + dec(v2)),
             h: '兩個 $t=\\dfrac{' + n + 'k}{100}$ 分別是 $' + dec(tOf(n, ks[0])) + '$ 與 $' + dec(tOf(n, ks[1])) + '$；整數取兩筆平均、非整數進位取一筆。',
             p: { data: data, ks: ks, ans: [fr2(v1), fr2(v2)] } };
  };
  L1.pctFreq = function (r) {
    var m = r.int(8, 20), n = m * (m + 1) / 2, k = r.pick([10, 20, 25, 30, 40, 50, 60, 70, 75, 80, 90]);
    var data = []; for (var v = 1; v <= m; v++) for (var j = 0; j < v; j++) data.push(v);
    var ans = pctF(data, k), item = r.pick(['寶石', '貼紙', '徽章', '點數卡']);
    return { q: '某遊戲共有 ' + T(String(n)) + ' 位玩家：持有 ' + T('1') + ' 個' + item + '的有 ' + T('1') + ' 位、持有 ' + T('2') + ' 個的有 ' + T('2') + ' 位、……、持有 ' + T(String(m)) + ' 個的有 ' + T(String(m)) + ' 位。求每人持有' + item + '數量的第 ' + T(String(k)) + ' 百分位數。',
             a: T('P_{' + k + '}=' + dec(ans)),
             h: '$n=1+2+\\cdots+' + m + '=' + n + '$；$t=' + dec(tOf(n, k)) + '$，再列累積人數 $1,3,6,10,\\dots$（第 $j$ 格累積到 $\\frac{j(j+1)}{2}$）看落在哪一格。',
             p: { m: m, k: k, ans: fr2(ans) } };
  };

  /* ── §1-3 分散程度 ── */
  function devData(r, n) {
    /* 偏差和為 0；儘量讓偏差平方和被 n 整除（變異數是整數，L1 用），試 80 次不成就接受分數 */
    var dev, s, sq, tries = 0;
    do {
      dev = []; s = 0; for (var i = 0; i < n - 1; i++) { var d = r.int(-5, 5); dev.push(d); s += d; } dev.push(-s);
      sq = 0; dev.forEach(function (d) { sq += d * d; }); tries++;
    } while ((Math.abs(s) > 6 || sq === 0 || (sq % n !== 0 && tries < 80)) && tries < 120);
    var mu = r.int(8, 70); return r.shuffle(dev.map(function (d) { return mu + d; }));
  }
  L1.sdBasic = function (r) {
    var n = r.pick([5, 6, 8]), data = devData(r, n), mu = meanF(data), va = varF(data);
    var mx = Math.max.apply(null, data), mn = Math.min.apply(null, data);
    var dev = hxDev(data, Fr.toNum(mu)), sq = dev.map(function (d) { return d * d; }), ss = sumArr(sq);
    return { q: '某組資料為 ' + T(listTex(data)) + '。求 (1) 全距　(2) 算術平均數　(3) 變異數與標準差。',
             a: '(1) ' + T(String(mx - mn)) + '　(2) ' + T('\\mu=' + dec(mu)) + '　(3) ' + T('\\sigma^2=' + dec(va)) + '、' + T('\\sigma=' + sqrtBoth(va)),
             h: '全距 ' + T('=' + mx + '-' + mn) + '；平均 ' + T('\\mu=\\dfrac{' + sumArr(data) + '}{' + n + '}=' + dec(mu)) + '；偏差依序為 ' + T(listTex(dev)) + '（總和必為 $0$，可當檢查），偏差平方和 ' + T('=' + sq.join('+') + '=' + ss) + ' ⟹ ' + T('\\sigma^2=\\dfrac{' + ss + '}{' + n + '}') + '。',
             p: { data: data, ans: { range: mx - mn, mu: fr2(mu), var: fr2(va) } } };
  };
  L1.sdFromSums = function (r) {
    var n = r.pick([5, 6, 8, 10, 12]), data = devData(r, n), sx = sumArr(data), sxx = sumArr(data.map(function (v) { return v * v; }));
    var mu = meanF(data), va = varF(data);
    return { q: '已知 ' + T(String(n)) + ' 筆資料滿足 ' + T('\\displaystyle\\sum_{i=1}^{' + n + '}x_i=' + sx) + ' 且 ' + T('\\displaystyle\\sum_{i=1}^{' + n + '}x_i^2=' + sxx) + '。求此組資料的平均數與標準差。',
             a: T('\\mu=' + dec(mu)) + '、' + T('\\sigma^2=\\dfrac{' + sxx + '}{' + n + '}-' + (mu.d === 1 ? mu.n + '^2' : '\\left(' + Fr.tex(mu, true) + '\\right)^2') + '=' + dec(va)) + '、' + T('\\sigma=' + sqrtBoth(va)),
             h: '先求平均 ' + T('\\mu=\\dfrac{' + sx + '}{' + n + '}=' + dec(mu)) + '；再用「平方的平均減平均的平方」' + T('\\sigma^2=\\dfrac{\\sum x_i^2}{n}-\\mu^2=\\dfrac{' + sxx + '}{' + n + '}-' + dec(mu) + '^2') + '，不必知道每一筆是多少。',
             p: { n: n, sx: sx, sxx: sxx, ans: { mu: fr2(mu), var: fr2(va) } } };
  };
  L1.sumSqFromStats = function (r) {
    var n = r.pick([5, 8, 10, 12, 15, 20]), mu = r.int(5, 60), sg = r.int(2, 12), a = mu + r.pick([-5, -4, -3, -2, 2, 3, 4, 5]); if (a === 0) a = 10;   /* a=0 會寫成 (x_i-0)^2，而且兩小題同答案 */
    var s2 = n * (sg * sg + mu * mu), sa = n * sg * sg + n * (mu - a) * (mu - a);
    return { q: '某 ' + T(String(n)) + ' 筆資料的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。求 (1) ' + T('\\displaystyle\\sum_{i=1}^{' + n + '}x_i^2') + '　(2) ' + T('\\displaystyle\\sum_{i=1}^{' + n + '}(x_i-' + a + ')^2') + '。',
             a: '(1) ' + T(n + '(' + sg + '^2+' + mu + '^2)=' + s2) + '　(2) ' + T(n + '\\cdot' + sg + '^2+' + n + '(' + mu + '-' + a + ')^2=' + sa),
             h: '(1) ' + T('\\sum x_i^2=n(\\sigma^2+\\mu^2)=' + n + '(' + sg + '^2+' + mu + '^2)') + '；(2) 拆成「對平均的平方和」加上「平均離 ' + T(String(a)) + ' 有多遠」：' + T('\\sum(x_i-' + a + ')^2=n\\sigma^2+n(\\mu-' + a + ')^2=' + n + '\\times' + (sg * sg) + '+' + n + '\\times' + ((mu - a) * (mu - a))) + '。',
             p: { n: n, mu: mu, sg: sg, a: a, ans: { sumsq: s2, shifted: sa } } };
  };
  L1.addOne = function (r) {
    var n = r.pick([9, 14, 15, 19, 20, 24, 29]), mu = r.int(50, 80), sg = r.pick([3, 4, 5, 6, 8, 10]), kind = r.int(0, 1);
    var d = kind === 0 ? 0 : r.pick([-15, -12, -10, 10, 12, 15, 20]), v = mu + d;
    var mu2 = F(n * mu + v, n + 1), var2 = Fr.div(Fr.add(F(n * sg * sg), F(n * d * d, n + 1)), F(n + 1));
    return { q: '某組資料共 ' + T(String(n)) + ' 筆，平均數 ' + T(String(mu)) + '、標準差 ' + T(String(sg)) + '。若新增一筆資料 ' + T(String(v)) + (kind === 0 ? '（恰等於平均數）' : '') + '，求新資料的平均數與變異數。',
             a: T('\\mu\'=' + dec(mu2)) + '、' + T('\\sigma\'^2=' + dec(var2)) + (kind === 0 ? '（變小了：加入一筆等於平均的資料，標準差<b>會變小</b>）' : ''),
             h: '原平方和 $=n\\sigma^2=' + (n * sg * sg) + '$。新平均先算；對新平均的平方和 $=n\\sigma^2+n(\\mu-\\mu\')^2+(v-\\mu\')^2$，再除以 $n+1$。',
             p: { n: n, mu: mu, sg: sg, v: v, ans: { mu2: fr2(mu2), var2: fr2(var2) } } };
  };
  L1.mergeTwo = function (r) {
    var n1 = r.pick([10, 12, 15, 20, 24, 25, 30]), n2 = r.pick([10, 12, 15, 20, 24, 25, 30]);
    var m1 = r.int(55, 85), m2 = r.int(55, 85), s1 = r.pick([4, 5, 6, 8, 10, 12]), s2 = r.pick([4, 5, 6, 8, 10, 12]);
    if (m1 === m2) m2 += 5;
    var mu = F(n1 * m1 + n2 * m2, n1 + n2);
    var va = Fr.div(Fr.add(Fr.mul(F(n1), Fr.add(F(s1 * s1), Fr.mul(Fr.sub(F(m1), mu), Fr.sub(F(m1), mu)))), Fr.mul(F(n2), Fr.add(F(s2 * s2), Fr.mul(Fr.sub(F(m2), mu), Fr.sub(F(m2), mu))))), F(n1 + n2));
    return { q: '甲組 ' + T(String(n1)) + ' 人平均 ' + T(String(m1)) + ' 分、標準差 ' + T(String(s1)) + ' 分；乙組 ' + T(String(n2)) + ' 人平均 ' + T(String(m2)) + ' 分、標準差 ' + T(String(s2)) + ' 分。求兩組合併後 ' + T(String(n1 + n2)) + ' 人的平均數與變異數。',
             a: T('\\mu=' + dec(mu)) + '、' + T('\\sigma^2=' + dec(va)) + '（' + T('\\sigma=' + sqrtBoth(va)) + '）',
             h: '兩步：先用人數加權算合併平均 ' + T('\\mu=\\dfrac{' + n1 + '(' + m1 + ')+' + n2 + '(' + m2 + ')}{' + (n1 + n2) + '}=' + dec(mu)) + '；再套 ' + T('\\sigma^2=\\dfrac{' + n1 + '[' + (s1 * s1) + '+(' + m1 + '-\\mu)^2]+' + n2 + '[' + (s2 * s2) + '+(' + m2 + '-\\mu)^2]}{' + (n1 + n2) + '}') + '。',
             p: { n1: n1, m1: m1, s1: s1, n2: n2, m2: m2, s2: s2, ans: { mu: fr2(mu), var: fr2(va) } } };
  };

  /* ── §1-4 線性變換與標準化 ── */
  L1.linearTrans = function (r) {
    var mu = r.int(20, 80), sg = r.pick([3, 4, 5, 6, 8, 10, 12]);
    var a = r.pick([F(2), F(3), F(-2), F(-1), F(1, 2), F(3, 2), F(-1, 2), F(4, 5), F(6, 5)]), b = r.nz(-20, 40);
    var muy = Fr.add(Fr.mul(a, F(mu)), F(b)), sgy = Fr.mul(Fr.abs(a), F(sg)), vy = Fr.mul(sgy, sgy);
    var ax = Fr.eq(a, F(1)) ? '' : (Fr.eq(a, F(-1)) ? '-' : dec(a)), aa = Fr.abs(a);
    return { q: '某組資料 ' + T('x') + ' 的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。令 ' + T('y=' + ax + 'x' + (b > 0 ? '+' + b : String(b))) + '，求 ' + T('y') + ' 的平均數、標準差與變異數。',
             a: T('\\mu_y=' + dec(muy)) + '、' + T('\\sigma_y=' + dec(sgy)) + '、' + T('\\sigma_y^2=' + dec(vy)),
             h: T('\\mu_y=a\\mu_x+b=' + ax + '(' + mu + ')' + (b > 0 ? '+' + b : String(b))) + '；' + (Fr.eq(aa, F(1)) ? T('\\sigma_y=\\sigma_x=' + sg) + '（' + T('|a|=1') + '，平移不改變標準差）' : T('\\sigma_y=|a|\\sigma_x=' + dec(aa) + '\\times' + sg) + '（平移不改變標準差，係數要取絕對值）') + '，變異數是標準差的平方。',
             p: { mu: mu, sg: sg, a: fr2(a), b: b, ans: { mu: fr2(muy), sg: fr2(sgy) } } };
  };
  L1.inverseTrans = function (r) {
    var a = r.pick([F(1, 2), F(3, 5), F(4, 5), F(3, 4), F(6, 5), F(3, 2), F(2)]);
    var s1 = a.d * r.pick([2, 3, 4, 5]), mu1 = r.int(35, 60), b = r.int(8, 40);
    var s = r.int(20, 90), av = Fr.toNum(a);          /* 成績要落在 0～100：依序壓 μ_x、b、s（rng 取用順序不變） */
    if (av * mu1 > 80) mu1 = Math.floor(80 / av) - (mu1 % 5);
    if (av * mu1 + b > 90) b = Math.floor(90 - av * mu1);
    if (av * s + b > 100) s = Math.floor((100 - b) / av);
    var s2 = Fr.mul(a, F(s1)), mu2 = Fr.add(Fr.mul(a, F(mu1)), F(b)), y = Fr.add(Fr.mul(a, F(s)), F(b));
    return { q: '老師把全班成績依 ' + T('y=ax+b') + '（' + T('a\\gt0') + '）調整後，平均數由 ' + T(String(mu1)) + ' 變成 ' + T(dec(mu2)) + '、標準差由 ' + T(String(s1)) + ' 變成 ' + T(dec(s2)) + '。(1) 求 ' + T('a') + ' 與 ' + T('b') + '。　(2) 原本考 ' + T(String(s)) + ' 分的同學，調整後是幾分？',
             a: '(1) ' + T('a=\\dfrac{' + dec(s2) + '}{' + s1 + '}=' + dec(a)) + '、' + T('b=' + dec(mu2) + '-' + dec(a) + '(' + mu1 + ')=' + b) + '　(2) ' + T(dec(y)) + ' 分',
             h: '標準差只跟 ' + T('a') + ' 有關：' + T('a=\\dfrac{\\sigma_y}{\\sigma_x}=\\dfrac{' + dec(s2) + '}{' + s1 + '}') + '；再用 ' + T('\\mu_y=a\\mu_x+b') + '，把 ' + T(dec(mu2) + '=a(' + mu1 + ')+b') + ' 解出 ' + T('b') + '；第 (2) 小題把 ' + T('x=' + s) + ' 代進 ' + T('y=ax+b') + '。',
             p: { mu1: mu1, s1: s1, mu2: fr2(mu2), s2: fr2(s2), s: s, ans: { a: fr2(a), b: b, y: fr2(y) } } };
  };
  L1.zCompare = function (r) {
    var sub = r.shuffle(SUBJ).slice(0, 2), z1, z2, x1, x2, m1, m2, g1, g2, tries = 0;
    do {
      m1 = r.int(55, 80); m2 = r.int(55, 80); g1 = r.pick([4, 5, 8, 10, 12]); g2 = r.pick([4, 5, 8, 10, 12]);
      x1 = m1 + g1 * r.pick([-1, 1, 2]) + r.pick([0, g1 / 2 | 0]); x2 = m2 + g2 * r.pick([-1, 1, 2]) + r.pick([0, g2 / 2 | 0]);
      while (x1 > 100) x1 -= g1; while (x2 > 100) x2 -= g2;      /* 分數不超過 100 */
      z1 = F(x1 - m1, g1); z2 = F(x2 - m2, g2); tries++;
    } while (Fr.eq(z1, z2) && tries < 30);
    var better = Fr.lt(z2, z1) ? 0 : 1;
    return { q: NAMES[r.int(0, 5)] + '的' + sub[0] + '考 ' + T(String(x1)) + ' 分（全班平均 ' + T(String(m1)) + '、標準差 ' + T(String(g1)) + '），' + sub[1] + '考 ' + T(String(x2)) + ' 分（全班平均 ' + T(String(m2)) + '、標準差 ' + T(String(g2)) + '）。(1) 求兩科的標準化分數 ' + T('z') + '。　(2) 哪一科在班上的相對表現較好？',
             a: '(1) ' + sub[0] + ' ' + T('z=\\dfrac{' + x1 + '-' + m1 + '}{' + g1 + '}=' + dec(z1)) + '、' + sub[1] + ' ' + T('z=\\dfrac{' + x2 + '-' + m2 + '}{' + g2 + '}=' + dec(z2)) + '　(2) ' + sub[better] + '（' + T('z') + ' 較大）',
             h: T('z=\\dfrac{x-\\mu}{\\sigma}') + ' 量的是「高出平均幾個標準差」：' + sub[0] + ' 是 ' + T('\\dfrac{' + x1 + '-' + m1 + '}{' + g1 + '}') + '、' + sub[1] + ' 是 ' + T('\\dfrac{' + x2 + '-' + m2 + '}{' + g2 + '}') + '，算出來再比大小；直接比原始分數沒有意義。',
             p: { x1: x1, m1: m1, g1: g1, x2: x2, m2: m2, g2: g2, ans: { z1: fr2(z1), z2: fr2(z2), better: better } } };
  };
  L1.zInverse = function (r) {
    var mu = r.int(55, 80), sg = r.pick([4, 5, 6, 8, 10, 12]), kind = r.int(0, 1);
    if (kind === 0) {
      var z = r.pick([F(-2), F(-3, 2), F(-1), F(-1, 2), F(1, 2), F(1), F(3, 2), F(2), F(5, 2)]); if (mu + Fr.toNum(z) * sg > 100) z = F(-z.n, z.d);   /* 原始分數不超過 100 */
      var x = Fr.add(F(mu), Fr.mul(z, F(sg)));
      return { q: '某科成績的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。某生的標準化分數 ' + T('z=' + dec(z)) + '，求他的原始分數。',
               a: T('x=' + mu + '+(' + dec(z) + ')(' + sg + ')=' + dec(x)) + ' 分',
               h: '由 ' + T('z=\\dfrac{x-\\mu}{\\sigma}') + ' 反解 ' + T('x=\\mu+z\\sigma=' + mu + '+(' + dec(z) + ')(' + sg + ')') + '。',
               p: { kind: 0, mu: mu, sg: sg, z: fr2(z), ans: fr2(x) } };
    }
    var xv = mu + sg * r.pick([-2, -1, 1, 2]) + r.pick([0, 0, sg / 2 | 0, -(sg / 2 | 0)]); while (xv > 100) xv -= sg; var zz = F(xv - mu, sg);
    return { q: '某科成績的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。考 ' + T(String(xv)) + ' 分的同學，標準化分數 ' + T('z') + ' 是多少？標準化之後全班成績的平均數與標準差各是多少？',
             a: T('z=\\dfrac{' + xv + '-' + mu + '}{' + sg + '}=' + dec(zz)) + '；標準化後平均 ' + T('0') + '、標準差 ' + T('1'),
             h: T('z=\\dfrac{x-\\mu}{\\sigma}=\\dfrac{' + xv + '-' + mu + '}{' + sg + '}') + '；任何一組資料標準化後都是 ' + T('\\mu_z=0') + '、' + T('\\sigma_z=1') + '。',
             p: { kind: 1, mu: mu, sg: sg, x: xv, ans: fr2(zz) } };
  };
  L1.tScore = function (r) {
    var mu = r.int(55, 75), sg = r.pick([4, 5, 8, 10, 12, 15]), kind = r.int(0, 1);
    if (kind === 0) {
      var s = mu + sg * r.pick([-2, -1, 1, 2]) + r.pick([0, sg / 2 | 0, -(sg / 2 | 0)]); while (s > 100) s -= sg; var Tv = Fr.add(F(50), Fr.mul(F(10), F(s - mu, sg)));
      return { q: T('T') + ' 分數定義為 ' + T('T=50+10\\cdot\\dfrac{S-\\mu}{\\sigma}') + '。某科平均 ' + T(String(mu)) + ' 分、標準差 ' + T(String(sg)) + ' 分，某生考 ' + T(String(s)) + ' 分，求他的 ' + T('T') + ' 分數。',
               a: T('T=50+10\\cdot\\dfrac{' + s + '-' + mu + '}{' + sg + '}=' + dec(Tv)),
               h: '先算 ' + T('z=\\dfrac{S-\\mu}{\\sigma}=\\dfrac{' + s + '-' + mu + '}{' + sg + '}') + '，再 ' + T('T=50+10z') + '：' + T('T') + ' 分數就是把 ' + T('z') + ' 放大 $10$ 倍後搬到 $50$。',
               p: { kind: 0, mu: mu, sg: sg, s: s, ans: fr2(Tv) } };
    }
    var Tg = r.pick([30, 35, 40, 45, 55, 60, 65, 70, 75]); if (mu + (Tg - 50) / 10 * sg > 100) Tg = 100 - Tg;   /* 原始成績不超過 100 */
    var S = Fr.add(F(mu), Fr.mul(F(Tg - 50, 10), F(sg)));
    return { q: T('T') + ' 分數定義為 ' + T('T=50+10\\cdot\\dfrac{S-\\mu}{\\sigma}') + '。某科平均 ' + T(String(mu)) + ' 分、標準差 ' + T(String(sg)) + ' 分。' + T('T') + ' 分數為 ' + T(String(Tg)) + ' 的同學，原始成績是幾分？',
             a: T('z=\\dfrac{' + Tg + '-50}{10}=' + dec(F(Tg - 50, 10))) + ' ⟹ ' + T('S=' + mu + '+(' + dec(F(Tg - 50, 10)) + ')(' + sg + ')=' + dec(S)) + ' 分',
             h: '由 ' + T('T') + ' 反推 ' + T('z=\\dfrac{T-50}{10}=\\dfrac{' + Tg + '-50}{10}') + '，再 ' + T('S=\\mu+z\\sigma=' + mu + '+z(' + sg + ')') + '。',
             p: { kind: 1, mu: mu, sg: sg, T: Tg, ans: fr2(S) } };
  };

  /* ── §1-5 平均成長率 ── */
  var GROW2 = [[60, -10, 20], [80, -20, 20], [-20, 80, 20], [44, 0, 20], [21, 0, 10], [80, 25, 50], [150, -10, 50], [200, -25, 50], [125, 0, 50], [69, 0, 30], [160, -35, 30], [96, 21, 54], [10, 10, 10], [25, 25, 25], [-40, -40, -40], [-20, -20, -20], [50, -4, 20], [-4, 50, 20], [92, -25, 20], [-25, 92, 20], [140, -40, 20], [-40, 140, 20], [100, -28, 20], [-28, 100, 20], [-19, 0, -10], [0, -19, -10], [-36, 0, -20], [-51, 0, -30], [30, 30, 30], [40, 40, 40], [-30, -30, -30], [15, 15, 15]];
  var GROW3 = [[8, 25, 28, 20], [60, 20, -10, 20], [50, 28, -10, 20], [60, 35, -20, 20], [-2, 12, 28, 12], [10, 21, 0, 10], [80, 25, 50, 50], [170, 25, 0, 50], [44, 20, 0, 20], [20, 20, 20, 20], [-10, -10, -10, -10], [25, 8, 28, 20], [28, 25, 8, 20], [8, 28, 25, 20], [25, 28, 8, 20], [28, 8, 25, 20], [20, 44, 0, 20], [0, 44, 20, 20], [44, 0, 20, 20], [21, 0, 10, 10], [0, 10, 21, 10], [10, 0, 21, 10], [20, -10, 60, 20], [-10, 60, 20, 20], [28, -10, 50, 20], [-10, 50, 28, 20], [35, -20, 60, 20], [25, 0, 170, 50], [0, 170, 25, 50], [30, 30, 30, 30], [15, 15, 15, 15], [-20, -20, -20, -20], [12, 28, -2, 12], [28, -2, 12, 12]];
  L1.growthRate = function (r) {
    var row = r.pick(r.int(0, 1) ? GROW2 : GROW3), rates = row.slice(0, row.length - 1), g = row[row.length - 1];
    var item = r.pick(['某商品的價格', '某公司的營收', '某城市的人口', '某股票的價格', '某工廠的產量', '某網站的瀏覽量', '某社團的人數', '某地區的用電量']);
    var txt = rates.map(function (v) { return T((v < 0 ? '-' : '') + Math.abs(v) + '\\%'); }).join('、');
    var prod = rates.map(function (v) { return '(1' + (v < 0 ? '-' : '+') + dec(F(Math.abs(v), 100)) + ')'; }).join('');
    var pf = F(1); rates.forEach(function (v) { pf = Fr.mul(pf, F(100 + v, 100)); });
    return { q: item + '連續 ' + T(String(rates.length)) + ' 年的成長率依序為 ' + txt + '。求這 ' + T(String(rates.length)) + ' 年的平均成長率。',
             a: T('(1+\\bar r)^' + rates.length + '=' + prod + '=' + dec(pf) + '=(' + dec(F(100 + g, 100)) + ')^' + rates.length) + ' ⟹ ' + T('\\bar r=' + (g < 0 ? '-' : '') + Math.abs(g) + '\\%'),
             h: '成長率要用「乘」的：' + T('(1+\\bar r)^' + rates.length + '=' + prod) + '，右邊乘出來恰好會是某個數的 ' + T(String(rates.length)) + ' 次方——不能把成長率直接平均。',
             p: { rates: rates, ans: g } };
  };
  var GROWT = [[100, 121, 2, 10], [1000, 1331, 3, 10], [100, 144, 2, 20], [200, 288, 2, 20], [500, 720, 2, 20], [1000, 1728, 3, 20], [500, 864, 3, 20], [400, 625, 2, 25], [800, 1250, 2, 25], [512, 1000, 3, 25], [100, 225, 2, 50], [400, 900, 2, 50], [200, 675, 3, 50], [400, 1350, 3, 50], [100, 64, 2, -20], [500, 320, 2, -20], [1000, 512, 3, -20], [100, 81, 2, -10], [1000, 729, 3, -10], [400, 196, 2, -30], [1000, 343, 3, -30], [400, 484, 2, 10], [2000, 2662, 3, 10], [250, 360, 2, 20], [125, 216, 3, 20], [1600, 2500, 2, 25], [800, 1800, 2, 50], [160, 540, 3, 50], [100, 169, 2, 30], [1000, 2197, 3, 30], [250, 490, 2, 40], [500, 1372, 3, 40], [500, 1280, 2, 60], [1600, 900, 2, -25], [2500, 900, 2, -40], [400, 100, 2, -50]];
  L1.growthTotal = function (r) {
    var row = r.pick(GROWT), A = row[0], B = row[1], n = row[2], g = row[3], kind = r.int(0, 1);
    var item = r.pick(['某商品的價格', '某地區的房價指數', '某公司的年營收（萬元）', '某社團的人數']);
    var q = kind === 0
      ? item + '從 ' + T(String(A)) + ' 經過 ' + T(String(n)) + ' 次調整後變成 ' + T(String(B)) + '。求平均每次的成長率。'
      : item + '經過 ' + T(String(n)) + ' 年後變成原來的 ' + T(dec(F(B, A))) + ' 倍。求平均每年的成長率。';
    return { q: q, a: T('(1+\\bar r)^' + n + '=\\dfrac{' + B + '}{' + A + '}=' + dec(F(B, A)) + '=(' + dec(F(100 + g, 100)) + ')^' + n) + ' ⟹ ' + T('\\bar r=' + (g < 0 ? '-' : '') + Math.abs(g) + '\\%'),
             h: '只看首尾：' + T('(1+\\bar r)^' + n + '=\\dfrac{\\text{末}}{\\text{初}}=\\dfrac{' + B + '}{' + A + '}') + '，開 ' + T(String(n)) + ' 次方根；比值小於 $1$ 就是負成長。',
             p: { A: A, B: B, n: n, ans: g } };
  };

  /* ── §2-1 相關係數 ── */
  L1.corrData = function (r) {
    var d = makeXY(r, false);
    var dx = hxDev(d.x, d.mx), dy = hxDev(d.y, d.my);
    return { q: '五筆二維資料 ' + T('(x,y)') + ' 為 ' + T(pairsTex(d.x, d.y)) + '。求 ' + T('x') + ' 與 ' + T('y') + ' 的相關係數 ' + T('r') + '。',
             a: T('\\mu_x=' + d.mx + '、\\mu_y=' + d.my) + '；' + T('S_{xx}=' + d.sxx + '、S_{yy}=' + d.syy + '、S_{xy}=' + d.sxy) + ' ⟹ ' + T('r=\\dfrac{' + d.sxy + '}{\\sqrt{' + d.sxx + '\\times' + d.syy + '}}=' + dec(d.r)),
             h: '先算兩個平均 ' + T('\\mu_x=' + d.mx) + '、' + T('\\mu_y=' + d.my) + '，把兩排偏差寫出來：' + T('x') + ' 的偏差 ' + T(listTex(dx)) + '、' + T('y') + ' 的偏差 ' + T(listTex(dy)) + '；再套 ' + T('r=\\dfrac{\\sum(x_i-\\mu_x)(y_i-\\mu_y)}{\\sqrt{\\sum(x_i-\\mu_x)^2\\sum(y_i-\\mu_y)^2}}') + '，段考的數字一定開得出來。',
             p: { x: d.x, y: d.y, ans: fr2(d.r) } };
  };
  L1.corrSums = function (r) {
    var d = makeXY(r, false), sx = sumArr(d.x), sy = sumArr(d.y), sxx = sumArr(d.x.map(function (v) { return v * v; })), syy = sumArr(d.y.map(function (v) { return v * v; }));
    var sxy = 0; for (var i = 0; i < 5; i++) sxy += d.x[i] * d.y[i];
    return { q: '有 ' + T('5') + ' 組資料 ' + T('(x_i,y_i)') + '，已知 ' + T('\\sum x_i=' + sx + ',\\ \\sum x_i^2=' + sxx + ',\\ \\sum y_i=' + sy + ',\\ \\sum y_i^2=' + syy + ',\\ \\sum x_iy_i=' + sxy) + '。求相關係數 ' + T('r') + '。',
             a: T('S_{xx}=' + sxx + '-\\dfrac{' + sx + '^2}{5}=' + d.sxx + '、S_{yy}=' + syy + '-\\dfrac{' + sy + '^2}{5}=' + d.syy + '、S_{xy}=' + sxy + '-\\dfrac{' + sx + '\\cdot' + sy + '}{5}=' + d.sxy) + ' ⟹ ' + T('r=' + dec(d.r)),
             h: '三個都是「減掉平均的貢獻」：' + T('S_{xx}=\\sum x^2-\\dfrac{(\\sum x)^2}{n}=' + sxx + '-\\dfrac{' + sx + '^2}{5}') + '、' + T('S_{yy}=' + syy + '-\\dfrac{' + sy + '^2}{5}') + '、' + T('S_{xy}=\\sum xy-\\dfrac{\\sum x\\sum y}{n}=' + sxy + '-\\dfrac{' + sx + '\\cdot' + sy + '}{5}') + '，最後代 ' + T('r=\\dfrac{S_{xy}}{\\sqrt{S_{xx}S_{yy}}}') + '。',
             p: { n: 5, sx: sx, sxx: sxx, sy: sy, syy: syy, sxy: sxy, ans: fr2(d.r) } };
  };
  L1.corrTransform = function (r) {
    var rr = r.pick([F(3, 5), F(-3, 5), F(4, 5), F(-4, 5), F(1, 2), F(-1, 2), F(3, 4), F(-3, 4), F(9, 10), F(-9, 10), F(7, 10), F(-7, 10)]);
    var pairs = [], anss = [], texs = [], prods = [];
    for (var i = 0; i < 3; i++) {
      var a = r.pick([2, 3, -1, -2, -3, 5]), c = r.pick([1, 2, 3, -1, -2, -4]), b = r.nz(-9, 9), dd = r.nz(-9, 9);
      pairs.push([a, c]); prods.push(a * c);
      var rv = a * c > 0 ? rr : F(-rr.n, rr.d); anss.push(rv);
      texs.push('(' + (a === 1 ? '' : a === -1 ? '-' : a) + 'x' + (b > 0 ? '+' + b : b) + ',\\ ' + (c === 1 ? '' : c === -1 ? '-' : c) + 'y' + (dd > 0 ? '+' + dd : dd) + ')');
    }
    return { q: '已知 ' + T('x') + ' 與 ' + T('y') + ' 的相關係數為 ' + T(dec(rr)) + '。求下列各組新資料的相關係數：(1) ' + T(texs[0]) + '　(2) ' + T(texs[1]) + '　(3) ' + T(texs[2]),
             a: '(1) ' + T(dec(anss[0])) + '　(2) ' + T(dec(anss[1])) + '　(3) ' + T(dec(anss[2])),
             h: T('(ax+b,\\ cy+d)') + ' 的相關係數只看 ' + T('ac') + ' 的正負（平移 ' + T('b') + '、' + T('d') + ' 完全沒影響）：本題三組的 ' + T('ac') + ' 依序是 ' + T(prods.join(',\\ ')) + '，' + T('ac\\gt0') + ' 不變、' + T('ac\\lt0') + ' 變號。',
             p: { r: fr2(rr), ac: pairs, ans: anss.map(fr2) } };
  };
  L1.corrPerfect = function (r) {
    var a = r.pick([F(2), F(-2), F(3), F(-3), F(1, 2), F(-1, 2), F(3, 2), F(-3, 4), F(4, 5)]), b = r.nz(-10, 20), mu = r.int(10, 60), sg = r.pick([2, 4, 5, 6, 8, 10]);
    var muy = Fr.add(Fr.mul(a, F(mu)), F(b)), sgy = Fr.mul(Fr.abs(a), F(sg)), rv = a.n > 0 ? 1 : -1;
    return { q: '設 ' + T('n') + ' 筆二維資料滿足 ' + T('y_i=' + (Fr.eq(a, F(1)) ? '' : dec(a)) + 'x_i' + (b > 0 ? '+' + b : String(b))) + '，且 ' + T('x') + ' 的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。求 ' + T('y') + ' 的平均數、標準差、' + T('x') + ' 與 ' + T('y') + ' 的相關係數，以及 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線。',
             a: T('\\mu_y=' + dec(muy)) + '、' + T('\\sigma_y=' + dec(sgy)) + '、' + T('r=' + rv) + '、最適直線就是 ' + T(lineTex(a, F(b))),
             h: '所有點都在同一條直線上 ⟹ ' + T('r=\\pm1') + '（正負看斜率 ' + T(dec(a)) + '），最適直線就是 ' + T(lineTex(a, F(b))) + ' 本身；' + T('\\mu_y=' + (Fr.eq(a, F(1)) ? String(mu) : dec(a) + '(' + mu + ')') + (b > 0 ? '+' + b : String(b))) + '、' + T('\\sigma_y=|' + dec(a) + '|\\times' + sg) + '。',
             p: { a: fr2(a), b: b, mu: mu, sg: sg, ans: { mu: fr2(muy), sg: fr2(sgy), r: rv } } };
  };

  /* ── §2-2 最適直線 ── */
  L1.fitData = function (r) {
    var d = makeXY(r, false);
    return { q: '五筆二維資料 ' + T('(x,y)') + ' 為 ' + T(pairsTex(d.x, d.y)) + '。求 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線（以 ' + T('y=ax+b') + ' 作答）。',
             a: T('\\mu_x=' + d.mx + '、\\mu_y=' + d.my + '、S_{xx}=' + d.sxx + '、S_{xy}=' + d.sxy) + ' ⟹ 斜率 ' + T('a=\\dfrac{' + d.sxy + '}{' + d.sxx + '}=' + dec(d.slope)) + '，直線 ' + T(lineTex(d.slope, d.icpt)),
             h: '斜率 ' + T('=\\dfrac{S_{xy}}{S_{xx}}=' + hxDiv(d.sxy, d.sxx)) + '，再用「必過重心 ' + T('(' + d.mx + ',' + d.my + ')') + '」寫出直線：' + T('y-' + d.my + '=a(x-' + d.mx + ')') + '。',
             p: { x: d.x, y: d.y, ans: { a: fr2(d.slope), b: fr2(d.icpt) } } };
  };
  L1.fitStats = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(3, 4), F(1, 2), F(-3, 5), F(-4, 5), F(-1, 2), F(7, 10)]);
    var sx = r.pick([4, 5, 8, 10]), sy = r.pick([4, 6, 8, 10, 12]), mx = r.int(40, 70), my = r.int(40, 80);
    var slope = Fr.mul(rr, F(sy, sx)), icpt = Fr.sub(F(my), Fr.mul(slope, F(mx))), x0 = mx + r.pick([-10, -5, 5, 10, 20]), yh = Fr.add(F(my), Fr.mul(slope, F(x0 - mx)));
    return { q: '已知 ' + T('\\mu_x=' + mx + '、\\mu_y=' + my + '、\\sigma_x=' + sx + '、\\sigma_y=' + sy) + '，相關係數 ' + T('r=' + dec(rr)) + '。(1) 求 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線。　(2) 當 ' + T('x=' + x0) + ' 時，' + T('y') + ' 的預測值是多少？',
             a: '(1) 斜率 ' + T('=r\\dfrac{\\sigma_y}{\\sigma_x}=' + dec(rr) + '\\times\\dfrac{' + sy + '}{' + sx + '}=' + dec(slope)) + '，過 ' + T('(' + mx + ',' + my + ')') + ' ⟹ ' + T(lineTex(slope, icpt)) + '　(2) ' + T('\\hat y=' + my + '+' + (Fr.eq(slope, F(1)) ? '' : slope.n < 0 ? '(' + dec(slope) + ')' : dec(slope)) + '(' + x0 + '-' + mx + ')=' + dec(yh)),
             h: '斜率 ' + T('=r\\dfrac{\\sigma_y}{\\sigma_x}=' + dec(rr) + '\\times\\dfrac{' + sy + '}{' + sx + '}') + '，直線必過重心 ' + T('(' + mx + ',' + my + ')') + '；第 (2) 小題直接從重心出發 ' + T('\\hat y=' + my + '+\\text{斜率}\\times(' + x0 + '-' + mx + ')') + '。',
             p: { r: fr2(rr), sx: sx, sy: sy, mx: mx, my: my, x0: x0, ans: { a: fr2(slope), b: fr2(icpt), yh: fr2(yh) } } };
  };
  L1.fitCentroid = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(3, 4), F(1, 2), F(2, 5), F(-3, 5), F(-4, 5), F(-1, 2)]);
    var sx = r.pick([4, 5, 8, 10, 12]), sy = r.pick([4, 5, 6, 8, 10, 12]), a = Fr.mul(rr, F(sy, sx));
    var mx = r.int(40, 75), b = r.int(40, 85) - Math.round(Fr.toNum(a) * mx); if (b === 0) b = 1;   /* 先選英文平均（40～85 附近）再反推整數截距；舊版 b∈[-30,60] 會算出負的或破百的平均 */
    var my = Fr.add(Fr.mul(a, F(mx)), F(b));
    return { q: '某班數學成績 ' + T('x') + ' 的平均數為 ' + T(String(mx)) + '、標準差為 ' + T(String(sx)) + '；英文成績 ' + T('y') + ' 的標準差為 ' + T(String(sy)) + '。已知 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線為 ' + T(lineTex(a, F(b))) + '。(1) 求英文成績的平均數。　(2) 求兩科的相關係數 ' + T('r') + '。',
             a: '(1) 直線過重心 ⟹ ' + T('\\mu_y=' + (Fr.eq(a, F(1)) ? String(mx) : Fr.eq(a, F(-1)) ? '-' + mx : dec(a) + '(' + mx + ')') + (b > 0 ? '+' + b : b) + '=' + dec(my)) + '　(2) ' + T(dec(a) + '=r\\cdot\\dfrac{' + sy + '}{' + sx + '}') + ' ⟹ ' + T('r=' + dec(rr)),
             h: '兩個性質：① 直線必過 ' + T('(\\mu_x,\\mu_y)') + '，把 ' + T('x=' + mx) + ' 代進 ' + T(lineTex(a, F(b))) + ' 就得 ' + T('\\mu_y') + '；② 斜率 ' + T('=r\\dfrac{\\sigma_y}{\\sigma_x}') + '，由 ' + T(dec(a) + '=r\\cdot\\dfrac{' + sy + '}{' + sx + '}') + ' 反解 ' + T('r') + '。',
             p: { a: fr2(a), b: b, mx: mx, sx: sx, sy: sy, ans: { my: fr2(my), r: fr2(rr) } } };
  };
  L1.fitTransform = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(1, 2), F(7, 10), F(-3, 5), F(-1, 2)]), sx = r.pick([5, 10, 20]), sy = r.pick([4, 8, 10, 12, 20]), mx = r.int(40, 70), my = r.int(40, 80);
    var pr = r.pick([[2, 0], [1, 10], [1, -5], [2, 10], [F(1, 2), 0], [F(1, 2), 20]]), sr = r.pick([[1, 10], [2, 0], [F(1, 2), 30], [1, 20], [2, -10], [F(6, 5), 0]]);
    var p = typeof pr[0] === 'number' ? F(pr[0]) : pr[0], q = pr[1], s = typeof sr[0] === 'number' ? F(sr[0]) : sr[0], t = sr[1];
    var slope = Fr.mul(rr, F(sy, sx)), slope2 = Fr.mul(slope, Fr.div(s, p));
    var mx2 = Fr.add(Fr.mul(p, F(mx)), F(q)), my2 = Fr.add(Fr.mul(s, F(my)), F(t)), icpt2 = Fr.sub(my2, Fr.mul(slope2, mx2));
    function vt(c, k, v) { return (Fr.eq(c, F(1)) ? '' : dec(c)) + v + (k > 0 ? '+' + k : k < 0 ? String(k) : ''); }
    return { q: '已知 ' + T('\\mu_x=' + mx + '、\\sigma_x=' + sx + '、\\mu_y=' + my + '、\\sigma_y=' + sy + '、r=' + dec(rr)) + '。令 ' + T("x'=" + vt(p, q, 'x')) + '、' + T("y'=" + vt(s, t, 'y')) + '，求 ' + T("y'") + ' 對 ' + T("x'") + ' 的最適直線。',
             a: T("\\sigma_{x'}=" + dec(Fr.mul(Fr.abs(p), F(sx))) + "、\\sigma_{y'}=" + dec(Fr.mul(Fr.abs(s), F(sy))) + "、r'=" + dec(p.n * s.n > 0 ? rr : F(-rr.n, rr.d))) + ' ⟹ 斜率 ' + T(dec(slope2)) + '；過 ' + T('(' + dec(mx2) + ',' + dec(my2) + ')') + ' ⟹ ' + T(lineTex(slope2, icpt2).replace(/^y=/, "y'=").replace(/x/, "x'")),
             h: '線性變換後 ' + T("\\sigma_{x'}=|p|\\sigma_x") + '、' + T("\\sigma_{y'}=|s|\\sigma_y") + '，本題 ' + T('|p|=' + dec(Fr.abs(p))) + '、' + T('|s|=' + dec(Fr.abs(s))) + '、' + T('ps=' + dec(Fr.mul(p, s))) + '（決定 ' + T("r'") + ' 的正負）；新斜率 ' + T('=\\dfrac{s}{p}\\times\\text{舊斜率}') + '，新直線過新重心 ' + T('(' + dec(mx2) + ',' + dec(my2) + ')') + '。',
             p: { r: fr2(rr), sx: sx, sy: sy, mx: mx, my: my, p: fr2(p), q: q, s: fr2(s), t: t, ans: { a: fr2(slope2), b: fr2(icpt2) } } };
  };
  L1.stdFit = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(1, 2), F(7, 10), F(9, 10), F(2, 5), F(-3, 5), F(-4, 5), F(-1, 2), F(-7, 10), F(-9, 10), F(-2, 5)]);
    var c = r.pick([F(-2), F(-3, 2), F(-1), F(-1, 2), F(1, 2), F(1), F(3, 2), F(2), F(5, 2), F(-5, 2), F(4, 5), F(-4, 5)]);
    var yh = Fr.mul(rr, c);
    return { q: '某二維資料的相關係數為 ' + T('r=' + dec(rr)) + '。把 ' + T('x') + '、' + T('y') + ' 都標準化為 ' + T("x''") + '、' + T("y''") + '。(1) 求 ' + T("y''") + ' 對 ' + T("x''") + ' 的最適直線。　(2) 某筆資料的 ' + T("x''=" + dec(c)) + '，用此直線預測它的 ' + T("y''") + '。',
             a: '(1) ' + T("y''=" + dec(rr) + "x''") + '（過原點，斜率就是 ' + T('r') + '）　(2) ' + T("\\hat y''=" + dec(rr) + '\\times(' + dec(c) + ')=' + dec(yh)),
             h: '標準化後 ' + T('\\mu=0') + '、' + T('\\sigma=1') + ' ⟹ 斜率 ' + T("=r\\cdot\\dfrac{\\sigma_{y''}}{\\sigma_{x''}}=r=" + dec(rr)) + '，而且必過原點 ' + T('(0,0)') + '；第 (2) 小題把 ' + T("x''=" + dec(c)) + ' 代進去乘上 ' + T('r') + '。',
             p: { r: fr2(rr), c: fr2(c), ans: fr2(yh) } };
  };


  /* ═══════════════════════ L2 ═══════════════════════ */
  var L2 = {};

  /* 2-1 由迴歸直線反推缺失的資料（建中 113 下 多 3 型） */
  L2.regMissing = function (r) {
    var x1 = r.int(1, 4), gap = r.pick([2, 2, 4, 4, 6]), x2 = x1 + gap, xs = [x1, x2, x1, x2];
    var s = r.pick([F(-2), F(-1), F(-1, 2), F(1, 2), F(1), F(2), F(3, 2), F(-3, 2)]);
    var y1 = r.int(1, 9), yb = r.int(1, 9), K2 = Fr.mul(s, F(2 * gap));     // (a+y4)-(y1+yb) = 2·s·gap（gap 為偶數 ⟹ 整數）
    var sumRight = y1 + yb + K2.n / K2.d;                                    // a + y4
    if (sumRight < 2) { y1 += 2 - sumRight; sumRight = y1 + yb + K2.n / K2.d; }
    var a = Math.floor(sumRight / 2) + r.pick([-1, 0, 1, 2]), y4 = sumRight - a;
    if (a < 0) { a = 0; y4 = sumRight; } if (y4 < 0) { y4 = 0; a = sumRight; }
    var ys = [y1, a, yb, y4], mx = F(x1 + x2, 2), my = F(y1 + a + yb + y4, 4), c = Fr.sub(my, Fr.mul(s, mx));
    return { q: '已知兩變數 ' + T('x') + ' 與 ' + T('y') + ' 的四筆數據為 ' + T('x:\\ ' + xs.join(',\\ ')) + '；' + T('y:\\ ' + y1 + ',\\ a,\\ b,\\ ' + y4) + '，且用最小平方法求得 ' + T('y') + ' 對 ' + T('x') + ' 的迴歸直線為 ' + T(lineTex(s, c)) + '。求 ' + T('a') + '、' + T('b') + ' 與 ' + T('y') + ' 的平均數。',
             a: T('\\mu_x=' + dec(mx)) + ' 代入直線得 ' + T('\\mu_y=' + dec(my)) + ' ⟹ ' + T('a+b=' + (a + yb)) + '；斜率 ' + T('=\\dfrac{S_{xy}}{S_{xx}}') + ' 給 ' + T('a-b=' + (a - yb)) + ' ⟹ ' + T('a=' + a) + '、' + T('b=' + yb) + '、' + T('\\mu_y=' + dec(my)),
             h: '兩個條件、兩個未知數：① 直線必過 ' + T('(\\mu_x,\\mu_y)') + '，把 ' + T('\\mu_x=' + dec(mx)) + ' 代進 ' + T(lineTex(s, c)) + ' 得 ' + T('\\mu_y') + '，而四筆 ' + T('y') + ' 的總和 ' + T('=4\\mu_y') + ' 就給出 ' + T('a+b') + '；② 斜率 ' + T('=\\dfrac{S_{xy}}{S_{xx}}') + '，' + T('x') + ' 只取 ' + T(String(x1)) + ' 與 ' + T(String(x2)) + ' 兩個值，偏差是 $\\mp' + (gap / 2) + '$，展開後 ' + T('\\mu_y') + ' 會消掉，只剩 ' + T('a-b') + '。',
             p: { x: xs, y: ys, slope: fr2(s), icpt: fr2(c), ans: { a: a, b: yb, my: fr2(my) } } };
  };
  /* 2-2 由 r、迴歸直線與 y 的統計量反推 x 的平均與標準差（例題 30 型） */
  L2.regReverse = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(3, 4), F(1, 2), F(2, 5)]), sy = r.pick([4, 5, 6, 8, 10]), sx = r.pick([4, 5, 8, 10]);
    var s = Fr.mul(rr, F(sy, sx)), mx = r.int(40, 70), my = r.int(50, 85), b = Fr.sub(F(my), Fr.mul(s, F(mx)));
    return { q: '某班 ' + T('x') + '（數學）與 ' + T('y') + '（英文）成績的相關係數為 ' + T(dec(rr)) + '，' + T('y') + ' 對 ' + T('x') + ' 的最適直線為 ' + T(lineTex(s, b)) + '。已知英文的平均數為 ' + T(String(my)) + '、標準差為 ' + T(String(sy)) + '。求數學的平均數 ' + T('\\mu_x') + ' 與標準差 ' + T('\\sigma_x') + '。',
             a: '直線過重心：' + T(my + '=' + dec(s) + '\\mu_x' + (b.n >= 0 ? '+' : '') + dec(b)) + ' ⟹ ' + T('\\mu_x=' + mx) + '；斜率 ' + T(dec(s) + '=' + dec(rr) + '\\cdot\\dfrac{' + sy + '}{\\sigma_x}') + ' ⟹ ' + T('\\sigma_x=' + sx),
             h: '把 ' + T('\\mu_y=' + my) + ' 代進 ' + T(lineTex(s, b)) + ' 解出 ' + T('\\mu_x') + '；再用斜率 ' + T(dec(s) + '=' + dec(rr) + '\\cdot\\dfrac{' + sy + '}{\\sigma_x}') + ' 反解 ' + T('\\sigma_x') + '。',
             p: { r: fr2(rr), sy: sy, my: my, slope: fr2(s), icpt: fr2(b), ans: { mx: mx, sx: sx } } };
  };
  /* 2-3 兩條迴歸直線：y 對 x 與 x 對 y ⟹ 斜率相乘 = r²，交點 = 重心 */
  L2.regBothLines = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(1, 2), F(-3, 5), F(-4, 5), F(-1, 2)]), sx = r.pick([2, 4, 5, 10]), sy = r.pick([2, 4, 5, 10]);
    if (Fr.eq(Fr.abs(Fr.mul(rr, F(sy, sx))), F(1)) || Fr.eq(Fr.abs(Fr.mul(rr, F(sx, sy))), F(1))) sy = sx;   /* 斜率為 ±1 時答案會寫出 `1\times…` */
    var mx = r.int(20, 60), my = r.int(20, 80);
    var b1 = Fr.mul(rr, F(sy, sx)), c1 = Fr.sub(F(my), Fr.mul(b1, F(mx)));       // y = b1 x + c1
    var b2 = Fr.mul(rr, F(sx, sy)), c2 = Fr.sub(F(mx), Fr.mul(b2, F(my)));       // x = b2 y + c2
    var mulT = b1.n < 0 ? '(' + dec(b1) + ')\\times(' + dec(b2) + ')' : dec(b1) + '\\times' + dec(b2);
    return { q: '某二維數據中，' + T('y') + ' 對 ' + T('x') + ' 的最適直線為 ' + T(lineTex(b1, c1)) + '，' + T('x') + ' 對 ' + T('y') + ' 的最適直線為 ' + T(lineTex(b2, c2).replace(/^y=/, 'x=').replace(/x(?=[+\\-]|$)/, 'y')) + '。(1) 求 ' + T('(\\mu_x,\\mu_y)') + '。　(2) 求相關係數 ' + T('r') + '。',
             a: '(1) 兩直線都過重心，解聯立得 ' + T('(\\mu_x,\\mu_y)=(' + mx + ',' + my + ')') + '　(2) 兩斜率相乘 ' + T(mulT + '=r^2=' + dec(Fr.mul(rr, rr))) + '，且 ' + T('r') + ' 與斜率同號 ⟹ ' + T('r=' + dec(rr)),
             h: T('y') + ' 對 ' + T('x') + ' 的斜率是 ' + T('r\\dfrac{\\sigma_y}{\\sigma_x}') + '、' + T('x') + ' 對 ' + T('y') + ' 的斜率是 ' + T('r\\dfrac{\\sigma_x}{\\sigma_y}') + '，相乘恰為 ' + T('r^2') + '：本題 ' + T(mulT + '=r^2') + '；兩條線都通過 ' + T('(\\mu_x,\\mu_y)') + '，解聯立就是重心。',
             p: { b1: fr2(b1), c1: fr2(c1), b2: fr2(b2), c2: fr2(c2), ans: { mx: mx, my: my, r: fr2(rr) } } };
  };
  /* 2-4 換單位後的迴歸直線（中山女高 113 下 多 6／114 學測 A 12 型） */
  L2.regUnits = function (r) {
    var kind = r.int(0, 1), a = r.pick([F(2), F(3), F(5), F(1, 2), F(3, 2), F(5, 2), F(-2), F(-1, 2)]), b = r.nz(-30, 60);
    var p = r.pick([F(2), F(10), F(100), F(1, 10), F(1, 100), F(5, 2)]), q = r.pick([F(2), F(10), F(100), F(1, 10), F(1, 1000), F(11, 5)]);
    var a2, b2, ptxt, qtxt;
    if (kind === 0) { a2 = Fr.mul(a, Fr.div(q, p)); b2 = Fr.mul(q, F(b)); ptxt = 'u=' + dec(p) + 'x'; }
    else { a2 = Fr.mul(F(-1), Fr.mul(a, q)); b2 = Fr.mul(q, Fr.add(Fr.mul(a, F(100)), F(b))); ptxt = 'u=100-x'; p = F(-1); }
    qtxt = 'v=' + dec(q) + 'y';
    var lt = lineTex(a2, b2).replace(/^y=/, 'v=').replace(/x(?=[+\\-]|$)/, 'u');
    return { q: '某組二維數據 ' + T('(x,y)') + ' 的迴歸直線為 ' + T(lineTex(a, F(b))) + '。今將數據依 ' + T(ptxt) + '、' + T(qtxt) + ' 轉換為 ' + T('(u,v)') + '。求 ' + T('v') + ' 對 ' + T('u') + ' 的迴歸直線 ' + T("v=a'u+b'") + '，並判斷 ' + T('u') + ' 與 ' + T('v') + ' 的相關係數與原來相比是否改變。',
             a: T(lt) + '；' + (p.n * q.n > 0 ? '相關係數不變' : '相關係數變號（' + T('pq\\lt0') + '）'),
             h: '把 $x=' + (kind === 0 ? '\\frac{u}{' + dec(p) + '}' : '100-u') + '$、$y=\\frac{v}{' + dec(q) + '}$ 代回原直線整理即可；也可用「新斜率 $=$ 舊斜率 $\\times\\frac{q}{p}$、必過新重心」。',
             p: { a: fr2(a), b: b, kind: kind, p: fr2(p), q: fr2(q), ans: { a2: fr2(a2), b2: fr2(b2), rSame: p.n * q.n > 0 } } };
  };
  /* 2-5 由迴歸斜率反推 σ_y、μ_y（113 學測 A 9 型） */
  L2.corrFromSlope = function (r) {
    var rr = r.pick([F(1, 2), F(3, 5), F(3, 4), F(4, 5), F(2, 5)]), sy = r.pick([F(1), F(2), F(4), F(5), F(10), F(1, 2)]);
    var sx = r.pick([F(1, 2), F(3, 2), F(2), F(1, 5), F(3, 10), F(4)]), a = Fr.mul(rr, Fr.div(sy, sx));   /* σ_x=1 會寫出 \dfrac{\sigma_y}{1} */
    var mx = r.pick([F(5), F(6), F(52, 10), F(8), F(10), F(12)]), b = r.pick([F(-6, 10), F(4, 10), F(1), F(-2), F(3), F(-1, 2)]), my = Fr.add(Fr.mul(a, mx), b);
    if (Fr.toNum(my) < 2 * Fr.toNum(sy) + 2) { b = F(Math.max(1, Math.ceil(2 * Fr.toNum(sy) + 2 - Fr.toNum(Fr.mul(a, mx))))); my = Fr.add(Fr.mul(a, mx), b); }   /* 體重要為正：μ_y 至少 2σ_y+2（舊版會出現負的平均體重與 |-2.6--1.4|） */
    var px = Fr.add(mx, r.pick([F(4, 10), F(-4, 10), F(1), F(-1), F(1, 2)])), py = Fr.add(my, r.pick([F(-12, 10), F(12, 10), F(3, 2), F(-1, 2), F(2)]));
    var within = !Fr.lt(sy, Fr.abs(Fr.sub(py, my)));   // |py-my| ≤ σy
    return { q: '某物種身長 ' + T('x') + ' 與體重 ' + T('y') + ' 的相關係數為 ' + T(dec(rr)) + '，' + T('\\mu_x=' + dec(mx)) + '、' + T('\\sigma_x=' + dec(sx)) + '，' + T('y') + ' 對 ' + T('x') + ' 的迴歸直線為 ' + T(lineTex(a, b)) + '。(1) 求 ' + T('\\mu_y') + ' 與 ' + T('\\sigma_y') + '。　(2) 個體 ' + T('P(' + dec(px) + ',' + dec(py) + ')') + ' 的體重與 ' + T('\\mu_y') + ' 之差的絕對值是否超過一個標準差？',
             a: '(1) ' + T('\\mu_y=' + (Fr.eq(a, F(1)) ? dec(mx) : dec(a) + '(' + dec(mx) + ')') + (b.n >= 0 ? '+' : '') + dec(b) + '=' + dec(my)) + '；' + T(dec(a) + '=' + dec(rr) + '\\cdot\\dfrac{\\sigma_y}{' + dec(sx) + '}') + ' ⟹ ' + T('\\sigma_y=' + dec(sy)) + '　(2) ' + T('|' + dec(py) + '-' + dec(my) + '|=' + dec(Fr.abs(Fr.sub(py, my)))) + (within ? '，沒有超過' : '，超過了') + ' ' + T('\\sigma_y=' + dec(sy)),
             h: '重心在直線上 ⟹ 把 ' + T('\\mu_x=' + dec(mx)) + ' 代進 ' + T(lineTex(a, b)) + ' 就得 ' + T('\\mu_y') + '；再由斜率 ' + T(dec(a) + '=' + dec(rr) + '\\cdot\\dfrac{\\sigma_y}{' + dec(sx) + '}') + ' 反解 ' + T('\\sigma_y') + '，最後比 ' + T('|' + dec(py) + '-\\mu_y|') + ' 與 ' + T('\\sigma_y') + ' 的大小。',
             p: { r: fr2(rr), sx: fr2(sx), mx: fr2(mx), slope: fr2(a), icpt: fr2(b), px: fr2(px), py: fr2(py), ans: { my: fr2(my), sy: fr2(sy), within: within } } };
  };
  /* 2-6 新增恰在重心的一筆（例題 33 型） */
  L2.addCentroid = function (r) {
    var n = r.pick([9, 19, 24, 49, 99]), mx = r.int(50, 80), my = r.int(30, 70), sx = r.pick([2, 4, 5, 6, 10]), sy = r.pick([2, 3, 4, 5, 8]), rr = r.pick([F(3, 5), F(4, 5), F(1, 2), F(-3, 5), F(7, 10)]);
    var vx = F(n * sx * sx, n + 1), vy = F(n * sy * sy, n + 1);
    return { q: '某檢定 ' + T(String(n)) + ' 人的筆試 ' + T('x') + ' 與實作 ' + T('y') + ' 成績：' + T('\\mu_x=' + mx + '、\\sigma_x=' + sx + '、\\mu_y=' + my + '、\\sigma_y=' + sy + '、r=' + dec(rr)) + '。後來補登一位成績恰為 ' + T('(' + mx + ',' + my + ')') + ' 的考生。求新的 ' + T(String(n + 1)) + ' 筆資料的 ' + T('\\mu_x') + '、' + T('\\sigma_x^2') + '、' + T('\\sigma_y^2') + ' 與相關係數 ' + T('r') + '。',
             a: T('\\mu_x=' + mx) + '（不變）、' + T('\\sigma_x^2=\\dfrac{' + n + '\\times' + (sx * sx) + '}{' + (n + 1) + '}=' + dec(vx)) + '、' + T('\\sigma_y^2=' + dec(vy)) + '、' + T('r=' + dec(rr)) + '（不變：三個和 ' + T('S_{xx},S_{yy},S_{xy}') + ' 都沒有增加）',
             h: '新的一筆與重心重合 ⟹ 兩個平均不變、' + T('S_{xx},S_{yy},S_{xy}') + ' 三個和都沒有增加；只有分母由 ' + T(String(n)) + ' 變成 ' + T(String(n + 1)) + '，所以 ' + T('\\sigma_x^2=' + (sx * sx) + '\\times\\dfrac{' + n + '}{' + (n + 1) + '}') + '、' + T('\\sigma_y^2=' + (sy * sy) + '\\times\\dfrac{' + n + '}{' + (n + 1) + '}') + '，而 ' + T('r') + ' 的分子分母同時約掉 ' + T('n') + ' 所以不變。',
             p: { n: n, mx: mx, my: my, sx: sx, sy: sy, r: fr2(rr), ans: { vx: fr2(vx), vy: fr2(vy) } } };
  };
  /* 2-7 固定全距的整數資料，變異數的最小值（竹科實中 113 下 單 3 型） */
  L2.minVarRange = function (r) {
    var n = r.pick([5, 6, 7, 8]), R = r.int(6, 12), M = r.int(2020, 2030), best = null, bestArr = null;
    (function rec(start, left, acc) {
      if (left === 0) { var d = [0, R].concat(acc), v = varF(d); if (best === null || Fr.lt(v, best)) { best = v; bestArr = acc.slice(); } return; }
      for (var c = start; c <= R; c++) { acc.push(c); rec(c, left - 1, acc); acc.pop(); }
    })(0, n - 2, []);
    var arr = [M - R].concat(bestArr.map(function (c) { return M - R + c; })).concat([M]);
    return { q: '有一組皆為整數的 ' + T(String(n)) + ' 筆資料，其中最大值為 ' + T(String(M)) + '、全距為 ' + T(String(R)) + '。求此組資料變異數的最小可能值。',
             a: T('\\sigma^2_{\\min}=' + dec(best)) + '（例如 ' + T(listTex(arr)) + '）',
             h: '最小值必為 $' + (M - R) + '$。先平移成 $0$ 與 $' + R + '$ 兩端固定，其餘 $' + (n - 2) + '$ 筆全部擠到最靠近中間的整數（' + (R % 2 === 0 ? '$' + (R / 2) + '$' : '$' + Math.floor(R / 2) + '$ 或 $' + Math.ceil(R / 2) + '$') + '），變異數才最小。',
             p: { n: n, M: M, R: R, ans: fr2(best) } };
  };
  /* 2-8 由 f(x)=Σ(x-x_i)² 的兩個函數值反推 μ 與 σ（107 全國模考 型） */
  L2.sumSqShift = function (r) {
    var n = r.pick([5, 8, 10, 12, 20]), mu = r.int(4, 12), sg = r.pick([2, 3, 4, 5]), d1 = r.pick([-3, -2, -1, 1]), d2 = d1 + r.pick([2, 3, 4]);
    var x1 = mu + d1, x2 = mu + d2, f1 = n * (d1 * d1 + sg * sg), f2 = n * (d2 * d2 + sg * sg);
    return { q: '設 ' + T('x_1,x_2,\\dots,x_{' + n + '}') + ' 為實數，二次函數 ' + T('f(x)=(x-x_1)^2+(x-x_2)^2+\\cdots+(x-x_{' + n + '})^2') + '。已知 ' + T('f(' + x1 + ')=' + f1) + '、' + T('f(' + x2 + ')=' + f2) + '。求這 ' + T(String(n)) + ' 個數的平均數 ' + T('\\mu') + ' 與標準差 ' + T('\\sigma') + '。',
             a: T('f(x)=' + n + '(x-\\mu)^2+' + n + '\\sigma^2') + '，兩式相減解得 ' + T('\\mu=' + mu) + '，再代回得 ' + T(n + '\\sigma^2=' + (n * sg * sg)) + ' ⟹ ' + T('\\sigma=' + sg),
             h: T('\\sum(x-x_i)^2=n(x-\\mu)^2+n\\sigma^2') + '：頂點在 ' + T('x=\\mu') + '、最小值 ' + T('n\\sigma^2') + '。本題就是 ' + T(n + '(' + x1 + '-\\mu)^2+' + n + '\\sigma^2=' + f1) + '、' + T(n + '(' + x2 + '-\\mu)^2+' + n + '\\sigma^2=' + f2) + '，兩式相減會消掉 ' + T('\\sigma') + '，先解 ' + T('\\mu') + '。',
             p: { n: n, x1: x1, f1: f1, x2: x2, f2: f2, ans: { mu: mu, sg: sg } } };
  };
  /* 2-9 新增一筆後標準差已知，反推那一筆（台南女中 112 下 填 19 型，數字設計成整數） */
  L2.reverseAdd = function (r) {
    var m = r.pick([9, 16, 25, 36]), n = m - 1, c = r.pick([1, 1, 4]), sg = Math.sqrt(m * c), k = r.pick([1, 2]), mu = r.int(50, 75), d = m * k, y = mu + d;
    var var2 = n * (c + k * k);
    return { q: '有 ' + T(String(n)) + ' 個數據的算術平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。若再加入一個數據 ' + T('y') + '（' + T('y\\gt' + mu) + '），這 ' + T(String(m)) + ' 個數據的變異數變為 ' + T(String(var2)) + '。求 ' + T('y') + '。',
             a: '令 ' + T('d=y-' + mu) + '，新平均 ' + T('=' + mu + '+\\dfrac{d}{' + m + '}') + '；新平方和 ' + T('=' + n + '\\cdot' + (sg * sg) + '+\\dfrac{' + n + '}{' + m + '}d^2=' + m + '\\times' + var2) + ' ⟹ ' + T('d^2=' + (d * d)) + ' ⟹ ' + T('y=' + y),
             h: '令 ' + T('d=y-' + mu) + '（新資料離舊平均的距離）：對新平均的平方和 ' + T('=n\\sigma^2+\\dfrac{n}{n+1}d^2=' + n + '\\times' + (sg * sg) + '+\\dfrac{' + n + '}{' + m + '}d^2') + '，令它等於 ' + T(m + '\\times' + var2) + ' 解 ' + T('d') + '，取正根。',
             p: { n: n, mu: mu, sg: sg, var2: var2, ans: y } };
  };
  /* 2-10 合併後的平均與標準差已知，反推一組的平均與另一組的標準差（雄中 108 下 填 14 型） */
  L2.mergeReverse = function (r) {
    var n1 = r.pick([20, 30, 40]), n2 = r.pick([10, 20, 30]), s1 = r.pick([4, 5, 6, 8]), s2 = r.pick([5, 6, 8, 10]);
    var m1v = r.int(55, 75), m2 = m1v + 5, tries = 0;
    while ((n1 * m1v + n2 * m2) % (n1 + n2) !== 0 && tries < 30) { m2 += 1; tries++; }   // 讓合併平均是整數
    if ((n1 * m1v + n2 * m2) % (n1 + n2) !== 0) { n2 = n1; m2 = m1v + 10; }
    var mu = (n1 * m1v + n2 * m2) / (n1 + n2), m1 = F(m1v);
    var va = Fr.div(Fr.add(Fr.mul(F(n1), Fr.add(F(s1 * s1), Fr.mul(Fr.sub(m1, F(mu)), Fr.sub(m1, F(mu))))), F(n2 * (s2 * s2 + (m2 - mu) * (m2 - mu)))), F(n1 + n2));
    return { q: '某班分甲、乙兩組。甲組 ' + T(String(n1)) + ' 人平均 ' + T('x') + ' 分、標準差 ' + T(String(s1)) + ' 分；乙組 ' + T(String(n2)) + ' 人平均 ' + T(String(m2)) + ' 分、標準差 ' + T('y') + ' 分。全班 ' + T(String(n1 + n2)) + ' 人的平均為 ' + T(String(mu)) + ' 分、變異數為 ' + T(dec(va)) + '。求 ' + T('(x,y)') + '。',
             a: T(n1 + 'x+' + n2 + '(' + m2 + ')=' + (n1 + n2) + '(' + mu + ')') + ' ⟹ ' + T('x=' + dec(m1)) + '；再由合併變異數公式 ' + T('\\dfrac{' + n1 + '[' + (s1 * s1) + '+(' + dec(m1) + '-' + mu + ')^2]+' + n2 + '[y^2+(' + m2 + '-' + mu + ')^2]}{' + (n1 + n2) + '}=' + dec(va)) + ' ⟹ ' + T('y=' + s2),
             h: '兩個未知數各用一條式子：平均數的加權式 ' + T(n1 + 'x+' + n2 + '(' + m2 + ')=' + (n1 + n2) + '(' + mu + ')') + ' 先解出 ' + T('x') + '；再把 ' + T('x') + ' 代進合併變異數公式 ' + T('\\dfrac{' + n1 + '[' + (s1 * s1) + '+(x-' + mu + ')^2]+' + n2 + '[y^2+(' + m2 + '-' + mu + ')^2]}{' + (n1 + n2) + '}=' + dec(va)) + '，裡面就只剩 ' + T('y^2') + ' 未知。',
             p: { n1: n1, s1: s1, n2: n2, m2: m2, mu: mu, var: fr2(va), ans: { x: fr2(m1), y: s2 } } };
  };
  /* 2-11 線性調分：把最高分與最低分拉到指定值（103 指考乙 2 型） */
  L2.linearReverse = function (r) {
    var mn = r.int(15, 35), M = Math.min(100, mn + r.pick([50, 60, 70, 75, 80])), mu = r.int(mn + 20, M - 15);   /* 最高分不超過 100 */
    var L = r.pick([40, 50, 60]), H = 100; if (H - L === M - mn) L = (L === 60 ? 50 : 60);   /* 避開 b=1：純平移時「標準差變大還是變小」沒有答案（舊版會答「b>1 變大」） */
    var b = F(H - L, M - mn), a = Fr.sub(F(L), Fr.mul(b, F(mn))), mu2 = Fr.add(a, Fr.mul(b, F(mu)));
    return { q: '某班某次考試平均 ' + T(String(mu)) + ' 分、最高分 ' + T(String(M)) + '、最低分 ' + T(String(mn)) + '。欲做線性調整（調整後 ' + T('=a+b\\times') + ' 原始分數，' + T('b\\gt0') + '），使最高分變成 ' + T(String(H)) + '、最低分變成 ' + T(String(L)) + '。(1) 求 ' + T('a') + '、' + T('b') + '。　(2) 調整後的平均是多少？標準差變大還是變小？',
             a: '(1) ' + T('b=\\dfrac{' + H + '-' + L + '}{' + M + '-' + mn + '}=' + dec(b)) + '、' + T('a=' + L + '-' + dec(b) + '(' + mn + ')=' + dec(a)) + '　(2) ' + T('\\mu\'=' + dec(a) + '+' + dec(b) + '(' + mu + ')=' + dec(mu2)) + '；' + (Fr.lt(b, F(1)) ? T('b\\lt1') + ' ⟹ 標準差變小' : T('b\\gt1') + ' ⟹ 標準差變大'),
             h: '兩點決定直線：$(' + mn + ',' + L + ')$ 與 $(' + M + ',' + H + ')$ 給 $b$（斜率）與 $a$；平均照同一條式子變，標準差只乘 $b$。',
             p: { mn: mn, M: M, mu: mu, L: L, H: H, ans: { a: fr2(a), b: fr2(b), mu2: fr2(mu2) } } };
  };
  /* 2-12 五科 z 分數排名（中山女高 113 下 填 13 型） */
  L2.zRank = function (r) {
    var subs = r.shuffle(SUBJ).slice(0, 5), sc = [], mu = [], sg = [], z = [], tries = 0, ok;
    do {
      sc = []; mu = []; sg = []; z = [];
      for (var i = 0; i < 5; i++) { var m = r.int(60, 85), g = r.pick([F(2), F(4), F(5), F(8), F(10)]); var s = m + Fr.toNum(g) * r.pick([-2, -1, 0, 1, 2]) + r.pick([0, 0, 1, -1]); while (s > 100) s -= Fr.toNum(g); sc.push(s); mu.push(m); sg.push(g); z.push(Fr.div(F(s - m), g)); }
      var vals = z.map(Fr.toNum), srt = vals.slice().sort(function (a, b) { return b - a; }); ok = srt[0] > srt[1] && srt[3] > srt[4]; tries++;
    } while (!ok && tries < 40);
    var best = 0, worst = 0; for (i = 1; i < 5; i++) { if (Fr.lt(z[best], z[i])) best = i; if (Fr.lt(z[i], z[worst])) worst = i; }
    var rows = subs.map(function (s, i) { return s + '：' + T(String(sc[i])) + ' 分（平均 ' + T(String(mu[i])) + '、標準差 ' + T(dec(sg[i])) + '）'; });
    var hrows = subs.map(function (s, i) { return s + ' ' + T('\\dfrac{' + sc[i] + '-' + mu[i] + '}{' + dec(sg[i]) + '}'); });
    return { q: NAMES[r.int(0, 5)] + '五科段考成績如下——' + rows.join('；') + '。哪一科在班上的相對表現最好？哪一科最差？',
             a: T('z') + ' 依序為 ' + T(z.map(dec).join(',\\ ')) + ' ⟹ 最好：' + subs[best] + '、最差：' + subs[worst],
             h: '五科各算 ' + T('z=\\dfrac{x-\\mu}{\\sigma}') + '：' + hrows.join('、') + '，算出來再比大小；標準差小的科目，同樣高出幾分會換到更大的 ' + T('z') + '。',
             p: { sc: sc, mu: mu, sg: sg.map(fr2), ans: { best: best, worst: worst } } };
  };
  /* 2-13 次數呈規律的百分位數：k² 位／k+1 位（中山女高 113 下 單 2、成功 113 下 填 6 型） */
  L2.pctFreqSquare = function (r) {
    var kind = r.int(0, 1), m = kind === 0 ? r.int(6, 10) : r.int(8, 15), data = [];
    for (var v = 1; v <= m; v++) for (var j = 0; j < (kind === 0 ? v * v : v + 1); j++) data.push(v);
    var n = data.length, k = r.pick([10, 12, 20, 25, 30, 40, 50, 60, 70, 75, 80, 90]), ans = pctF(data, k), mu = meanF(data);
    var desc = kind === 0 ? '持有 $1$ 顆的有 $1$ 位、持有 $2$ 顆的有 $4$ 位、持有 $3$ 顆的有 $9$ 位，依此類推（持有 $k$ 顆的有 $k^2$ 位），持有 $' + m + '$ 顆的有 $' + (m * m) + '$ 位'
                          : '$1$ 出現 $2$ 次、$2$ 出現 $3$ 次、$3$ 出現 $4$ 次，依此類推，$' + m + '$ 出現 $' + (m + 1) + '$ 次';
    var tot = kind === 0 ? '\\sum k^2=\\dfrac{' + m + '(' + (m + 1) + ')(' + (2 * m + 1) + ')}{6}=' + n : '\\sum(k+1)=2+3+\\cdots+' + (m + 1) + '=' + n;
    return { q: (kind === 0 ? '某遊戲共有 ' + T(String(n)) + ' 位玩家，每位都持有寶石：' : '某組資料共 ' + T(String(n)) + ' 筆：') + desc + '。(1) 求第 ' + T(String(k)) + ' 百分位數。　(2) 求算術平均數。',
             a: '(1) ' + T('t=\\dfrac{' + n + '\\times' + k + '}{100}=' + dec(tOf(n, k))) + ' ⟹ ' + T('P_{' + k + '}=' + dec(ans)) + '　(2) ' + T('\\mu=' + dec(mu)),
             h: '先算總筆數 ' + T(tot) + '；再算 ' + T('t=\\dfrac{' + n + '\\times' + k + '}{100}=' + dec(tOf(n, k))) + '，列累積次數表看第 ' + T('t') + ' 筆落在哪個值；平均數用 ' + T('\\dfrac{\\sum(\\text{值}\\times\\text{次數})}{' + n + '}') + '。',
             p: { kind: kind, m: m, k: k, ans: { pk: fr2(ans), mu: fr2(mu) } } };
  };
  /* 2-14 成長率混合題：金額漲幅＋百分比／反推最後一年至少（竹科實中 113 下 單 4、例題 17 型） */
  /* [P0, ΔP, r2%, r3%, 平均 g%]：(1+ΔP/P0)(1+r2)(1+r3) = (1+g)³，全部驗過 */
  var GROWM = [[50, 4, 25, 28, 20], [25, 2, 25, 28, 20], [100, 8, 25, 28, 20], [200, 16, 25, 28, 20], [400, 32, 25, 28, 20], [50, 30, 20, -10, 20], [100, 60, 20, -10, 20], [200, 120, 20, -10, 20], [20, 10, 28, -10, 20], [40, 20, 28, -10, 20], [100, 50, 28, -10, 20], [100, 60, 35, -20, 20], [50, 30, 35, -20, 20], [100, 10, 21, 0, 10], [200, 20, 21, 0, 10], [50, 5, 21, 0, 10], [50, 40, 25, 50, 50], [100, 80, 25, 50, 50], [25, 11, 20, 0, 20], [50, 22, 20, 0, 20], [50, 10, 20, 20, 20], [100, 20, 20, 20, 20], [200, 40, 20, 20, 20]];
  var GROWR = [[25, 28, 40, 71.5], [20, 20, 20, 20], [10, 21, 10, 0], [60, 20, 20, -10], [8, 25, 20, 28], [80, 25, 50, 50], [44, 20, 20, 0], [50, 28, 20, -10], [60, 35, 20, -20], [-2, 12, 12, 28], [25, 28, 20, 8], [28, 25, 20, 8], [10, 10, 10, 10], [30, 30, 30, 30], [50, 20, 20, -4], [20, 50, 20, -4], [-4, 50, 20, 20], [50, -4, 20, 20], [20, 25, 20, 15.2], [12, -2, 12, 28], [25, 8, 20, 28], [20, 60, 20, -10], [28, 50, 20, -10], [35, 60, 20, -20], [25, 80, 50, 50], [20, 44, 20, 0], [21, 10, 10, 0]];
  L2.growthMixed = function (r) {
    var kind = r.int(0, 1), nm = r.int(0, 2);
    if (kind === 0) {
      var row = r.pick(GROWM), P0 = row[0], dP = row[1], r2 = row[2], r3 = row[3], g = row[4], r1 = F(dP * 100, P0);
      var fac = hxMulList([dec(Fr.add(F(1), F(dP, P0))), dec(F(100 + r2, 100)), dec(F(100 + r3, 100))]);
      return { q: ['某商品', '某原料', '某零件'][nm] + '去年底單價 ' + T(String(P0)) + ' 元。今年一月比去年底漲 ' + T(String(dP)) + ' 元，二月比一月漲 ' + T(r2 + '\\%') + '，三月比二月' + (r3 >= 0 ? '漲 ' + T(r3 + '\\%') : '跌 ' + T((-r3) + '\\%')) + '。求這三個月平均每月的成長率。',
               a: '第一個月的漲幅是 ' + T('\\dfrac{' + dP + '}{' + P0 + '}=' + dec(r1) + '\\%') + '；' + T('(1+\\bar r)^3=' + fac + '=' + dec(F(Math.round(Math.pow(1 + g / 100, 3) * 1e6), 1e6))) + ' ⟹ ' + T('\\bar r=' + g + '\\%'),
               h: '「漲多少錢」要先換成「漲幾成」：$\\frac{' + dP + '}{' + P0 + '}$；三個月的倍率是 ' + T(fac) + '，相乘之後再開三次方根。',
               p: { kind: 0, item: nm, P0: P0, dP: dP, r2: r2, r3: r3, ans: g } };
    }
    var rw = r.pick(GROWR), a1 = rw[0], a2 = rw[1], g2 = rw[2], need = rw[3];
    return { q: ['某公司', '某工廠', '某連鎖店'][nm] + '前兩年的營業額成長率分別為 ' + T(a1 + '\\%') + '、' + T(a2 + '\\%') + '。若這三年的平均成長率要達到 ' + T(g2 + '\\%') + '（含）以上，則第三年的成長率至少要多少？',
             a: T('(1+r_3)\\ge\\dfrac{(' + dec(F(100 + g2, 100)) + ')^3}{' + dec(F(100 + a1, 100)) + '\\times' + dec(F(100 + a2, 100)) + '}=' + dec(F(Math.round((100 + need) * 10), 1000))) + ' ⟹ 至少 ' + T(need + '\\%'),
             h: '平均成長率 ' + T('\\ge' + g2 + '\\%') + ' ⟺ 三個倍率的乘積 ' + T('\\ge(' + dec(F(100 + g2, 100)) + ')^3') + '，把已知的兩個倍率 ' + T(dec(F(100 + a1, 100))) + '、' + T(dec(F(100 + a2, 100))) + ' 除過去就得第三年的倍率。',
             p: { kind: 1, item: nm, a1: a1, a2: a2, g: g2, ans: need } };
  };
  /* 2-15 等差資料的統計量：μ、Me、P_k 與 σ²=d²(n²−1)/12（竹科實中 113 下 多 5、板橋 112 下 填 10 型） */
  L2.apStats = function (r) {
    var n = r.pick([10, 12, 15, 16, 20, 24, 25]), a1 = r.int(1, 9), d = r.pick([2, 3, 4, 5, 6]), data = [];
    for (var i = 0; i < n; i++) data.push(a1 + d * i);
    var k = r.pick([20, 25, 30, 40, 60, 70, 75, 80]), mu = meanF(data), pk = pctF(data, k), va = varF(data);
    return { q: '設等差資料 ' + T('X:\\ ' + a1 + ',\\ ' + (a1 + d) + ',\\ ' + (a1 + 2 * d) + ',\\ \\dots,\\ ' + data[n - 1]) + '（共 ' + T(String(n)) + ' 筆）。求 (1) 算術平均數與中位數　(2) 第 ' + T(String(k)) + ' 百分位數　(3) 變異數。',
             a: '(1) ' + T('\\mu=Me=\\dfrac{' + a1 + '+' + data[n - 1] + '}{2}=' + dec(mu)) + '　(2) ' + T('t=' + dec(tOf(n, k))) + ' ⟹ ' + T('P_{' + k + '}=' + dec(pk)) + '　(3) ' + T('\\sigma^2=\\dfrac{d^2(n^2-1)}{12}=\\dfrac{' + (d * d) + '(' + (n * n) + '-1)}{12}=' + dec(va)),
             h: '等差資料左右對稱 ⟹ ' + T('\\mu=Me=\\dfrac{' + a1 + '+' + data[n - 1] + '}{2}') + '（首尾平均）；' + T('P_k') + ' 先算 ' + T('t=\\dfrac{' + n + '\\times' + k + '}{100}=' + dec(tOf(n, k))) + ' 再照規則取；變異數有公式 ' + T('\\dfrac{d^2(n^2-1)}{12}=\\dfrac{' + (d * d) + '(' + (n * n) + '-1)}{12}') + '（把資料平移成 ' + T('0,d,2d,\\dots') + ' 再用 ' + T('\\sum k^2') + ' 推得）。',
             p: { n: n, a1: a1, d: d, k: k, ans: { mu: fr2(mu), pk: fr2(pk), var: fr2(va) } } };
  };
  /* 2-16 由「兩兩乘積和」與「平方和」求變異數（板橋 113 下 填 13 型） */
  L2.pairProdVar = function (r) {
    var xs, s;
    do { xs = []; for (var i = 0; i < 6; i++) xs.push(r.int(1, 9)); s = sumArr(xs); } while (s % 6 !== 0);
    var S2 = sumArr(xs.map(function (v) { return v * v; })), P = (s * s - S2) / 2, mu = s / 6, va = F(S2, 6); va = Fr.sub(va, F(mu * mu));
    return { q: '有六個正數，若任意兩數的乘積總和為 ' + T(String(P)) + '，且這六個數的平方和為 ' + T(String(S2)) + '。求這六個數的變異數。',
             a: T('\\left(\\sum x_i\\right)^2=' + S2 + '+2(' + P + ')=' + (s * s)) + ' ⟹ ' + T('\\sum x_i=' + s) + '、' + T('\\mu=' + mu) + '；' + T('\\sigma^2=\\dfrac{' + S2 + '}{6}-' + mu + '^2=' + dec(va)),
             h: '把「和的平方」展開：' + T('\\left(\\sum x_i\\right)^2=\\sum x_i^2+2\\sum_{i\\lt j}x_ix_j=' + S2 + '+2(' + P + ')') + '，六個數都是正的所以總和取正根；再用 ' + T('\\sigma^2=\\dfrac{\\sum x^2}{n}-\\mu^2=\\dfrac{' + S2 + '}{6}-\\mu^2') + '。',
             p: { P: P, S2: S2, ans: fr2(va) } };
  };
  /* 2-17 T 分數的及格門檻（115 學測 A 9 型） */
  L2.tThreshold = function (r) {
    var mu = r.int(55, 70), s1 = r.pick([8, 10, 12, 15]), s2 = r.pick([4, 5, 6, 8]); if (s1 === s2) s1 += 4;
    var T0 = r.pick([35, 40, 45]), z0 = F(T0 - 50, 10), p1 = Fr.add(F(mu), Fr.mul(z0, F(s1))), p2 = Fr.add(F(mu), Fr.mul(z0, F(s2)));
    var st = mu + s2 * r.pick([-1, -2, 1]), Tst = Fr.add(F(50), Fr.mul(F(10), F(st - mu, s2)));
    return { q: T('T') + ' 分數定義為 ' + T('T=50+10\\cdot\\dfrac{S-\\mu}{\\sigma}') + '。某班數學與英文的平均皆為 ' + T(String(mu)) + ' 分，數學標準差 ' + T(String(s1)) + '、英文標準差 ' + T(String(s2)) + '。(1) 甲生英文考 ' + T(String(st)) + ' 分，求其英文 ' + T('T') + ' 分數。　(2) 若兩科及格標準皆為「' + T('T\\ge' + T0) + '」，求兩科各自的及格原始分數，並說明哪一科的門檻較低。',
             a: '(1) ' + T('T=' + dec(Tst)) + '　(2) ' + T('z\\ge' + dec(z0)) + ' ⟹ 數學 ' + T('S\\ge' + mu + '+(' + dec(z0) + ')(' + s1 + ')=' + dec(p1)) + '、英文 ' + T('S\\ge' + dec(p2)) + '；' + (Fr.lt(p1, p2) ? '數學' : '英文') + '的門檻較低，因為它的標準差較大（同樣的 $z$ 對應到離平均更遠的分數）',
             h: '(1) 先算 ' + T('z=\\dfrac{' + st + '-' + mu + '}{' + s2 + '}') + ' 再 ' + T('T=50+10z') + '；(2) ' + T('T\\ge' + T0) + ' ⟺ ' + T('z\\ge' + dec(z0)) + ' ⟺ ' + T('S\\ge\\mu+(' + dec(z0) + ')\\sigma') + '：數學是 ' + T(mu + '+(' + dec(z0) + ')(' + s1 + ')') + '、英文是 ' + T(mu + '+(' + dec(z0) + ')(' + s2 + ')') + '，' + T('\\sigma') + ' 越大門檻被拉得越低。',
             p: { mu: mu, s1: s1, s2: s2, T0: T0, st: st, ans: { Tst: fr2(Tst), p1: fr2(p1), p2: fr2(p2) } } };
  };
  /* 2-18 學期成績：平時取較高幾次，期末至少要考幾分（例題 3／北一女 113 下 填 7 型） */
  L2.weightedMin = function (r) {
    var m = r.pick([5, 6]), k = m - 2, quiz = [], target = r.pick([60, 65, 70, 75]), s1, s2, need, tries = 0;
    do {
      quiz = []; for (var i = 0; i < m; i++) quiz.push(r.int(45, 95));
      s1 = r.int(50, 85); s2 = r.int(50, 85);
      var best = quiz.slice().sort(function (a, b) { return b - a; }).slice(0, k), pt = F(sumArr(best), k);
      need = Fr.div(Fr.sub(F(100 * target), Fr.add(F(20 * s1 + 20 * s2), Fr.mul(F(30), pt))), F(30)); tries++;
    } while ((Fr.toNum(need) <= 30 || Fr.toNum(need) > 100) && tries < 80);
    var ans = Math.ceil(Fr.toNum(need) - 1e-9), bestArr = quiz.slice().sort(function (a, b) { return b - a; }).slice(0, k);
    return { q: '數學學期成績：第一次期中考 ' + T('20\\%') + '、第二次期中考 ' + T('20\\%') + '、期末考 ' + T('30\\%') + '、平時成績 ' + T('30\\%') + '；平時成績是 ' + T(String(m)) + ' 次平時考中取 ' + T(String(k)) + ' 次較高的成績求算術平均。某生兩次期中考分別為 ' + T(String(s1)) + '、' + T(String(s2)) + ' 分，平時考依序為 ' + T(listTex(quiz)) + '。若學期成績要達 ' + T(String(target)) + ' 分（含）以上，期末考至少要考幾分？（取最小整數）',
             a: '平時 ' + T('=\\dfrac{' + bestArr.join('+') + '}{' + k + '}=' + dec(F(sumArr(bestArr), k))) + '；' + T('0.2(' + s1 + ')+0.2(' + s2 + ')+0.3E+0.3(' + dec(F(sumArr(bestArr), k)) + ')\\ge' + target) + ' ⟹ ' + T('E\\ge' + dec(need)) + ' ⟹ 至少 ' + T(String(ans)) + ' 分',
             h: '兩層加權：先算裡面那層——取較高的 $' + k + '$ 次平均 ' + T('\\dfrac{' + bestArr.join('+') + '}{' + k + '}') + '；再列外層不等式 ' + T('0.2(' + s1 + ')+0.2(' + s2 + ')+0.3E+0.3\\times\\text{平時}\\ge' + target) + ' 解 ' + T('E') + '，非整數要無條件進位。',
             p: { quiz: quiz, k: k, s1: s1, s2: s2, target: target, ans: ans } };
  };

  /* ══════════════════════════════════════════════════════════ */
  /* ══════════════════════════════════════════════════════════
     L1 解題步驟（s：每步一段 HTML）與第一層提示（h1：只講「這是哪一型、第一步做什麼」，不帶數字）
     全部由 p（與 o.a）重算，所以與題目、答案一定一致；答案由頁面另行附在步驟後。
     用法：用 splice 腳本插在 META（var META_L1 = [）之前，並把 wrapAll(L1) 換成 wrapAll(L1, L1_SOL, L1_H1)。
     自己加的小工具一律加前綴 sol。
     ══════════════════════════════════════════════════════════ */
  function solF(t) { return F(t[0], t[1]); }                      /* p 裡的 [n,d] 還原成分數 */
  function solFin(o) { return '答案：' + o.a + '。'; }
  function solPar(s) { return String(s).charAt(0) === '-' ? '(' + s + ')' : String(s); }   /* 負數加括號 */
  function solCoef(f) { return Fr.eq(f, F(1)) ? '' : (Fr.eq(f, F(-1)) ? '-' : dec(f)); }   /* 係數 ±1 省略 */
  function solPre(f) { return Fr.eq(f, F(1)) ? '' : solPar(dec(f)); }                      /* 乘在括號前的係數 */
  function solDiv(n, d) { return d === 1 ? String(n) : (n < 0 ? '-' : '') + '\\dfrac{' + Math.abs(n) + '}{' + d + '}'; }
  function solMean(a) { return sumArr(a) / a.length; }

  var L1_H1 = {
    centralTrio: '這是「平均數、中位數、眾數」：先把資料由小到大排好，正中間那一筆是中位數、出現最多次的是眾數，平均數則是總和除以筆數。',
    weightedMean: '這是「加權平均」：權重是人數，先把兩班的總分各自算出來再相加，最後除以總人數，不能把兩個平均直接相加除以二。',
    weightedScore: '這是「加權平均求最低分數」：先把已知各項的「權重乘分數」加起來，再列一個不等式解出未知那一科要考幾分。',
    freqTable: '這是「次數分配表」：平均數用「數值乘次數」的總和除以總次數，中位數則用累積次數找出正中間那一筆落在哪一格。',
    meanShift: '這是「新增或剔除資料後的平均」：一律回到「總和」思考，先算出原本的總和再加減，最後除以新的筆數。',
    pctPosition: '這是「百分位數取第幾筆」：先算位置，位置是整數就取相鄰兩筆的平均，不是整數就無條件進位取一筆。',
    pctData: '這是「排序資料的百分位數」：兩個百分位數各自先算位置，再照整數與非整數兩種規則去取值。',
    pctFreq: '這是「次數有規律的百分位數」：先用等差和算出總筆數，再算位置，最後用累積次數表找出落在哪一格。',
    sdBasic: '這是「全距、變異數與標準差」：先算平均，再把每筆的偏差寫出來（總和必為零），偏差平方和除以筆數就是變異數。',
    sdFromSums: '這是「由總和與平方和求標準差」：平均數是總和除以筆數，變異數用「平方的平均減去平均的平方」，不必知道每一筆。',
    sumSqFromStats: '這是「由平均與標準差反推平方和」：把變異數的定義式反解，偏離某個定點時再拆成「對平均的偏差」加上「平均離那個點的距離」。',
    addOne: '這是「新增一筆資料的影響」：先用總和算新平均，再把對舊平均的平方和換算成對新平均的平方和，最後除以新的筆數。',
    mergeTwo: '這是「兩組資料合併」：先用人數加權算合併平均，再套合併變異數公式，每一組都要加上「組平均離總平均」的修正項。',
    linearTrans: '這是「線性變換」：平均數跟著整條式子走，標準差只被係數放大而且要取絕對值，平移完全不影響分散程度。',
    inverseTrans: '這是「由變換前後反推係數」：兩個標準差的比就是倍率，再把平均數代回去解出常數項。',
    zCompare: '這是「標準化跨科比較」：各科先算標準化分數，看的是高出平均幾個標準差，直接比原始分數沒有意義。',
    zInverse: '這是「標準化分數與原始分數互換」：把標準化的定義式反解就能互相換算，任何資料標準化後平均是零、標準差是一。',
    tScore: '這是「$T$ 分數」：先算標準化分數，再把它放大十倍後搬到五十；反過來問就先由 $T$ 分數求出標準化分數。',
    growthRate: '這是「平均成長率」：成長率要用乘的，把每年的成長率換成倍率相乘，再開次方根，不能把成長率直接平均。',
    growthTotal: '這是「由首尾值求平均成長率」：只看最後與最初的比值，再開次方根；比值小於一就是負成長。',
    corrData: '這是「由資料算相關係數」：先算兩個平均，把兩排偏差寫出來，再算兩個平方和與一個乘積和代進公式。',
    corrSums: '這是「由總和算相關係數」：三個和都要先減掉平均的貢獻，再代進相關係數的公式。',
    corrTransform: '這是「線性變換對相關係數的影響」：平移完全沒有影響，只看兩個係數乘積的正負決定相關係數是否變號。',
    corrPerfect: '這是「完全線性關係」：所有點都落在同一條直線上，相關係數是正負一，最適直線就是那條直線本身。',
    fitData: '這是「由資料求最適直線」：斜率是乘積和除以平方和，再用「必過重心」把直線寫出來。',
    fitStats: '這是「由統計量求最適直線與預測」：斜率等於相關係數乘上兩個標準差的比，直線必過重心，預測時直接從重心出發。',
    fitCentroid: '這是「由最適直線反推平均與相關係數」：直線必過重心，代入橫坐標的平均就得縱坐標的平均；再由斜率公式反解相關係數。',
    fitTransform: '這是「線性變換後的最適直線」：兩個標準差各乘上係數的絕對值，相關係數看兩個係數乘積的正負，新直線通過新的重心。',
    stdFit: '這是「標準化後的最適直線」：標準化後平均是零、標準差是一，所以斜率就等於相關係數，而且直線必過原點。'
  };

  var L1_SOL = {};

  /* ── §1-1 集中趨勢與加權平均 ── */
  L1_SOL.centralTrio = function (p, o) {
    var d = p.data.slice().sort(function (a, b) { return a - b; }), mu = solF(p.ans.mu), s = sumArr(p.data);
    return ['先把 $7$ 筆資料由小到大排好：' + T(listTex(d)) + '。',
      '平均數是總和除以筆數：' + T('\\mu=\\dfrac{' + s + '}{7}=' + dec(mu)) + '。',
      '$7$ 筆的中位數是正中間的第 $4$ 筆 ' + T('Me=' + p.ans.me) + '；出現最多次（$3$ 次）的值是眾數 ' + T('Mo=' + p.ans.mo) + '。' + solFin(o)];
  };

  L1_SOL.weightedMean = function (p, o) {
    var t1 = p.n1 * p.m1, t2 = p.n2 * p.m2, n = p.n1 + p.n2, mu = solF(p.ans);
    return ['權重是人數，先把兩班的總分算出來：甲班 ' + T(p.n1 + '\\times' + p.m1 + '=' + t1) + ' 分，乙班 ' + T(p.n2 + '\\times' + p.m2 + '=' + t2) + ' 分。',
      '兩班總分相加，再除以總人數 ' + T(String(n)) + '：' + T('\\mu=\\dfrac{' + t1 + '+' + t2 + '}{' + n + '}=' + dec(mu)) + ' 分（不是把兩個平均相加除以二）。' + solFin(o)];
  };

  L1_SOL.weightedScore = function (p, o) {
    var kn = [], known = 0, i;
    for (i = 0; i < 4; i++) if (i !== p.idx) { kn.push(p.w[i] + '(' + p.s[i] + ')'); known += p.w[i] * p.s[i]; }
    var need = F(100 * p.target - known, p.w[p.idx]);
    return ['學期成績 ' + T('=\\dfrac{\\sum(\\text{權重}\\times\\text{分數})}{100}') + '，已知的三項合計 ' + T(kn.join('+') + '=' + known) + '。',
      '設未知的那一科考 $x$ 分，列不等式 ' + T(known + '+' + p.w[p.idx] + 'x\\ge100\\times' + p.target + '=' + (100 * p.target)) + '，解得 ' + T('x\\ge' + dec(need)) + '。',
      '分數要取整數，所以至少要考 ' + T(String(p.ans)) + ' 分。' + solFin(o)];
  };

  L1_SOL.freqTable = function (p, o) {
    var n = sumArr(p.cnts), prods = [], cum = [], run = 0, i;
    for (i = 0; i < 4; i++) { prods.push(p.vals[i] * p.cnts[i]); run += p.cnts[i]; cum.push(run); }
    var mu = solF(p.ans.mu), me = solF(p.ans.me);
    var pos = n % 2 ? '第 ' + T(String((n + 1) / 2)) + ' 筆' : '第 ' + T(String(n / 2)) + ' 與第 ' + T(String(n / 2 + 1)) + ' 筆的平均';
    return ['總筆數 ' + T('n=' + p.cnts.join('+') + '=' + n) + '；把「數值乘次數」加起來得 ' + T(prods.join('+') + '=' + sumArr(prods)) + '。',
      '平均數 ' + T('\\mu=\\dfrac{' + sumArr(prods) + '}{' + n + '}=' + dec(mu)) + '。',
      '累積次數依序是 ' + T(listTex(cum)) + '，中位數取' + pos + '，得 ' + T('Me=' + dec(me)) + '。' + solFin(o)];
  };

  L1_SOL.meanShift = function (p, o) {
    var v = solF(p.ans), tot = p.n * p.mu;
    if (p.kind === 0) {
      return ['用「總和」思考：原本 ' + T(String(p.n)) + ' 筆的總和 ' + T('=' + p.n + '\\times' + p.mu + '=' + tot) + '。',
        '加入 ' + T(String(p.v)) + ' 之後總和變成 ' + T(tot + '+' + p.v + '=' + (tot + p.v)) + '，筆數變成 ' + T(String(p.n + 1)) + '。',
        '新平均 ' + T("\\mu'=\\dfrac{" + (tot + p.v) + '}{' + (p.n + 1) + '}=' + dec(v)) + '。' + solFin(o)];
    }
    var left = tot - p.rem[0] - p.rem[1];
    return ['全部評審的總分 ' + T('=' + p.n + '\\times' + p.mu + '=' + tot) + ' 分。',
      '剔除 ' + T(String(p.rem[0])) + ' 與 ' + T(String(p.rem[1])) + ' 之後剩下 ' + T(tot + '-' + p.rem[0] + '-' + p.rem[1] + '=' + left) + ' 分，人數剩 ' + T(String(p.n - 2)) + ' 位。',
      '成績 ' + T('=\\dfrac{' + left + '}{' + (p.n - 2) + '}=' + dec(v)) + ' 分。' + solFin(o)];
  };

  /* ── §1-2 百分位數 ── */
  L1_SOL.pctPosition = function (p, o) {
    var t = solF(p.ans.t), pos = p.ans.pos;
    return ['百分位數要先算位置：' + T('t=\\dfrac{nk}{100}=\\dfrac{' + p.n + '\\times' + p.k + '}{100}=' + dec(t)) + '。',
      (t.d === 1
        ? T('t=' + t.n) + ' 是整數，規則是取第 ' + T(String(pos[0])) + ' 筆與第 ' + T(String(pos[1])) + ' 筆的平均。'
        : T('t=' + dec(t)) + ' 不是整數，規則是無條件進位，取第 ' + T(String(pos[0])) + ' 筆。') + solFin(o)];
  };

  L1_SOL.pctData = function (p, o) {
    var n = p.data.length, out = [], i;
    for (i = 0; i < 2; i++) {
      var t = F(n * p.ks[i], 100), v = solF(p.ans[i]);
      out.push(T('t=\\dfrac{' + n + '\\times' + p.ks[i] + '}{100}=' + dec(t))
        + (t.d === 1 ? '，是整數 ⟹ 取第 ' + T(String(t.n)) + ' 與第 ' + T(String(t.n + 1)) + ' 筆的平均 ' : '，不是整數 ⟹ 進位取第 ' + T(String(Math.ceil(t.n / t.d))) + ' 筆 ')
        + T('P_{' + p.ks[i] + '}=' + dec(v)));
    }
    return ['資料已經由小到大排好，共 ' + T('n=' + n) + ' 筆；兩個百分位數各自先算 ' + T('t=\\dfrac{nk}{100}') + '。',
      '第 ' + T(String(p.ks[0])) + ' 百分位數：' + out[0] + '。',
      '第 ' + T(String(p.ks[1])) + ' 百分位數：' + out[1] + '。' + solFin(o)];
  };

  L1_SOL.pctFreq = function (p, o) {
    var m = p.m, n = m * (m + 1) / 2, t = F(n * p.k, 100), v = solF(p.ans), cum = [], c = 0, j;
    for (j = 1; j <= m; j++) { c += j; cum.push(c); }
    var cumT = cum.slice(0, Math.min(6, m)).join(',\\ ') + (m > 6 ? ',\\ \\dots' : '');
    return ['總人數是 $1$ 到 ' + T(String(m)) + ' 的和：' + T('n=\\dfrac{' + m + '\\times' + (m + 1) + '}{2}=' + n) + '。',
      '位置 ' + T('t=\\dfrac{' + n + '\\times' + p.k + '}{100}=' + dec(t)) + '；累積人數依序是 ' + T(cumT) + '（第 $j$ 格累積到 ' + T('\\dfrac{j(j+1)}{2}') + '）。',
      '照規則取' + (t.d === 1 ? '第 ' + T(String(t.n)) + ' 與第 ' + T(String(t.n + 1)) + ' 筆的平均' : '第 ' + T(String(Math.ceil(t.n / t.d))) + ' 筆') + '，落在 ' + T('P_{' + p.k + '}=' + dec(v)) + '。' + solFin(o)];
  };

  /* ── §1-3 分散程度 ── */
  L1_SOL.sdBasic = function (p, o) {
    var d = p.data, n = d.length, mu = solF(p.ans.mu), va = solF(p.ans.var), m0 = Fr.toNum(mu);
    var dev = d.map(function (v) { return v - m0; }), sq = dev.map(function (x) { return x * x; }), ss = sumArr(sq);
    return ['(1) 全距是最大值減最小值：' + T('' + Math.max.apply(null, d) + '-' + Math.min.apply(null, d) + '=' + p.ans.range) + '。',
      '(2) 平均數 ' + T('\\mu=\\dfrac{' + sumArr(d) + '}{' + n + '}=' + dec(mu)) + '。',
      '(3) 每筆的偏差依序是 ' + T(listTex(dev)) + '（總和為 $0$，可以拿來檢查），偏差平方和 ' + T('=' + sq.join('+') + '=' + ss) + '。',
      '變異數 ' + T('\\sigma^2=\\dfrac{' + ss + '}{' + n + '}=' + dec(va)) + '，標準差是它的正平方根 ' + T('\\sigma=\\sqrt{' + dec(va) + '}=' + sqrtBoth(va)) + '。' + solFin(o)];
  };

  L1_SOL.sdFromSums = function (p, o) {
    var mu = solF(p.ans.mu), va = solF(p.ans.var);
    return ['平均數是總和除以筆數：' + T('\\mu=\\dfrac{' + p.sx + '}{' + p.n + '}=' + dec(mu)) + '。',
      '再用「平方的平均減去平均的平方」：' + T('\\sigma^2=\\dfrac{\\sum x_i^2}{n}-\\mu^2=\\dfrac{' + p.sxx + '}{' + p.n + '}-' + dec(mu) + '^2=' + dec(va)) + '。',
      '標準差是變異數的正平方根 ' + T('\\sigma=\\sqrt{' + dec(va) + '}=' + sqrtBoth(va)) + '；整個過程都不需要知道每一筆資料是多少。' + solFin(o)];
  };

  L1_SOL.sumSqFromStats = function (p, o) {
    return ['(1) 把 ' + T('\\sigma^2=\\dfrac{\\sum x_i^2}{n}-\\mu^2') + ' 反解：' + T('\\sum x_i^2=n(\\sigma^2+\\mu^2)=' + p.n + '(' + p.sg + '^2+' + p.mu + '^2)=' + p.ans.sumsq) + '。',
      '(2) 把 ' + T('x_i-' + p.a) + ' 拆成 ' + T('(x_i-\\mu)+(\\mu-' + p.a + ')') + '，平方展開後交叉項的總和是 $0$，所以 ' + T('\\sum(x_i-' + p.a + ')^2=n\\sigma^2+n(\\mu-' + p.a + ')^2') + '。',
      '代入數字 ' + T('=' + p.n + '\\times' + (p.sg * p.sg) + '+' + p.n + '\\times' + ((p.mu - p.a) * (p.mu - p.a)) + '=' + p.ans.shifted) + '。' + solFin(o)];
  };

  L1_SOL.addOne = function (p, o) {
    var mu2 = solF(p.ans.mu2), var2 = solF(p.ans.var2), d = p.v - p.mu, ss = p.n * p.sg * p.sg, n1 = p.n + 1;
    var sqT = d === 0 ? String(ss) : ss + '+\\dfrac{' + p.n + '}{' + n1 + '}\\times' + (d * d);
    return ['先算新平均：原總和 ' + T('=' + p.n + '\\times' + p.mu + '=' + (p.n * p.mu)) + '，加入 ' + T(String(p.v)) + ' 後 ' + T("\\mu'=\\dfrac{" + (p.n * p.mu) + '+' + p.v + '}{' + n1 + '}=' + dec(mu2)) + '。',
      '原本對舊平均的平方和 ' + T('=n\\sigma^2=' + p.n + '\\times' + (p.sg * p.sg) + '=' + ss) + '；新資料離舊平均 ' + T('d=' + p.v + '-' + p.mu + '=' + d) + (d === 0 ? '（恰好等於平均）' : '') + '。',
      '對新平均的平方和 ' + T('=n\\sigma^2+\\dfrac{n}{n+1}d^2=' + sqT) + '，再除以 ' + T(String(n1)) + ' 得 ' + T("\\sigma'^2=" + dec(var2)) + '。' + solFin(o)];
  };

  L1_SOL.mergeTwo = function (p, o) {
    var n = p.n1 + p.n2, mu = solF(p.ans.mu), va = solF(p.ans.var), muT = dec(mu).replace('\\dfrac', '\\frac');
    return ['先用人數加權算合併平均：' + T('\\mu=\\dfrac{' + p.n1 + '\\times' + p.m1 + '+' + p.n2 + '\\times' + p.m2 + '}{' + n + '}=' + dec(mu)) + '。',
      '合併變異數要把「組平均離總平均」的修正項加進去：' + T('\\sigma^2=\\dfrac{n_1[\\sigma_1^2+(\\mu_1-\\mu)^2]+n_2[\\sigma_2^2+(\\mu_2-\\mu)^2]}{n_1+n_2}') + '。',
      '代入數字 ' + T('=\\dfrac{' + p.n1 + '[' + (p.s1 * p.s1) + '+(' + p.m1 + '-' + muT + ')^2]+' + p.n2 + '[' + (p.s2 * p.s2) + '+(' + p.m2 + '-' + muT + ')^2]}{' + n + '}=' + dec(va)) + '，標準差 ' + T('\\sigma=\\sqrt{' + dec(va) + '}=' + sqrtBoth(va)) + '。' + solFin(o)];
  };

  /* ── §1-4 線性變換與標準化 ── */
  L1_SOL.linearTrans = function (p, o) {
    var a = solF(p.a), muy = solF(p.ans.mu), sgy = solF(p.ans.sg), vy = Fr.mul(sgy, sgy), aa = Fr.abs(a);
    return ['平均數跟著整條式子走：' + T('\\mu_y=a\\mu_x+b=' + solCoef(a) + '(' + p.mu + ')' + (p.b > 0 ? '+' + p.b : String(p.b)) + '=' + dec(muy)) + '。',
      '標準差只被係數放大、而且要取絕對值（平移不影響）：' + (Fr.eq(aa, F(1)) ? T('\\sigma_y=\\sigma_x=' + dec(sgy)) : T('\\sigma_y=|a|\\sigma_x=' + dec(aa) + '\\times' + p.sg + '=' + dec(sgy))) + '。',
      '變異數是標準差的平方：' + T('\\sigma_y^2=' + solPar(dec(sgy)) + '^2=' + dec(vy)) + '。' + solFin(o)];
  };

  L1_SOL.inverseTrans = function (p, o) {
    var a = solF(p.ans.a), mu2 = solF(p.mu2), s2 = solF(p.s2), y = solF(p.ans.y);
    return ['(1) 標準差只跟倍率 $a$ 有關：' + T('a=\\dfrac{\\sigma_y}{\\sigma_x}=\\dfrac{' + dec(s2) + '}{' + p.s1 + '}=' + dec(a)) + '。',
      '再用 ' + T('\\mu_y=a\\mu_x+b') + '：' + T(dec(mu2) + '=' + dec(a) + '\\times' + p.mu1 + '+b') + ' ⟹ ' + T('b=' + p.ans.b) + '。',
      '(2) 把 ' + T('x=' + p.s) + ' 代進 ' + T('y=' + dec(a) + 'x+' + p.ans.b) + '：' + T('y=' + dec(a) + '\\times' + p.s + '+' + p.ans.b + '=' + dec(y)) + ' 分。' + solFin(o)];
  };

  L1_SOL.zCompare = function (p, o) {
    var z1 = solF(p.ans.z1), z2 = solF(p.ans.z2);
    return ['(1) 標準化分數 ' + T('z=\\dfrac{x-\\mu}{\\sigma}') + ' 量的是「高出平均幾個標準差」。第一科 ' + T('z=\\dfrac{' + p.x1 + '-' + p.m1 + '}{' + p.g1 + '}=' + dec(z1)) + '。',
      '第二科 ' + T('z=\\dfrac{' + p.x2 + '-' + p.m2 + '}{' + p.g2 + '}=' + dec(z2)) + '。',
      '(2) 比較兩個 ' + T('z') + '：' + T(Fr.lt(z2, z1) ? dec(z1) + '\\gt' + dec(z2) : dec(z2) + '\\gt' + dec(z1)) + '，' + T('z') + ' 較大的那一科相對表現較好（直接比原始分數沒有意義）。' + solFin(o)];
  };

  L1_SOL.zInverse = function (p, o) {
    if (p.kind === 0) {
      var z = solF(p.z), x = solF(p.ans);
      return ['標準化的定義是 ' + T('z=\\dfrac{x-\\mu}{\\sigma}') + '，要回推原始分數就把它反解成 ' + T('x=\\mu+z\\sigma') + '。',
        '代入數字：' + T('x=' + p.mu + '+(' + dec(z) + ')(' + p.sg + ')=' + dec(x)) + ' 分。' + solFin(o)];
    }
    var zz = solF(p.ans);
    return ['直接代定義：' + T('z=\\dfrac{x-\\mu}{\\sigma}=\\dfrac{' + p.x + '-' + p.mu + '}{' + p.sg + '}=' + dec(zz)) + '。',
      '把整組資料都標準化，等於先平移再伸縮：平移讓平均變成 $0$，除以 ' + T('\\sigma') + ' 讓標準差變成 $1$。' + solFin(o)];
  };

  L1_SOL.tScore = function (p, o) {
    if (p.kind === 0) {
      var z = F(p.s - p.mu, p.sg), Tv = solF(p.ans);
      return ['先算標準化分數 ' + T('z=\\dfrac{S-\\mu}{\\sigma}=\\dfrac{' + p.s + '-' + p.mu + '}{' + p.sg + '}=' + dec(z)) + '。',
        T('T') + ' 分數就是把 ' + T('z') + ' 放大 $10$ 倍後搬到 $50$：' + T('T=50+10z=50+10(' + dec(z) + ')=' + dec(Tv)) + '。' + solFin(o)];
    }
    var z2 = F(p.T - 50, 10), S = solF(p.ans);
    return ['由 ' + T('T=50+10z') + ' 反推標準化分數：' + T('z=\\dfrac{T-50}{10}=\\dfrac{' + p.T + '-50}{10}=' + dec(z2)) + '。',
      '再由 ' + T('z=\\dfrac{S-\\mu}{\\sigma}') + ' 反解原始成績：' + T('S=\\mu+z\\sigma=' + p.mu + '+(' + dec(z2) + ')(' + p.sg + ')=' + dec(S)) + ' 分。' + solFin(o)];
  };

  /* ── §1-5 平均成長率 ── */
  L1_SOL.growthRate = function (p, o) {
    var n = p.rates.length, g = p.ans, pf = F(1);
    p.rates.forEach(function (v) { pf = Fr.mul(pf, F(100 + v, 100)); });
    var prod = p.rates.map(function (v) { return '(1' + (v < 0 ? '-' : '+') + dec(F(Math.abs(v), 100)) + ')'; }).join('');
    return ['成長率要用「乘」的：把每一年的成長率換成倍率 ' + T(prod) + '，相乘之後就是 ' + T(String(n)) + ' 年的總倍率。',
      '總倍率 ' + T(prod + '=' + dec(pf)) + '，而平均成長率 ' + T('\\bar r') + ' 滿足 ' + T('(1+\\bar r)^' + n + '=' + dec(pf)) + '。',
      '把它寫成 ' + T(String(n)) + ' 次方：' + T(dec(pf) + '=(' + dec(F(100 + g, 100)) + ')^' + n) + ' ⟹ ' + T('1+\\bar r=' + dec(F(100 + g, 100))) + ' ⟹ ' + T('\\bar r=' + (g < 0 ? '-' : '') + Math.abs(g) + '\\%') + '。' + solFin(o)];
  };

  L1_SOL.growthTotal = function (p, o) {
    var ratio = F(p.B, p.A), g = p.ans;
    return ['平均成長率只看首尾：' + T('(1+\\bar r)^' + p.n + '=\\dfrac{\\text{末}}{\\text{初}}=\\dfrac{' + p.B + '}{' + p.A + '}=' + dec(ratio)) + '。',
      '把 ' + T(dec(ratio)) + ' 寫成 ' + T(String(p.n)) + ' 次方：' + T(dec(ratio) + '=(' + dec(F(100 + g, 100)) + ')^' + p.n) + ' ⟹ ' + T('1+\\bar r=' + dec(F(100 + g, 100))) + '。',
      '所以 ' + T('\\bar r=' + (g < 0 ? '-' : '') + Math.abs(g) + '\\%') + (g < 0 ? '（比值小於 $1$，是負成長）' : '') + '。' + solFin(o)];
  };

  /* ── §2-1 相關係數 ── */
  L1_SOL.corrData = function (p, o) {
    var n = p.x.length, mx = solMean(p.x), my = solMean(p.y), rr = solF(p.ans);
    var dx = p.x.map(function (v) { return v - mx; }), dy = p.y.map(function (v) { return v - my; });
    var sxx = 0, syy = 0, sxy = 0, i;
    for (i = 0; i < n; i++) { sxx += dx[i] * dx[i]; syy += dy[i] * dy[i]; sxy += dx[i] * dy[i]; }
    return ['先算兩個平均：' + T('\\mu_x=\\dfrac{' + sumArr(p.x) + '}{' + n + '}=' + mx) + '、' + T('\\mu_y=\\dfrac{' + sumArr(p.y) + '}{' + n + '}=' + my) + '。',
      '把兩排偏差寫出來：' + T('x') + ' 的偏差 ' + T(listTex(dx)) + '，' + T('y') + ' 的偏差 ' + T(listTex(dy)) + '（兩排的總和都是 $0$）。',
      '三個和：' + T('S_{xx}=' + sxx) + '、' + T('S_{yy}=' + syy) + '、' + T('S_{xy}=' + sxy) + '。',
      '代進公式 ' + T('r=\\dfrac{S_{xy}}{\\sqrt{S_{xx}S_{yy}}}=\\dfrac{' + sxy + '}{\\sqrt{' + sxx + '\\times' + syy + '}}=' + dec(rr)) + '。' + solFin(o)];
  };

  L1_SOL.corrSums = function (p, o) {
    var n = p.n, Sxx = p.sxx - p.sx * p.sx / n, Syy = p.syy - p.sy * p.sy / n, Sxy = p.sxy - p.sx * p.sy / n, rr = solF(p.ans);
    return ['三個「和」都要先減掉平均的貢獻：' + T('S_{xx}=\\sum x^2-\\dfrac{(\\sum x)^2}{n}') + '、' + T('S_{yy}=\\sum y^2-\\dfrac{(\\sum y)^2}{n}') + '、' + T('S_{xy}=\\sum xy-\\dfrac{\\sum x\\sum y}{n}') + '。',
      '代入數字：' + T('S_{xx}=' + p.sxx + '-\\dfrac{' + p.sx + '^2}{' + n + '}=' + Sxx) + '、' + T('S_{yy}=' + p.syy + '-\\dfrac{' + p.sy + '^2}{' + n + '}=' + Syy) + '。',
      T('S_{xy}=' + p.sxy + '-\\dfrac{' + p.sx + '\\cdot' + p.sy + '}{' + n + '}=' + Sxy) + '。',
      '最後 ' + T('r=\\dfrac{' + Sxy + '}{\\sqrt{' + Sxx + '\\times' + Syy + '}}=' + dec(rr)) + '。' + solFin(o)];
  };

  L1_SOL.corrTransform = function (p, o) {
    var rr = solF(p.r), lines = [], i;
    for (i = 0; i < 3; i++) {
      var ac = p.ac[i][0] * p.ac[i][1];
      lines.push('(' + (i + 1) + ') ' + T('a=' + p.ac[i][0]) + '、' + T('c=' + p.ac[i][1]) + ' ⟹ ' + T('ac=' + ac) + (ac > 0 ? ' 為正，' + T('r') + ' 不變：' : ' 為負，' + T('r') + ' 變號：') + T('r=' + dec(solF(p.ans[i]))));
    }
    return ['線性變換 ' + T('(ax+b,\\ cy+d)') + ' 只會拉伸或翻轉，不改變資料的關聯強度：平移 ' + T('b') + '、' + T('d') + ' 完全沒影響，只有 ' + T('ac') + ' 的正負決定是否變號（原本 ' + T('r=' + dec(rr)) + '）。',
      lines[0] + '；' + lines[1] + '。',
      lines[2] + '。' + solFin(o)];
  };

  L1_SOL.corrPerfect = function (p, o) {
    var a = solF(p.a), muy = solF(p.ans.mu), sgy = solF(p.ans.sg), aa = Fr.abs(a);
    return ['所有點 ' + T('(x_i,y_i)') + ' 都落在同一條直線上，屬於完全線性相關：' + T('r=' + p.ans.r) + '（斜率 ' + T(dec(a)) + (a.n > 0 ? ' 為正' : ' 為負') + '），最適直線就是這條直線本身。',
      '平均數跟著式子走：' + T('\\mu_y=' + solCoef(a) + '(' + p.mu + ')' + (p.b > 0 ? '+' + p.b : String(p.b)) + '=' + dec(muy)) + '。',
      '標準差只乘上係數的絕對值：' + T('\\sigma_y=|a|\\sigma_x=' + dec(aa) + '\\times' + p.sg + '=' + dec(sgy)) + '。' + solFin(o)];
  };

  /* ── §2-2 最適直線 ── */
  L1_SOL.fitData = function (p, o) {
    var n = p.x.length, mx = solMean(p.x), my = solMean(p.y), sl = solF(p.ans.a), ic = solF(p.ans.b);
    var dx = p.x.map(function (v) { return v - mx; }), dy = p.y.map(function (v) { return v - my; });
    var sxx = 0, sxy = 0, i;
    for (i = 0; i < n; i++) { sxx += dx[i] * dx[i]; sxy += dx[i] * dy[i]; }
    return ['先算重心 ' + T('(\\mu_x,\\mu_y)=(' + mx + ',' + my + ')') + '，並寫出兩排偏差 ' + T(listTex(dx)) + ' 與 ' + T(listTex(dy)) + '。',
      '兩個和：' + T('S_{xx}=' + sxx) + '、' + T('S_{xy}=' + sxy) + '，斜率 ' + T('a=\\dfrac{S_{xy}}{S_{xx}}=' + solDiv(sxy, sxx) + '=' + dec(sl)) + '。',
      '最適直線必過重心：' + T('y-' + my + '=' + solCoef(sl) + '(x-' + mx + ')') + ' ⟹ ' + T(lineTex(sl, ic)) + '。' + solFin(o)];
  };

  L1_SOL.fitStats = function (p, o) {
    var rr = solF(p.r), sl = solF(p.ans.a), ic = solF(p.ans.b), yh = solF(p.ans.yh);
    return ['(1) 斜率 ' + T('=r\\dfrac{\\sigma_y}{\\sigma_x}=' + dec(rr) + '\\times\\dfrac{' + p.sy + '}{' + p.sx + '}=' + dec(sl)) + '。',
      '直線必過重心 ' + T('(' + p.mx + ',' + p.my + ')') + '：' + T('y-' + p.my + '=' + solCoef(sl) + '(x-' + p.mx + ')') + ' ⟹ ' + T(lineTex(sl, ic)) + '。',
      '(2) 預測時直接從重心出發：' + T('\\hat y=' + p.my + '+' + solPre(sl) + '(' + p.x0 + '-' + p.mx + ')=' + dec(yh)) + '。' + solFin(o)];
  };

  L1_SOL.fitCentroid = function (p, o) {
    var a = solF(p.a), my = solF(p.ans.my), rr = solF(p.ans.r);
    return ['(1) 最適直線一定通過重心 ' + T('(\\mu_x,\\mu_y)') + '，所以把 ' + T('x=' + p.mx) + ' 代進直線就是英文的平均數：' + T('\\mu_y=' + solCoef(a) + '(' + p.mx + ')' + (p.b > 0 ? '+' + p.b : String(p.b)) + '=' + dec(my)) + '。',
      '(2) 斜率的公式是 ' + T('a=r\\dfrac{\\sigma_y}{\\sigma_x}') + '，把已知代進去：' + T(dec(a) + '=r\\cdot\\dfrac{' + p.sy + '}{' + p.sx + '}') + '。',
      '兩邊同乘 ' + T('\\dfrac{\\sigma_x}{\\sigma_y}') + ' 反解得 ' + T('r=' + dec(rr)) + '。' + solFin(o)];
  };

  L1_SOL.fitTransform = function (p, o) {
    var rr = solF(p.r), pp = solF(p.p), ss = solF(p.s), sl2 = solF(p.ans.a), ic2 = solF(p.ans.b);
    var sl = Fr.mul(rr, F(p.sy, p.sx));
    var sx2 = Fr.mul(Fr.abs(pp), F(p.sx)), sy2 = Fr.mul(Fr.abs(ss), F(p.sy));
    var mx2 = Fr.add(Fr.mul(pp, F(p.mx)), F(p.q)), my2 = Fr.add(Fr.mul(ss, F(p.my)), F(p.t));
    var r2 = pp.n * ss.n > 0 ? rr : F(-rr.n, rr.d);
    return ['先看變換對統計量的影響：' + T("\\sigma_{x'}=|p|\\sigma_x=" + dec(sx2)) + '、' + T("\\sigma_{y'}=|s|\\sigma_y=" + dec(sy2)) + '；' + T('ps=' + dec(Fr.mul(pp, ss))) + ' 決定相關係數的正負 ⟹ ' + T("r'=" + dec(r2)) + '。',
      '新斜率 ' + T("=r'\\dfrac{\\sigma_{y'}}{\\sigma_{x'}}=" + dec(r2) + '\\times\\dfrac{' + dec(sy2) + '}{' + dec(sx2) + '}=' + dec(sl2)) + '（也等於舊斜率 ' + T(dec(sl)) + ' 乘上 ' + T('\\dfrac{s}{p}') + '）。',
      '新直線必過新重心 ' + T('(' + dec(mx2) + ',' + dec(my2) + ')') + '，代進點斜式整理得 ' + T(lineTex(sl2, ic2).replace(/^y=/, "y'=").replace(/x/, "x'")) + '。' + solFin(o)];
  };

  L1_SOL.stdFit = function (p, o) {
    var rr = solF(p.r), c = solF(p.c), yh = solF(p.ans);
    return ['(1) 標準化之後 ' + T('\\mu=0') + '、' + T('\\sigma=1') + '，所以斜率 ' + T("=r\\cdot\\dfrac{\\sigma_{y''}}{\\sigma_{x''}}=r=" + dec(rr)) + '，而且直線必過原點 ' + T('(0,0)') + '，最適直線是 ' + T("y''=" + dec(rr) + "x''") + '。',
      '(2) 把 ' + T("x''=" + dec(c)) + ' 代進去：' + T("\\hat y''=" + dec(rr) + '\\times(' + dec(c) + ')=' + dec(yh)) + '。' + solFin(o)];
  };

  var META_L1 = [
      ['centralTrio', '§1-1 平均數、中位數、眾數'], ['weightedMean', '§1-1 兩班合併的平均'], ['weightedScore', '§1-1 加權平均：至少要考幾分'], ['freqTable', '§1-1 次數分配表的平均與中位數'], ['meanShift', '§1-1 新增／剔除資料後的平均'],
      ['pctPosition', '§1-2 百分位數取第幾筆'], ['pctData', '§1-2 排序資料的百分位數'], ['pctFreq', '§1-2 「持 k 顆的有 k 位」的百分位數'],
      ['sdBasic', '§1-3 全距、變異數、標準差'], ['sdFromSums', '§1-3 由 Σx、Σx² 求標準差'], ['sumSqFromStats', '§1-3 由 μ、σ 求平方和'], ['addOne', '§1-3 新增一筆資料的影響'], ['mergeTwo', '§1-3 兩組資料合併'],
      ['linearTrans', '§1-4 線性變換 y=ax+b'], ['inverseTrans', '§1-4 由變換前後反推 a、b'], ['zCompare', '§1-4 標準化：跨科比較'], ['zInverse', '§1-4 z 分數與原始分數互換'], ['tScore', '§1-4 T 分數'],
      ['growthRate', '§1-5 平均成長率'], ['growthTotal', '§1-5 由首尾值求平均成長率'],
      ['corrData', '§2-1 由資料算相關係數'], ['corrSums', '§2-1 只給 Σ 的相關係數'], ['corrTransform', '§2-1 線性變換對 r 的影響'], ['corrPerfect', '§2-1 完全線性關係'],
      ['fitData', '§2-2 由資料求最適直線'], ['fitStats', '§2-2 由統計量求最適直線與預測'], ['fitCentroid', '§2-2 由最適直線反推 μ_y 與 r'], ['fitTransform', '§2-2 線性變換後的最適直線'], ['stdFit', '§2-2 標準化後的最適直線']
  ];
  var META_L2 = [
      ['regMissing', '§2 由迴歸直線反推缺失資料'], ['regReverse', '§2 由 r、直線反推 μ_x、σ_x'], ['regBothLines', '§2 兩條迴歸直線：交點與 r²'], ['regUnits', '§2 換單位後的迴歸直線'], ['corrFromSlope', '§2 由斜率反推 σ_y、μ_y'], ['addCentroid', '§2 新增重心那一筆'],
      ['minVarRange', '§1 固定全距的最小變異數'], ['sumSqShift', '§1 由 f(x)=Σ(x−x_i)² 反推 μ、σ'], ['reverseAdd', '§1 新增一筆後 σ 已知，反推那一筆'], ['mergeReverse', '§1 合併結果已知，反推 (x,y)'], ['linearReverse', '§1 把最高分最低分拉到指定值'], ['zRank', '§1 五科 z 分數排名'],
      ['pctFreqSquare', '§1 k² 位／k+1 次的百分位數'], ['growthMixed', '§1 成長率：金額漲幅、反推最後一年'], ['apStats', '§1 等差資料的 μ、P_k、σ²'], ['pairProdVar', '§1 兩兩乘積和求變異數'], ['tThreshold', '§1 T 分數的及格門檻'], ['weightedMin', '§1 兩層加權：期末至少幾分']
  ];
  /* ══════════════════════════════════════════════════════════
     L3　中上（15 型）：每型對應固定題 L3-1～L3-15 的「類似題」
     一維統計量一律用母體定義（σ² = Σ(x−μ)²/n）、百分位數照講義的
     t = nk/100 規則；二維資料沿用本章 makeXY 的偏差設計
     （x 偏差 = k·I、y 偏差 = s(m·I + c·E)，I⊥E 且 ΣI²=ΣE²）
     ⟹ r = m/√(m²+c²) 恰為 ±3/5、±4/5，斜率 = ms/k 為漂亮分數。
     p 只放輸入參數與旗標（答案另放 p.ans，驗算器不讀）。
     ══════════════════════════════════════════════════════════ */
  var L3 = {};

  /* ── 小工具（名稱一律加 l3 前綴） ── */
  function l3asc(a) { return a.slice().sort(function (p, q) { return p - q; }); }
  function l3desc(a) { return a.slice().sort(function (p, q) { return q - p; }); }
  function l3rng(a, b) { var o = [], i; for (i = a; i <= b; i++) o.push(i); return o; }
  function l3cntGe(a, v) { var c = 0, i; for (i = 0; i < a.length; i++) if (a[i] >= v) c++; return c; }
  function l3devs(a, mu) { var o = [], i; for (i = 0; i < a.length; i++) o.push(a[i] - mu); return o; }
  function l3signed(v) { return (v > 0 ? '+' : '') + v; }
  /* c·v + k 的排版（c、k 為整數） */
  function l3lin(c, k, v) {
    var s = (c === 1 ? '' : c === -1 ? '-' : String(c)) + v;
    if (k > 0) s += '+' + k; else if (k < 0) s += String(k);
    return s;
  }
  /* 一般化的直線排版：yv = a·xv + b */
  function l3line(a, b, xv, yv) {
    var s = yv + '=';
    if (Fr.eq(a, F(1))) s += xv; else if (Fr.eq(a, F(-1))) s += '-' + xv; else s += dec(a) + xv;
    if (b.n > 0) s += '+' + dec(b); else if (b.n < 0) s += dec(b);
    return s;
  }
  function l3par(v) { return v < 0 ? '(' + v + ')' : String(v); }
  function l3par(v) { return v < 0 ? '(' + v + ')' : String(v); }
  function l3tExpr(n, k) { return 't=\\dfrac{' + n + '\\times' + k + '}{100}=' + dec(F(n * k, 100)); }
  function l3pc(p) { return (p < 0 ? '-' : '') + Math.abs(p) + '\\%'; }
  function l3f2(h) { var a = Math.abs(h); return (h < 0 ? '-' : '') + Math.floor(a / 100) + '.' + (a % 100 < 10 ? '0' : '') + (a % 100); }
  function l3f1(t) { var a = Math.abs(t); return (t < 0 ? '-' : '') + Math.floor(a / 10) + '.' + (a % 10); }
  function l3nSxy(x, y) { var n = x.length, s = 0, sx = 0, sy = 0, i; for (i = 0; i < n; i++) { s += x[i] * y[i]; sx += x[i]; sy += y[i]; } return n * s - sx * sy; }
  function l3nSxx(x) { var n = x.length, s = 0, q = 0, i; for (i = 0; i < n; i++) { s += x[i]; q += x[i] * x[i]; } return n * q - s * s; }
  /* 二維資料家族：I⊥E、ΣI²=ΣE²=Q ⟹ Sxx=Qk²、Syy=Qs²(m²+c²)、Sxy=Qmks、r=m/√(m²+c²) */
  var L3I4 = [-1, 0, 0, 1], L3E4 = [0, 1, -1, 0];                 /* Q=2 */
  var L3I5 = [-2, -1, 0, 1, 2], L3E5 = [-1, 2, 0, -2, 1];         /* Q=10 */
  var L3I6 = [-2, -1, 0, 0, 1, 2], L3E6 = [0, 0, 2, -1, -2, 1];   /* Q=10 */
  var L3MC = [[3, 4], [4, 3]];
  function l3build(I, E, k, s, m, c, mx, my, pm) {
    var n = I.length, x = [], y = [], j, id, Q = 0;
    for (j = 0; j < n; j++) Q += I[j] * I[j];
    for (j = 0; j < n; j++) { id = pm ? pm[j] : j; x.push(mx + k * I[id]); y.push(my + s * (m * I[id] + c * E[id])); }
    var slope = F(m * s, k);
    return { x: x, y: y, r: F(m, Math.sqrt(m * m + c * c)), slope: slope, icpt: Fr.sub(F(my), Fr.mul(slope, F(mx))),
             mx: mx, my: my, sxx: Q * k * k, syy: Q * s * s * (m * m + c * c), sxy: Q * m * k * s };
  }
  function l3xyPick(r) { var p = r.pick(L3MC); return [p[0] * r.sign(), p[1] * r.sign()]; }

  /* ══ L3-1　由大到小找百分位數（已知門檻以上有幾位，不必全部排序） ══ */
  var L3KP = [55, 60, 62, 64, 65, 66, 68, 70, 72, 75, 76, 80, 84, 85, 88, 90, 92, 95];
  L3.pctTop = function (r) {
    var n = r.pick([20, 25, 30, 40, 50]), i;
    var subj = r.pick(SUBJ), cls = r.pick(['甲', '乙', '丙', '丁', '戊']);
    var okI = [], okN = [];
    for (i = 0; i < L3KP.length; i++) ((n * L3KP[i]) % 100 === 0 ? okI : okN).push(L3KP[i]);
    var v = r.int(0, 2), ks;
    if (v === 0) ks = [r.pick(okI)];
    else if (v === 1) ks = [r.pick(okN)];
    else { ks = [r.pick(okI), r.pick(okN)]; ks.sort(function (p, q) { return p - q; }); }
    var need = 0;
    for (i = 0; i < ks.length; i++) {
      var t = n * ks[i] / 100, rk = (t === Math.floor(t)) ? (n - t + 1) : (n - Math.ceil(t) + 1);
      if (rk > need) need = rk;
    }
    var data, asc, dsc, m0, X, m, tries = 0;
    do {
      data = []; for (i = 0; i < n; i++) data.push(r.int(48, 100));
      asc = l3asc(data); dsc = l3desc(data);
      m0 = Math.min(need + r.int(1, 3), n - 1); X = dsc[m0 - 1]; m = l3cntGe(data, X); tries++;
    } while (m > n - 2 && tries < 25);
    var ps = ks.map(function (k) { return pctF(asc, k); });
    var segs = [], hs = [];
    for (i = 0; i < ks.length; i++) {
      var k = ks[i], t2 = n * k / 100, isInt = (t2 === Math.floor(t2));
      if (isInt) segs.push(T('P_{' + k + '}=\\dfrac{' + asc[t2 - 1] + '+' + asc[t2] + '}{2}=' + dec(ps[i])));
      else segs.push(T('P_{' + k + '}=' + dec(ps[i])));
      hs.push('$' + l3tExpr(n, k) + '$ ' + (isInt ? '是整數 ⟹ $P_{' + k + '}$ 取第 $' + t2 + '$ 小與第 $' + (t2 + 1) + '$ 小的平均，也就是第 $' + (n - t2 + 1) + '$ 大與第 $' + (n - t2) + '$ 大的平均' : '不是整數 ⟹ 無條件進位，$P_{' + k + '}$ 取第 $' + Math.ceil(t2) + '$ 小，也就是第 $' + (n - Math.ceil(t2) + 1) + '$ 大'));
    }
    return { q: '某次' + subj + '考試' + cls + '班 ' + T(String(n)) + ' 位同學的成績為 ' + T(listTex(data)) + '。已知 ' + T(String(X)) + ' 分（含）以上恰有 ' + T(String(m)) + ' 位，求此次成績的'
               + (ks.length === 1 ? '第 ' + T(String(ks[0])) + ' 百分位數。' : ' (1) 第 ' + T(String(ks[0])) + ' 百分位數　(2) 第 ' + T(String(ks[1])) + ' 百分位數。'),
             a: ks.length === 1 ? segs[0] : '(1) ' + segs[0] + '　(2) ' + segs[1],
             h: hs.join('；') + '。' + T(String(X)) + ' 分（含）以上恰有 ' + T(String(m)) + ' 位，所以只要由大到小數出前 ' + T(String(m)) + ' 個就夠，不必把 ' + T(String(n)) + ' 筆全部排序。',
             p: { n: n, ks: ks, v: v, thr: X, cnt: m, ans: ps.map(fr2) } };
  };

  /* ══ L3-2　亂序資料由小排到第 t 筆的百分位數 ══ */
  L3.pctSort = function (r) {
    var n = r.pick([24, 30, 36, 40, 45, 50, 60]), i;
    var subj = r.pick(SUBJ), unit = r.pick([['某班', '位學生', '成績'], ['某社團', '位團員', '每週練習時數'], ['某工廠', '個零件', '重量（公克）']]);
    var okI = [], okN = [], LO = [10, 12, 15, 20, 24, 25, 30, 35, 40, 45, 50, 55, 60];
    for (i = 0; i < LO.length; i++) ((n * LO[i]) % 100 === 0 ? okI : okN).push(LO[i]);
    var v = r.int(0, 2), ks;
    if (v === 0) ks = [r.pick(okI)];
    else if (v === 1) ks = [r.pick(okN)];
    else { ks = [r.pick(okI), 50]; if (ks[0] === 50) ks[0] = r.pick(okN); ks.sort(function (p, q) { return p - q; }); }
    var hi = unit[2] === '成績' ? 99 : (unit[2] === '重量（公克）' ? 60 : 20);
    var data = []; for (i = 0; i < n; i++) data.push(r.int(unit[2] === '成績' ? 2 : 1, hi));
    var asc = l3asc(data), ps = ks.map(function (k) { return pctF(asc, k); });
    var segs = [], hs = [], mx = 0;
    for (i = 0; i < ks.length; i++) {
      var k = ks[i], t2 = n * k / 100, isInt = (t2 === Math.floor(t2)), nd = isInt ? t2 + 1 : Math.ceil(t2);
      if (nd > mx) mx = nd;
      segs.push(isInt ? T('P_{' + k + '}=\\dfrac{' + asc[t2 - 1] + '+' + asc[t2] + '}{2}=' + dec(ps[i])) : T('P_{' + k + '}=' + dec(ps[i])));
      hs.push('$' + l3tExpr(n, k) + '$ ' + (isInt ? '是整數 ⟹ 取第 $' + t2 + '$ 小與第 $' + (t2 + 1) + '$ 小的平均' : '不是整數 ⟹ 無條件進位，取第 $' + Math.ceil(t2) + '$ 小'));
    }
    return { q: unit[0] + ' ' + T(String(n)) + ' ' + unit[1] + '的' + unit[2] + '依序為 ' + T(listTex(data)) + '。求'
               + (ks.length === 1 ? '這 ' + T(String(n)) + ' 筆數據的第 ' + T(String(ks[0])) + ' 百分位數。' : ' (1) 第 ' + T(String(ks[0])) + ' 百分位數　(2) 第 ' + T(String(ks[1])) + ' 百分位數。'),
             a: ks.length === 1 ? segs[0] : '(1) ' + segs[0] + '　(2) ' + segs[1],
             h: hs.join('；') + '。所以由小到大只要排到第 ' + T(String(mx)) + ' 筆就可以停，' + T(String(n)) + ' 筆不必全排。',
             p: { n: n, ks: ks, v: v, ans: ps.map(fr2) } };
  };

  /* ══ L3-3　五級評分的次數分配表：累積次數找百分位數（有一個恰卡在交界） ══ */
  var L3LV = [['某餐廳的網路評論共', '則', '星', '評論的星數'],
              ['某課程的回饋問卷共', '份', '分', '滿意度'],
              ['某 App 的使用者評分共', '筆', '分', '評分'],
              ['某次活動的滿意度調查共', '人', '分', '滿意度']];
  L3.pctLevels = function (r) {
    /* N 取「不是 100 的倍數」的數，才能同時存在 t 為整數與非整數的 k */
    var ctx = r.pick(L3LV), N = r.pick([150, 240, 250, 280, 320, 350, 360, 420, 450, 480]), i;
    var okI = [], okN = [], POOL = [4, 5, 8, 10, 12, 15, 16, 20, 24, 25, 28, 30, 32, 35, 36, 40, 44, 45, 48, 50, 55, 60, 64, 65, 70, 72, 75, 80];
    for (i = 0; i < POOL.length; i++) {
      var t = N * POOL[i] / 100;
      if (t === Math.floor(t)) { if (t >= 4 && t <= N - 4) okI.push(POOL[i]); }
      else if (Math.ceil(t) >= 2 && Math.ceil(t) <= N - 1) okN.push(POOL[i]);
    }
    if (!okI.length) okI = [50];
    if (!okN.length) okN = okI;
    var v = r.int(0, 2), k2 = r.pick(okI), t2 = N * k2 / 100;
    /* 讓第 j 級的累積次數恰為 t2（邊界） */
    var j = r.int(1, 4), cnt = [], left = t2, s;
    for (i = 0; i < j - 1; i++) { s = r.int(1, Math.max(1, Math.floor(left / (j - i)))); cnt.push(s); left -= s; }
    cnt.push(left);
    var rest = N - t2;
    for (i = j; i < 4; i++) { s = r.int(1, Math.max(1, Math.floor(rest / (5 - i)))); cnt.push(s); rest -= s; }
    cnt.push(rest);                                     /* 第 5 級 */
    var k1 = r.pick(okN), t1 = N * k1 / 100;
    var data = [], lv;
    for (lv = 1; lv <= 5; lv++) for (i = 0; i < cnt[lv - 1]; i++) data.push(lv);
    var cum = [], acc = 0; for (lv = 0; lv < 5; lv++) { acc += cnt[lv]; cum.push(acc); }
    var p1 = pctF(data, k1), p2 = pctF(data, k2), me = pctF(data, 50), mu = meanF(data);
    var head = ctx[0] + ' ' + T(String(N)) + ' ' + ctx[1] + '，' + ctx[3] + '由低到高計為 ' + T('1') + ' 至 ' + T('5') + ' ' + ctx[2] + '。統計結果為：'
      + [1, 2, 3, 4].map(function (u) { return T(String(u)) + ' ' + ctx[2] + ' ' + T(String(cnt[u - 1])) + ' ' + ctx[1]; }).join('、')
      + '，其餘皆為 ' + T('5') + ' ' + ctx[2] + '。';
    var hcum = '累積次數為 ' + T(listTex(cum)) + '；' + '$' + l3tExpr(N, k2) + '$ 恰好等於第 ' + T(String(j)) + ' 級的累積次數 ⟹ 第 ' + T(String(t2)) + ' 筆是 ' + T(String(j)) + ' ' + ctx[2] + '、第 ' + T(String(t2 + 1)) + ' 筆是 ' + T(String(j + 1)) + ' ' + ctx[2] + '，要取兩者的平均；';
    var h1 = '$' + l3tExpr(N, k1) + '$ 不是整數 ⟹ 無條件進位取第 ' + T(String(Math.ceil(t1))) + ' 筆。';
    if (v === 0) return { q: head + '求第 ' + T(String(k1)) + ' 百分位數與第 ' + T(String(k2)) + ' 百分位數。',
                          a: T('P_{' + k1 + '}=' + dec(p1)) + '、' + T('P_{' + k2 + '}=' + dec(p2)),
                          h: hcum + h1, p: { N: N, cnt: cnt.slice(0, 4), k1: k1, k2: k2, v: v, ans: [fr2(p1), fr2(p2)] } };
    if (v === 1) return { q: head + '求第 ' + T(String(k2)) + ' 百分位數與中位數。',
                          a: T('P_{' + k2 + '}=' + dec(p2)) + '、' + T('Me=' + dec(me)),
                          h: hcum + '中位數就是 $P_{50}$：$' + l3tExpr(N, 50) + '$，再用同一張累積次數表找。',
                          p: { N: N, cnt: cnt.slice(0, 4), k1: 50, k2: k2, v: v, ans: [fr2(p2), fr2(me)] } };
    return { q: head + '求第 ' + T(String(k1)) + ' 百分位數與全部 ' + T(String(N)) + ' ' + ctx[1] + '的平均' + ctx[2] + '數。',
             a: T('P_{' + k1 + '}=' + dec(p1)) + '、' + T('\\mu=' + dec(mu)),
             h: hcum.slice(0, hcum.indexOf('；') + 1) + h1 + '平均 $=\\dfrac{\\sum(\\text{級數}\\times\\text{次數})}{' + N + '}$。',
             p: { N: N, cnt: cnt.slice(0, 4), k1: k1, k2: k2, v: v, ans: [fr2(p1), fr2(mu)] } };
  };

  /* ══ L3-4　只給 Σx 與 Σx²：σ² = 平方的平均 − 平均的平方 ══ */
  L3.sdSums = function (r) {
    var n = r.pick([4, 4, 5, 5, 6, 8, 9, 10, 12, 15, 16, 20, 25]);
    var mu = r.int(2, 30), vv = r.pick([1, 4, 9, 16, 25, 36, 49, 64, 2, 3, 5, 6, 8, 10, 12, 15, 18, 20, 24, 27, 32, 40, 45, 50]);
    var S = n * mu, Q = n * (vv + mu * mu), v = r.int(0, 2);
    var a = mu + r.pick([-6, -5, -4, -3, -2, 2, 3, 4, 5, 6]);
    if (a < 1) a = mu + (mu - a);                       /* a 必須是正的，否則題幹會寫出 (x_1--4)^2 */
    var sa = n * vv + n * (mu - a) * (mu - a);
    var lhs1 = n <= 5 ? l3rng(1, n).map(function (i) { return 'x_' + i; }).join('+') : 'x_1+x_2+\\cdots+x_{' + n + '}';
    var lhs2 = n <= 5 ? l3rng(1, n).map(function (i) { return 'x_' + i + '^2'; }).join('+') : 'x_1^2+x_2^2+\\cdots+x_{' + n + '}^2';
    var head = '已知 ' + T(String(n)) + ' 個實數 ' + T('x_1,x_2,\\dots,x_{' + n + '}') + ' 滿足 ' + T(lhs1 + '=' + S) + ' 且 ' + T(lhs2 + '=' + Q) + '。';
    var base = '$\\mu=\\dfrac{' + S + '}{' + n + '}=' + mu + '$；$\\sigma^2=\\dfrac{\\sum x_i^2}{n}-\\mu^2=\\dfrac{' + Q + '}{' + n + '}-' + mu + '^2=' + vv + '$（平方的平均減平均的平方，不必知道每一筆是多少）。';
    if (v === 0) return { q: head + '求這 ' + T(String(n)) + ' 個數的標準差。',
                          a: T('\\sigma^2=' + vv) + ' ⟹ ' + T('\\sigma=' + sqrtBoth(F(vv))),
                          h: base, p: { n: n, S: S, Q: Q, v: v, ans: { va: vv } } };
    if (v === 1) return { q: head + '求 (1) 這 ' + T(String(n)) + ' 個數的變異數與標準差　(2) ' + T('(x_1-' + a + ')^2+(x_2-' + a + ')^2+\\cdots+(x_{' + n + '}-' + a + ')^2') + ' 的值。',
                          a: '(1) ' + T('\\sigma^2=' + vv) + '、' + T('\\sigma=' + sqrtBoth(F(vv))) + '　(2) ' + T(n + '\\sigma^2+' + n + '(\\mu-' + a + ')^2=' + (n * vv) + '+' + (n * (mu - a) * (mu - a)) + '=' + sa),
                          h: base + '第 (2) 小題用 $\\sum(x_i-a)^2=n\\sigma^2+n(\\mu-a)^2$：把「對平均的平方和 $' + (n * vv) + '$」再加上「平均離 $' + a + '$ 有 $' + Math.abs(mu - a) + '$ 的 $' + n + '$ 倍平方」。',
                          p: { n: n, S: S, Q: Q, a: a, v: v, ans: { va: vv, sa: sa } } };
    return { q: head + '求 (1) 這 ' + T(String(n)) + ' 個數的標準差　(2) ' + T('f(c)=(x_1-c)^2+(x_2-c)^2+\\cdots+(x_{' + n + '}-c)^2') + ' 的最小值，以及此時 ' + T('c') + ' 的值。',
             a: '(1) ' + T('\\sigma=' + sqrtBoth(F(vv))) + '　(2) 最小值 ' + T(n + '\\sigma^2=' + (n * vv)) + '，此時 ' + T('c=\\mu=' + mu),
             h: base + '第 (2) 小題：$f(c)=n(c-\\mu)^2+n\\sigma^2$，開口向上 ⟹ $c=\\mu=' + mu + '$ 時最小，最小值 $=' + n + '\\times' + vv + '=' + (n * vv) + '$。',
             p: { n: n, S: S, Q: Q, v: v, ans: { va: vv, mn: n * vv, c: mu } } };
  };

  /* ══ L3-5　平方的平均 = σ² + μ²（不是 μ²） ══ */
  L3.sqMean = function (r) {
    var v = r.int(0, 2);
    if (v === 0) {                                     /* BMI 型 */
      var n = r.pick([8, 10, 12, 15, 20, 25]), bmi = r.int(18, 25);
      var mh = r.pick([F(15, 10), F(16, 10), F(165, 100), F(17, 10), F(175, 100), F(18, 10)]);
      var sh = r.pick([F(5, 100), F(1, 10), F(15, 100), F(2, 10)]);
      var e = Fr.add(Fr.mul(sh, sh), Fr.mul(mh, mh)), mw = Fr.mul(F(bmi), e);
      return { q: T('\\text{BMI}=\\dfrac{w}{h^2}') + '（' + T('w') + ' 為體重公斤、' + T('h') + ' 為身高公尺）。某健身房 ' + T(String(n)) + ' 位會員的 BMI 皆為 ' + T(String(bmi)) + '，身高的平均數為 ' + T(dec(mh)) + ' 公尺、標準差為 ' + T(dec(sh)) + ' 公尺。求這 ' + T(String(n)) + ' 位會員體重的算術平均數。',
               a: T('\\dfrac{1}{' + n + '}\\sum h_i^2=\\sigma_h^2+\\mu_h^2=' + dec(Fr.mul(sh, sh)) + '+' + dec(Fr.mul(mh, mh)) + '=' + dec(e)) + ' ⟹ ' + T('\\mu_w=' + bmi + '\\times' + dec(e) + '=' + dec(mw)) + ' 公斤',
               h: '$w_i=' + bmi + 'h_i^2$ 不是線性變換，所以 $\\mu_w=' + bmi + '\\cdot\\dfrac{\\sum h_i^2}{' + n + '}=' + bmi + '(\\sigma_h^2+\\mu_h^2)$；若寫成 $' + bmi + '\\times' + dec(mh) + '^2=' + dec(Fr.mul(F(bmi), Fr.mul(mh, mh))) + '$ 就是漏掉 $\\sigma_h^2=' + dec(Fr.mul(sh, sh)) + '$ 那一項。',
               p: { v: 0, n: n, bmi: bmi, mh: fr2(mh), sh: fr2(sh), ans: fr2(mw) } };
    }
    if (v === 1) {                                     /* 正方形面積型 */
      var n1 = r.pick([6, 8, 10, 12, 16, 20]), ms = r.pick([F(6), F(8), F(10), F(12), F(15), F(75, 10), F(125, 10)]);
      var ss = r.pick([F(1), F(2), F(3), F(5, 10), F(15, 10), F(25, 10)]);
      var e1 = Fr.add(Fr.mul(ss, ss), Fr.mul(ms, ms));
      var ob = r.pick([['正方形', '邊長', '面積', '平方公分', '公分'], ['圓形貼紙', '半徑', '面積除以 $\\pi$ 之值', '平方公分', '公分']]);
      return { q: '某組 ' + T(String(n1)) + ' 個' + ob[0] + '的' + ob[1] + '（' + ob[4] + '）平均數為 ' + T(dec(ms)) + '、標準差為 ' + T(dec(ss)) + '。求這 ' + T(String(n1)) + ' 個' + ob[0] + '的' + ob[2] + '的算術平均數。',
               a: T('\\dfrac{1}{' + n1 + '}\\sum x_i^2=\\sigma^2+\\mu^2=' + dec(Fr.mul(ss, ss)) + '+' + dec(Fr.mul(ms, ms)) + '=' + dec(e1)) + ' ' + ob[3],
               h: '面積是' + ob[1] + '的<b>平方</b>，平方的平均 $=\\sigma^2+\\mu^2=' + dec(Fr.mul(ss, ss)) + '+' + dec(Fr.mul(ms, ms)) + '$，不是 $\\mu^2=' + dec(Fr.mul(ms, ms)) + '$——平方不是線性變換。',
               p: { v: 1, n: n1, mu: fr2(ms), sg: fr2(ss), ans: fr2(e1) } };
    }
    var n2 = r.pick([10, 15, 20, 24, 30]), aa = r.pick([F(2), F(3), F(5), F(1, 2), F(4), F(10)]);
    var bb = r.nz(-20, 30), mu2 = r.int(3, 14), sg2 = r.pick([1, 2, 3, 4, 5]);
    var e2 = F(sg2 * sg2 + mu2 * mu2), my2 = Fr.add(Fr.mul(aa, e2), F(bb));
    return { q: '某 ' + T(String(n2)) + ' 筆資料 ' + T('x') + ' 的平均數為 ' + T(String(mu2)) + '、標準差為 ' + T(String(sg2)) + '。令 ' + T('y=' + (Fr.eq(aa, F(1)) ? '' : dec(aa)) + 'x^2' + (bb > 0 ? '+' + bb : String(bb))) + '，求 ' + T('y') + ' 的算術平均數。',
             a: T('\\dfrac{\\sum x_i^2}{' + n2 + '}=\\sigma^2+\\mu^2=' + (sg2 * sg2) + '+' + (mu2 * mu2) + '=' + dec(e2)) + ' ⟹ ' + T('\\mu_y=' + dec(aa) + '\\times' + dec(e2) + (bb > 0 ? '+' + bb : String(bb)) + '=' + dec(my2)),
             h: '$y$ 含有 $x^2$，不能直接代 $\\mu_x$：先用 $\\dfrac{\\sum x_i^2}{' + n2 + '}=\\sigma^2+\\mu^2=' + (sg2 * sg2) + '+' + (mu2 * mu2) + '$，再乘 $' + dec(aa) + '$、加 $' + bb + '$。',
             p: { v: 2, n: n2, a: fr2(aa), b: bb, mu: mu2, sg: sg2, ans: fr2(my2) } };
  };

  /* ══ L3-6　新增一筆恰等於平均：平方和不變、只有分母變大 ══ */
  /* [n, t]：σ'=t 為整數、σ²=(n+1)t²/n 也是整數（驗算：n·σ²/(n+1)=t²） */
  var L3ADD = [[8, 4], [9, 3], [10, 10], [11, 11], [12, 6], [13, 13], [14, 14], [15, 15], [16, 4], [18, 6], [19, 19], [21, 21],
               [20, 10], [20, 20], [24, 12], [25, 5], [27, 9], [28, 14], [32, 8], [36, 6], [45, 15], [48, 12], [49, 7],
               [50, 10], [54, 18], [63, 21], [64, 8], [72, 12], [80, 20], [98, 14]];
  L3.addAtMean = function (r) {
    var row = r.pick(L3ADD), n = row[0], t = row[1], vv = (n + 1) * t * t / n;
    var who = r.pick(['小武', '小安', '小柏', '小玲', '阿哲']), sub = r.pick(SUBJ);
    var mu = r.int(Math.max(2 * t, 50), Math.min(100 - 2 * t, 82));
    if (mu < 2 * t) mu = 2 * t + r.int(0, 5);
    var v = r.int(0, 2), rea = r.pick(['因病請假未參加', '因公假未參加', '因隔離未參加', '當天遲到未參加']);
    var head = who + rea + sub + '段考。其餘 ' + T(String(n)) + ' 人的成績平均為 ' + T(String(mu)) + ' 分';
    if (v === 0) return { q: head + '、標準差為 ' + T('\\sqrt{' + vv + '}') + ' 分。' + who + '補考恰得 ' + T(String(mu)) + ' 分，求全班 ' + T(String(n + 1)) + ' 人成績的標準差。',
                          a: T('\\sigma\'^2=\\dfrac{' + n + '\\times' + vv + '}{' + (n + 1) + '}=' + (t * t)) + ' ⟹ ' + T('\\sigma\'=' + t) + ' 分',
                          h: '新增的那一筆恰等於平均 ⟹ 平均仍是 $' + mu + '$、偏差平方和仍是 $' + n + '\\sigma^2=' + (n * vv) + '$（那一筆的偏差是 $0$），只有筆數由 $' + n + '$ 變成 $' + (n + 1) + '$：$\\sigma\'^2=\\dfrac{' + (n * vv) + '}{' + (n + 1) + '}$。',
                          p: { v: 0, n: n, mu: mu, va: vv, ans: { va2: t * t, sd2: t } } };
    if (v === 1) return { q: head + '、變異數為 ' + T(String(vv)) + '。' + who + '補考恰得 ' + T(String(mu)) + ' 分（與原本的平均相同），求全班 ' + T(String(n + 1)) + ' 人成績的平均數、變異數與標準差，並說明標準差變大還是變小。',
                          a: T('\\mu\'=' + mu) + '（不變）、' + T('\\sigma\'^2=\\dfrac{' + n + '\\times' + vv + '}{' + (n + 1) + '}=' + (t * t)) + '、' + T('\\sigma\'=' + t) + '；標準差<b>變小</b>',
                          h: '平方和 $=' + n + '\\times' + vv + '=' + (n * vv) + '$ 完全沒有增加，分母卻從 $' + n + '$ 變成 $' + (n + 1) + '$ ⟹ 變異數乘上 $\\dfrac{' + n + '}{' + (n + 1) + '}$ 一定變小。',
                          p: { v: 1, n: n, mu: mu, va: vv, ans: { va2: t * t, sd2: t } } };
    return { q: head + '。' + who + '補考恰得 ' + T(String(mu)) + ' 分，此時全班 ' + T(String(n + 1)) + ' 人成績的標準差為 ' + T(String(t)) + ' 分。求原本那 ' + T(String(n)) + ' 人成績的標準差。',
             a: T('\\sigma^2=\\dfrac{' + (n + 1) + '\\times' + (t * t) + '}{' + n + '}=' + vv) + ' ⟹ ' + T('\\sigma=' + sqrtBoth(F(vv))) + ' 分',
             h: '倒過來想：新增的一筆偏差為 $0$ ⟹ 兩次的偏差平方和相同，$' + n + '\\sigma^2=' + (n + 1) + '\\sigma\'^2=' + (n + 1) + '\\times' + (t * t) + '=' + ((n + 1) * t * t) + '$。',
             p: { v: 2, n: n, mu: mu, sd2: t, ans: { va: vv } } };
  };

  /* ══ L3-7　合併後的 σ 已知，反求其中一組的 σ ══ */
  L3.mergeSolveSd = function (r) {
    var NP = [10, 12, 15, 16, 20, 24, 25, 30, 32, 36, 40, 45, 50, 60];
    var n1, n2, g, u, mu, m1, m2, d1, d2, kn, sk, S = 10, vu = 60, cand, tries = 0, ok = false;
    do {
      n1 = r.pick(NP); n2 = r.pick(NP); g = gcd(n1, n2); u = r.nz(-4, 4);
      d1 = (n2 / g) * u; d2 = -(n1 / g) * u; mu = r.int(58, 74);
      m1 = mu + d1; m2 = mu + d2; kn = r.int(0, 1); sk = r.pick([2, 3, 4, 5, 6, 8, 10, 12]);
      cand = [];
      if (Math.abs(d1) <= 15 && Math.abs(d2) <= 15 && m1 >= 35 && m1 <= 92 && m2 >= 35 && m2 <= 92) {
        var nk = kn === 0 ? n1 : n2, nu = kn === 0 ? n2 : n1, dk = kn === 0 ? d1 : d2, du = kn === 0 ? d2 : d1, mv = kn === 0 ? m2 : m1;
        for (var SS = 5; SS <= 24; SS++) {
          var num = (n1 + n2) * SS * SS - nk * (sk * sk + dk * dk);
          if (num <= 0 || num % nu !== 0) continue;
          var w = num / nu - du * du;
          if (w >= 4 && w <= 400 && 4 * w <= mv * mv && mv + 2 * Math.sqrt(w) <= 104) cand.push([SS, w]);
        }
      }
      tries++;
    } while (cand.length === 0 && tries < 60);
    if (cand.length === 0) { n1 = 30; n2 = 20; mu = 66; d1 = -6; d2 = 9; m1 = 60; m2 = 75; kn = 1; sk = 5; cand = [[10, 60]]; }
    var pk = r.pick(cand); S = pk[0]; vu = pk[1];
    var N = n1 + n2, lab = ['甲', '乙'], un = kn === 0 ? 1 : 0;
    var nk2 = kn === 0 ? n1 : n2, dk2 = kn === 0 ? d1 : d2, nu2 = un === 0 ? n1 : n2, du2 = un === 0 ? d1 : d2;
    var mk = kn === 0 ? m1 : m2, mu2 = un === 0 ? m1 : m2;
    var sg = '\\sigma_{\\text{' + lab[un] + '}}';
    var v = r.int(0, 2), sub = r.pick(SUBJ);
    var muTex = '\\mu=\\dfrac{' + n1 + '(' + m1 + ')+' + n2 + '(' + m2 + ')}{' + N + '}=' + mu;
    var eq = '\\dfrac{' + nu2 + '[' + sg + '^2+(' + mu2 + '-' + mu + ')^2]+' + nk2 + '[' + sk + '^2+(' + mk + '-' + mu + ')^2]}{' + N + '}=' + (v === 2 ? S * S : S + '^2');
    var head = lab[0] + '組 ' + T(String(n1)) + ' 人的' + sub + '平均為 ' + T(String(m1)) + ' 分' + (kn === 0 ? '、標準差為 ' + T(String(sk)) + ' 分' : '') + '；'
      + lab[1] + '組 ' + T(String(n2)) + ' 人的平均為 ' + T(String(m2)) + ' 分' + (kn === 1 ? '、標準差為 ' + T(String(sk)) + ' 分' : '') + '。';
    var hbase = '先算合併平均 $' + muTex + '$；再把 $' + sg + '^2$ 當唯一的未知數代進合併變異數公式 $\\sigma^2=\\dfrac{n_1[\\sigma_1^2+(\\mu_1-\\mu)^2]+n_2[\\sigma_2^2+(\\mu_2-\\mu)^2]}{n_1+n_2}$，兩組離合併平均分別差 $' + Math.abs(du2) + '$ 與 $' + Math.abs(dk2) + '$。';
    if (v === 2) return { q: head + '兩組合併後 ' + T(String(N)) + ' 人的變異數為 ' + T(String(S * S)) + '，求' + lab[un] + '組的標準差。',
                          a: T(muTex) + '；' + T(eq) + ' ⟹ ' + T(sg + '^2=' + vu) + ' ⟹ ' + T(sg + '=' + sqrtBoth(F(vu))) + ' 分',
                          h: hbase + '注意題目給的是<b>變異數</b> $' + (S * S) + '$，不用再平方。',
                          p: { v: 2, n1: n1, m1: m1, n2: n2, m2: m2, kn: kn, sk: sk, cv: S * S, ans: { mu: mu, va: vu } } };
    if (v === 1) return { q: head + '兩組合併後 ' + T(String(N)) + ' 人的標準差為 ' + T(String(S)) + ' 分，求' + lab[un] + '組的變異數與標準差。',
                          a: T(muTex) + '；' + T(eq) + ' ⟹ ' + T(sg + '^2=' + vu) + '、' + T(sg + '=' + sqrtBoth(F(vu))) + ' 分',
                          h: hbase, p: { v: 1, n1: n1, m1: m1, n2: n2, m2: m2, kn: kn, sk: sk, cs: S, ans: { mu: mu, va: vu } } };
    return { q: head + '兩組合併後 ' + T(String(N)) + ' 人的標準差為 ' + T(String(S)) + ' 分，求' + lab[un] + '組的標準差。',
             a: T(muTex) + '；' + T(eq) + ' ⟹ ' + T(sg + '^2=' + vu) + ' ⟹ ' + T(sg + '=' + sqrtBoth(F(vu))) + ' 分',
             h: hbase, p: { v: 0, n1: n1, m1: m1, n2: n2, m2: m2, kn: kn, sk: sk, cs: S, ans: { mu: mu, va: vu } } };
  };

  /* ══ L3-8　兩科標準化分數相差 d ⟹ 把差乘回 σ 再補上平均差 ══ */
  L3.zGap = function (r) {
    var sub = r.shuffle(SUBJ).slice(0, 2), who = r.pick(NAMES);
    var v = r.int(0, 2), m1, m2, sg, d, diff, tries = 0;
    if (v <= 1) {
      do {
        m1 = r.int(55, 82); m2 = r.int(55, 82); sg = r.pick([4, 6, 8, 10]);
        d = r.pick([F(1), F(2), F(3), F(1, 2), F(3, 2), F(5, 2)]);
        diff = Fr.add(Fr.mul(d, F(sg)), F(m1 - m2)); tries++;
      } while ((Fr.toNum(diff) < 3 || Fr.toNum(diff) > 30 || diff.d !== 1) && tries < 60);
      if (diff.d !== 1 || Fr.toNum(diff) < 3) { m1 = 70; m2 = 68; sg = 4; d = F(2); diff = F(10); }
      var head = '某班' + sub[0] + '成績的平均數為 ' + T(String(m1)) + ' 分、標準差為 ' + T(String(sg)) + ' 分；' + sub[1] + '成績的平均數為 ' + T(String(m2)) + ' 分、標準差也是 ' + T(String(sg)) + ' 分。';
      var hb = '$z_1-z_2=\\dfrac{x_1-' + m1 + '}{' + sg + '}-\\dfrac{x_2-' + m2 + '}{' + sg + '}=\\dfrac{(x_1-x_2)-(' + m1 + '-' + m2 + ')}{' + sg + '}=' + dec(d) + '$：兩科 $\\sigma$ 相同時可以先通分，$(x_1-x_2)-(' + (m1 - m2) + ')=' + (Fr.eq(d, F(1)) ? '' : dec(d) + '\\times') + sg + '=' + dec(Fr.mul(d, F(sg))) + '$。';
      if (v === 0) return { q: head + who + '的' + sub[0] + '標準化分數比' + sub[1] + '標準化分數多 ' + T(dec(d)) + '，求' + who + '的' + sub[0] + '原始成績比' + sub[1] + '原始成績多幾分。',
                            a: T('(x_1-x_2)-(' + (m1 - m2) + ')=' + dec(Fr.mul(d, F(sg)))) + ' ⟹ ' + T('x_1-x_2=' + dec(diff)) + ' 分',
                            h: hb, p: { v: 0, m1: m1, m2: m2, sg: sg, d: fr2(d), ans: fr2(diff) } };
      var x2 = m2 + sg * r.pick([-2, -1, 0, 1]) + r.pick([0, 1, 2]);
      while (x2 + Fr.toNum(diff) > 100) x2 -= sg;
      var x1 = Fr.add(F(x2), diff);
      return { q: head + who + '的' + sub[0] + '標準化分數比' + sub[1] + '標準化分數多 ' + T(dec(d)) + '，且' + who + '的' + sub[1] + '原始成績為 ' + T(String(x2)) + ' 分。求' + who + '的' + sub[0] + '原始成績。',
               a: T('x_1-x_2=' + (Fr.eq(d, F(1)) ? '' : dec(d) + '\\times') + sg + '+(' + (m1 - m2) + ')=' + dec(diff)) + ' ⟹ ' + T('x_1=' + x2 + '+' + dec(diff) + '=' + dec(x1)) + ' 分',
               h: hb + '再把 $x_2=' + x2 + '$ 加上這個差。',
               p: { v: 1, m1: m1, m2: m2, sg: sg, d: fr2(d), x2: x2, ans: fr2(x1) } };
    }
    var s1 = r.pick([4, 5, 8, 10]), s2 = r.pick([4, 5, 6, 8, 12]);
    if (s1 === s2) s2 = s1 === 4 ? 8 : 4;
    var mm1 = r.int(55, 80), mm2 = r.int(55, 80), dd = r.pick([F(1), F(2), F(1, 2), F(3, 2), F(-1), F(-2), F(-1, 2)]);
    var xx1 = mm1 + s1 * r.pick([-2, -1, 1, 2]), z1, z2, xx2, tr = 0;
    do {
      if (tr) { xx1 = mm1 + s1 * r.pick([-2, -1, 1, 2]); dd = r.pick([F(1), F(2), F(1, 2), F(3, 2), F(-1), F(-2)]); }
      z1 = F(xx1 - mm1, s1); z2 = Fr.sub(z1, dd); xx2 = Fr.add(F(mm2), Fr.mul(z2, F(s2))); tr++;
    } while ((Fr.toNum(xx2) < 10 || Fr.toNum(xx2) > 100 || xx1 > 100 || xx1 < 10) && tr < 40);
    if (Fr.toNum(xx2) < 0 || Fr.toNum(xx2) > 100 || xx1 > 100) { mm1 = 70; mm2 = 65; s1 = 10; s2 = 5; xx1 = 80; dd = F(1); z1 = F(1); z2 = F(0); xx2 = F(65); }
    return { q: '某班' + sub[0] + '成績的平均數為 ' + T(String(mm1)) + ' 分、標準差為 ' + T(String(s1)) + ' 分；' + sub[1] + '成績的平均數為 ' + T(String(mm2)) + ' 分、標準差為 ' + T(String(s2)) + ' 分。'
               + who + '的' + sub[0] + '考 ' + T(String(xx1)) + ' 分，且他的' + sub[0] + '標準化分數比' + sub[1] + '標準化分數多 ' + T(dec(dd)) + '。求' + who + '的' + sub[1] + '原始成績。',
             a: T('z_1=\\dfrac{' + xx1 + '-' + mm1 + '}{' + s1 + '}=' + dec(z1)) + ' ⟹ ' + T('z_2=' + dec(z1) + '-(' + dec(dd) + ')=' + dec(z2)) + ' ⟹ ' + T('x_2=' + mm2 + '+(' + dec(z2) + ')(' + s2 + ')=' + dec(xx2)) + ' 分',
             h: '兩科 $\\sigma$ 不同，不能直接把分數差乘回去：先算 $z_1=\\dfrac{' + xx1 + '-' + mm1 + '}{' + s1 + '}=' + dec(z1) + '$，再由 $z_1-z_2=' + dec(dd) + '$ 得 $z_2=' + dec(z2) + '$，最後 $x_2=\\mu_2+z_2\\sigma_2=' + mm2 + '+(' + dec(z2) + ')(' + s2 + ')$。',
             p: { v: 2, m1: mm1, m2: mm2, s1: s1, s2: s2, x1: xx1, d: fr2(dd), ans: fr2(xx2) } };
  };

  /* ══ L3-9　平均成長率：n 個倍率相乘開 n 次方 ══ */
  /* 每列 [r_1,…,r_n,g]（百分比整數）：∏(1+r_i/100)=(1+g/100)^n，已用 Fraction 逐列驗過 */
  var L3GROW4 = [[80,60,-20,-10,20], [60,20,20,-10,20], [80,60,-40,20,20], [80,-20,20,20,20], [80,50,50,25,50], [80,80,25,25,50], [-40,35,-10,-10,-10], [-25,-10,-10,8,-10], [-40,35,-25,8,-10], [35,-28,-25,-10,-10], [-36,-20,-20,0,-20], [-36,-36,25,-20,-20], [-36,-36,0,0,-20], [75,40,40,12,40], [75,75,12,12,40]];
  var L3GROW5 = [[80,80,60,-40,-20,20], [80,60,-20,20,-10,20], [80,60,-40,20,20,20], [80,60,60,-40,-10,20], [80,50,50,50,25,50], [80,80,50,25,25,50], [-40,35,-25,-10,8,-10], [35,-28,-25,-10,-10,-10], [-40,35,35,-28,-25,-10], [-40,35,-10,-10,-10,-10], [-36,-20,-20,-20,0,-20], [-36,-36,-20,0,0,-20], [-36,-36,25,-20,-20,-20], [-36,-36,-36,25,0,-20], [75,40,40,40,12,40], [75,75,40,12,12,40]];
  var L3GROW6 = [[80,80,60,-40,-20,20,20], [80,60,60,-40,20,-10,20], [80,60,-20,20,20,-10,20], [80,60,35,-20,-20,20,20], [80,50,50,50,50,25,50], [80,80,50,50,25,25,50], [80,80,80,25,25,25,50], [-40,35,-25,-10,-10,8,-10], [-40,35,35,-28,-25,-10,-10], [-40,35,-10,-10,-10,-10,-10], [-40,-40,35,35,-10,-10,-10], [-36,-20,-20,-20,-20,0,-20], [-36,-36,-20,-20,0,0,-20], [-36,-36,25,-20,-20,-20,-20], [-36,-36,-36,0,0,0,-20], [75,40,40,40,40,12,40], [75,75,40,40,12,12,40], [75,75,75,12,12,12,40]];
  var L3GITEM = ['某公司的年營收', '某城市的人口數', '某商品的年銷售量', '某基金的淨值', '某地區的用電量'];
  L3.growthMean = function (r) {
    var v = r.int(0, 2), i;
    if (v === 1) {
      var y0 = r.int(2010, 2018), nn = 6, rh, prod, gm = 0, ct = 0, tries = 0;
      do {
        rh = []; prod = 1;
        for (i = 0; i < nn; i++) { var pp = r.int(50, 700); rh.push(pp); prod *= (1 + pp / 10000); }
        gm = (Math.pow(prod, 1 / nn) - 1) * 100; ct = Math.round(gm * 10); tries++;
      } while ((Math.abs(gm * 10 - ct) > 0.6 || ct < 12) && tries < 80);
      var idx = r.int(0, 4), opts = [];
      for (i = 0; i < 5; i++) opts.push(ct + 2 * (i - idx));
      var am = 0; for (i = 0; i < nn; i++) am += rh[i];
      var cn = r.pick(['某國', '某地區', '甲國']);
      return { q: cn + ' ' + T(y0 + '\\sim' + (y0 + nn - 1)) + ' 年的經濟成長率依序為 ' + T(rh.map(function (z) { return l3f2(z) + '\\%'; }).join(',\\ ')) + '。這 ' + T(String(nn)) + ' 年的平均成長率最接近下列何者？<br>'
                 + opts.map(function (z, j) { return '(' + (j + 1) + ') ' + T(l3f1(z) + '\\%'); }).join('　'),
               a: '(' + (idx + 1) + ') ' + T(l3f1(ct) + '\\%'),
               h: '$(1+\\bar r)^{' + nn + '}=\\prod(1+r_i)$，$\\bar r$ 是幾何平均。選擇題用估算：算術平均 $=\\dfrac{' + rh.map(l3f2).join('+') + '}{' + nn + '}\\approx' + (Math.round(am / nn) / 100).toFixed(2) + '\\%$；成長率都很小時幾何平均與算術平均極接近（且幾何平均永遠不超過算術平均），選最靠近的 $' + l3f1(ct) + '\\%$。',
               p: { v: 1, rates: rh, opts: opts, ans: idx + 1 } };
    }
    var nn2 = r.pick([4, 5, 6]), tab = nn2 === 4 ? L3GROW4 : (nn2 === 5 ? L3GROW5 : L3GROW6);
    var row = r.pick(tab), g = row[nn2], rates = r.shuffle(row.slice(0, nn2));
    var item = r.pick(L3GITEM), pf = F(1);
    for (i = 0; i < nn2; i++) pf = Fr.mul(pf, F(100 + rates[i], 100));
    var prodTex = rates.map(function (z) { return '(' + dec(F(100 + z, 100)) + ')'; }).join('');
    var txt = rates.map(function (z) { return T(l3pc(z)); }).join('、');
    var am2 = F(rates.reduce(function (s, z) { return s + z; }, 0), nn2);
    var hb = '成長率要用「乘」的：$(1+\\bar r)^{' + nn2 + '}=' + prodTex + '=' + dec(pf) + '$，右邊恰好是 $' + dec(F(100 + g, 100)) + '$ 的 $' + nn2 + '$ 次方 ⟹ $\\bar r=' + l3pc(g) + '$；不能把 $' + nn2 + '$ 個成長率直接平均。';
    if (v === 0) return { q: item + '連續 ' + T(String(nn2)) + ' 年的成長率依序為 ' + txt + '。求這 ' + T(String(nn2)) + ' 年的平均成長率。',
                          a: T('(1+\\bar r)^{' + nn2 + '}=' + prodTex + '=' + dec(pf) + '=(' + dec(F(100 + g, 100)) + ')^{' + nn2 + '}') + ' ⟹ ' + T('\\bar r=' + l3pc(g)),
                          h: hb, p: { v: 0, rates: rates, ans: g } };
    return { q: item + '連續 ' + T(String(nn2)) + ' 年的成長率依序為 ' + txt + '。求 (1) 這 ' + T(String(nn2)) + ' 年的平均成長率　(2) 這 ' + T(String(nn2)) + ' 個成長率的算術平均數，並比較兩者的大小。',
             a: '(1) ' + T('(1+\\bar r)^{' + nn2 + '}=' + dec(pf) + '=(' + dec(F(100 + g, 100)) + ')^{' + nn2 + '}') + ' ⟹ ' + T('\\bar r=' + l3pc(g)) + '　(2) 算術平均 ' + T('=\\dfrac{' + rates.join('+').replace(/\+-/g, '-') + '}{' + nn2 + '}=' + dec(am2) + '\\%') + '，' + (Fr.lt(F(g), am2) ? '比平均成長率<b>大</b>' : '與平均成長率<b>相等</b>') + '（算術平均 $\\ge$ 幾何平均）',
             h: hb + '第 (2) 小題只是把 $' + nn2 + '$ 個百分比相加除以 $' + nn2 + '$，它一定大於等於幾何平均（本題的平均成長率 $' + l3pc(g) + '$）。',
             p: { v: 2, rates: rates, ans: { g: g, am: fr2(am2) } } };
  };

  /* ══ L3-10　哪幾組資料的 r=0：只要 S_xy=0（點排成對稱的十字形） ══ */
  function l3zset(r) {
    var c = r.int(1, 5), a = r.int(1, 3), b = r.int(1, 3);
    var x = [c - a, c + a, c, c], y = [0, 0, b, -b], mode = r.int(0, 3), d, w, t = 0;
    if (mode === 1 || mode === 3) { do { w = r.nz(-3, 3); t++; } while ((w === b || w === -b) && t < 20); x.push(c); y.push(w); }
    if (mode === 2 || mode === 3) { do { d = r.int(1, 3); t++; } while (d === a && t < 20); if (d !== a) { x.push(c - d); y.push(0); x.push(c + d); y.push(0); } }
    return { x: x, y: y };
  }
  function l3zbreak(r, s) {
    var i, j, x, y;
    for (i = 0; i < 16; i++) {
      x = s.x.slice(); y = s.y.slice(); j = r.int(0, x.length - 1);
      if (r() < 0.5) y[j] += r.nz(-2, 2); else x[j] += r.nz(-2, 2);
      if (l3nSxy(x, y) !== 0 && l3nSxx(x) > 0 && l3nSxx(y) > 0) return { x: x, y: y };
    }
    return null;
  }
  L3.zeroCorr = function (r) {
    var sets = [], flags = [], seen = {}, guard = 0, nz = 0, s, b, key;
    var want = r.int(2, 3), v = r.int(0, 2);
    while (sets.length < 5 && guard < 300) {
      guard++;
      s = l3zset(r);
      var zero = (sets.length < want);
      if (!zero) { b = l3zbreak(r, s); if (!b) continue; s = b; }
      if (l3nSxx(s.x) <= 0 || l3nSxx(s.y) <= 0) continue;
      if ((l3nSxy(s.x, s.y) === 0) !== zero) continue;
      key = pairsTex(s.x, s.y);
      if (seen[key]) continue;
      seen[key] = 1; sets.push(s); flags.push(zero ? 1 : 0);
    }
    while (sets.length < 5) { sets.push({ x: [0, 2, 1, 1], y: [0, 0, 1, -1] }); flags.push(1); }
    var pm = r.shuffle(l3rng(0, 4)), X = [], FL = [], i;
    for (i = 0; i < 5; i++) { X.push(sets[pm[i]]); FL.push(flags[pm[i]]); }
    var lines = [];
    for (i = 0; i < 5; i++) lines.push('(' + (i + 1) + ') ' + T(pairsTex(X[i].x, X[i].y)));
    var body = lines.slice(0, 2).join('　') + '<br>' + lines.slice(2, 4).join('　') + '<br>' + lines[4];
    var zs = [], ns = [];
    for (i = 0; i < 5; i++) (FL[i] ? zs : ns).push('(' + (i + 1) + ')');
    var g0 = X[0], mx0 = F(g0.x.reduce(function (p, q) { return p + q; }, 0), g0.x.length);
    var hb = '$r=0\\iff S_{xy}=\\sum(x_i-\\mu_x)(y_i-\\mu_y)=0$。逐組先算 $\\mu_x$、$\\mu_y$，再把兩排偏差相乘加總；以第 $1$ 組為例：$' + g0.x.length + '$ 筆、$\\mu_x=' + dec(mx0) + '$，'
      + '$' + g0.x.length + 'S_{xy}=' + g0.x.length + '\\sum x_iy_i-(\\sum x_i)(\\sum y_i)=' + l3nSxy(g0.x, g0.y) + '$。點若對某條鉛直線左右對稱、而偏離該線的點 $y$ 值都相同（或相消），正負就剛好抵消。';
    if (v === 1) return { q: '下列哪幾組二維資料 ' + T('(X,Y)') + ' 的相關係數<b>不為</b> ' + T('0') + '？（多選）<br>' + body,
                          a: ns.join(''), h: hb + '把 $S_{xy}\\ne0$ 的挑出來就是答案。',
                          p: { v: 1, sets: X.map(function (z) { return [z.x, z.y]; }), ans: ns.join('') } };
    if (v === 2) return { q: '下列 ' + T('5') + ' 組二維資料 ' + T('(X,Y)') + ' 中，相關係數為 ' + T('0') + ' 的共有幾組？並寫出是哪幾組。<br>' + body,
                          a: T(String(zs.length)) + ' 組：' + zs.join(''), h: hb + '$r=0$ 只表示沒有<b>直線</b>關係，不代表 $x$ 與 $y$ 無關。',
                          p: { v: 2, sets: X.map(function (z) { return [z.x, z.y]; }), ans: zs.join('') } };
    return { q: '下列哪幾組二維資料 ' + T('(X,Y)') + ' 的相關係數為 ' + T('0') + '？（多選）<br>' + body,
             a: zs.join(''), h: hb + '$r=0$ 只表示沒有<b>直線</b>關係，不代表 $x$ 與 $y$ 無關。',
             p: { v: 0, sets: X.map(function (z) { return [z.x, z.y]; }), ans: zs.join('') } };
  };

  /* ══ L3-11　四點求最適直線並預估：斜率 S_xy/S_xx、過重心 ══ */
  L3.fitFour = function (r) {
    var k = r.pick([1, 1, 2]), s = r.pick([1, 1, 2]), mc = l3xyPick(r), m = mc[0], c = mc[1];
    var mx = r.int(0, 4), my = r.int(-2, 8), v = r.int(0, 2);
    var d = l3build(L3I4, L3E4, k, s, m, c, mx, my, r.shuffle(l3rng(0, 3)));
    var off = r.pick([F(-3), F(-2), F(2), F(3), F(4), F(-3, 2), F(5, 2), F(-5, 2), F(7, 2)]);
    var x0 = Fr.add(F(mx), off), yh = Fr.add(F(my), Fr.mul(d.slope, off));
    var dx = l3devs(d.x, mx), dy = l3devs(d.y, my);
    var hb = '四點的 $\\mu_x=' + mx + '$、$\\mu_y=' + my + '$；$x$ 偏差 $' + listTex(dx) + '$、$y$ 偏差 $' + listTex(dy) + '$ ⟹ $S_{xx}=' + d.sxx + '$、$S_{yy}=' + d.syy + '$、$S_{xy}=' + d.sxy + '$。斜率 $=\\dfrac{S_{xy}}{S_{xx}}=\\dfrac{' + d.sxy + '}{' + d.sxx + '}=' + dec(d.slope) + '$，再用「必過重心 $(' + mx + ',' + my + ')$」寫出 $y-' + my + '=' + dec(d.slope) + '(x-' + mx + ')$。';
    if (v === 1) return { q: '設二維數據 ' + T(pairsTex(d.x, d.y)) + '。(1) 求相關係數 ' + T('r') + '。　(2) 求 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線。',
                          a: '(1) ' + T('r=\\dfrac{' + d.sxy + '}{\\sqrt{' + d.sxx + '\\times' + d.syy + '}}=' + dec(d.r)) + '　(2) ' + T(l3line(d.slope, d.icpt, 'x', 'y')),
                          h: hb + '相關係數 $r=\\dfrac{S_{xy}}{\\sqrt{S_{xx}S_{yy}}}$，分母 $\\sqrt{' + d.sxx + '\\times' + d.syy + '}=' + Math.sqrt(d.sxx * d.syy) + '$ 開得出來。',
                          p: { v: 1, x: d.x, y: d.y, ans: { r: fr2(d.r), a: fr2(d.slope), b: fr2(d.icpt) } } };
    if (v === 2) {
      var s2 = F(d.sxy, d.syy), i2 = Fr.sub(F(mx), Fr.mul(s2, F(my)));
      return { q: '設二維數據 ' + T(pairsTex(d.x, d.y)) + '。(1) 求 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線。　(2) 求 ' + T('x') + ' 對 ' + T('y') + ' 的最適直線。',
               a: '(1) ' + T(l3line(d.slope, d.icpt, 'x', 'y')) + '　(2) ' + T(l3line(s2, i2, 'y', 'x')),
               h: hb + '第 (2) 小題把角色對調：斜率 $=\\dfrac{S_{xy}}{S_{yy}}=\\dfrac{' + d.sxy + '}{' + d.syy + '}=' + dec(s2) + '$，同樣過重心 $(' + mx + ',' + my + ')$，寫成 $x-' + mx + '=' + dec(s2) + '(y-' + my + ')$——兩條直線並不相同。',
               p: { v: 2, x: d.x, y: d.y, ans: { a: fr2(d.slope), b: fr2(d.icpt), a2: fr2(s2), b2: fr2(i2) } } };
    }
    return { q: '設二維數據 ' + T(pairsTex(d.x, d.y)) + '。(1) 求 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線。　(2) 利用 (1)，當 ' + T('x=' + dec(x0)) + ' 時預估 ' + T('y') + ' 的值。',
             a: '(1) ' + T(l3line(d.slope, d.icpt, 'x', 'y')) + '　(2) ' + T('\\hat y=' + my + '+(' + dec(d.slope) + ')(' + dec(x0) + '-' + mx + ')=' + dec(yh)),
             h: hb + '預估就是把 $x=' + dec(x0) + '$ 代進去，從重心出發算比較快：$\\hat y=' + my + '+(' + dec(d.slope) + ')\\times(' + dec(x0) + '-' + mx + ')$。',
             p: { v: 0, x: d.x, y: d.y, x0: fr2(x0), ans: { a: fr2(d.slope), b: fr2(d.icpt), yh: fr2(yh) } } };
  };

  /* ══ L3-12　五筆二維資料：偏差表三個和、迴歸直線與換單位的預測 ══ */
  /* [情境, x 名, x 單位, y 名, y 單位, 倍率, 換算後單位, mx 池, k 池, my 池] */
  var L3C5 = [['某冰果室以不同單價調查每日需求量', '單價', '元', '需求量', '百碗', 100, '碗', [65, 70, 75, 80, 85], [5, 10], [14, 15, 16, 18, 20]],
              ['某飲料店統計當日最高氣溫與銷售量', '氣溫', '度', '銷售量', '打', 12, '瓶', [24, 26, 28, 30], [2, 4], [15, 18, 20, 24]],
              ['某公司統計每月廣告費與銷售額', '廣告費', '萬元', '銷售額', '十萬元', 10, '萬元', [15, 20, 25], [2, 5], [14, 16, 18, 20]],
              ['某農場統計施肥量與收成量', '施肥量', '公斤', '收成量', '百公斤', 100, '公斤', [30, 40, 50], [5, 10], [14, 16, 18]]];
  L3.fitFive = function (r) {
    var ct = r.pick(L3C5), mx = r.pick(ct[7]), k = r.pick(ct[8]), my = r.pick(ct[9]);
    var mc = l3xyPick(r), m = mc[0], c = mc[1], v = r.int(0, 2);
    var d = l3build(L3I5, L3E5, k, 1, m, c, mx, my, null);
    var q0 = r.nz(-2 * k, 2 * k), x0 = mx + q0, yh = Fr.add(F(my), Fr.mul(d.slope, F(q0)));
    var conv = Fr.mul(yh, F(ct[5]));
    var dx = l3devs(d.x, mx), dy = l3devs(d.y, my);
    var head = ct[0] + '，得到 ' + T('5') + ' 筆資料（' + ct[1] + ' ' + T('x') + ' 的單位為' + ct[2] + '、' + ct[3] + ' ' + T('y') + ' 的單位為' + ct[4] + '）：'
      + T('x:\\ ' + listTex(d.x)) + '；' + T('y:\\ ' + listTex(d.y)) + '。';
    var hb = '$\\mu_x=' + mx + '$、$\\mu_y=' + my + '$；偏差 $x:' + listTex(dx) + '$、$y:' + listTex(dy) + '$ ⟹ $S_{xx}=' + d.sxx + '$、$S_{yy}=' + d.syy + '$、$S_{xy}=' + d.sxy + '$。$r=\\dfrac{' + d.sxy + '}{\\sqrt{' + d.sxx + '\\times' + d.syy + '}}=' + dec(d.r) + '$；斜率 $=\\dfrac{S_{xy}}{S_{xx}}=' + dec(d.slope) + '$，過重心 $(' + mx + ',' + my + ')$。';
    if (v === 1) return { q: head + '(1) 求 ' + T('S_{xx}') + '、' + T('S_{yy}') + '、' + T('S_{xy}') + '。　(2) 求相關係數。　(3) 求 ' + T('y') + ' 對 ' + T('x') + ' 的迴歸直線。',
                          a: '(1) ' + T('S_{xx}=' + d.sxx) + '、' + T('S_{yy}=' + d.syy) + '、' + T('S_{xy}=' + d.sxy) + '　(2) ' + T('r=' + dec(d.r)) + '　(3) ' + T(l3line(d.slope, d.icpt, 'x', 'y')),
                          h: hb, p: { v: 1, x: d.x, y: d.y, ans: { sxx: d.sxx, syy: d.syy, sxy: d.sxy, r: fr2(d.r), a: fr2(d.slope), b: fr2(d.icpt) } } };
    if (v === 2) return { q: head + '(1) 求相關係數。　(2) 求 ' + T('y') + ' 對 ' + T('x') + ' 的迴歸直線。　(3) 若' + ct[1] + '訂為 ' + T(String(x0)) + ' ' + ct[2] + '，用迴歸直線預測' + ct[3] + '（單位：' + ct[4] + '）。',
                          a: '(1) ' + T('r=' + dec(d.r)) + '　(2) ' + T(l3line(d.slope, d.icpt, 'x', 'y')) + '　(3) ' + T('\\hat y=' + my + '+(' + dec(d.slope) + ')(' + x0 + '-' + mx + ')=' + dec(yh)) + ' ' + ct[4],
                          h: hb + '預測直接從重心出發：$\\hat y=' + my + '+(' + dec(d.slope) + ')\\times(' + x0 + '-' + mx + ')$。',
                          p: { v: 2, x: d.x, y: d.y, x0: x0, ans: { r: fr2(d.r), a: fr2(d.slope), b: fr2(d.icpt), yh: fr2(yh) } } };
    return { q: head + '(1) 求相關係數。　(2) 求 ' + T('y') + ' 對 ' + T('x') + ' 的迴歸直線。　(3) 若' + ct[1] + '訂為 ' + T(String(x0)) + ' ' + ct[2] + '，用迴歸直線預測' + ct[3] + '是多少' + ct[6] + '。',
             a: '(1) ' + T('r=' + dec(d.r)) + '　(2) ' + T(l3line(d.slope, d.icpt, 'x', 'y')) + '　(3) ' + T('\\hat y=' + dec(yh)) + ' ' + ct[4] + ' ' + T('=' + dec(conv)) + ' ' + ct[6],
             h: hb + '第 (3) 小題代 $x=' + x0 + '$ 得 $\\hat y=' + dec(yh) + '$ ' + ct[4] + '，最後要記得換回' + ct[6] + '（乘 $' + ct[5] + '$）。',
             p: { v: 0, x: d.x, y: d.y, x0: x0, mul: ct[5], ans: { r: fr2(d.r), a: fr2(d.slope), b: fr2(d.icpt), yh: fr2(yh), cv: fr2(conv) } } };
  };

  /* ══ L3-13　六筆資料：先寫偏差表，S_xx、S_yy 是設計好的漂亮數字 ══ */
  var L3C6 = [['複習數學的時數', '小時', '數學成績', '分'], ['每週練習的時數', '小時', '測驗得分', '分'],
              ['每日閱讀的時數', '小時', '國文成績', '分'], ['每週上機練習的時數', '小時', '程式檢定成績', '分']];
  L3.fitSix = function (r) {
    var ct = r.pick(L3C6), mx = r.int(4, 8), s = r.pick([1, 2]), mc = l3xyPick(r), m = mc[0], c = mc[1];
    var my = r.int(66, 76), v = r.int(0, 2);
    var d = l3build(L3I6, L3E6, 1, s, m, c, mx, my, r.shuffle(l3rng(0, 5)));
    var dx = l3devs(d.x, mx), dy = l3devs(d.y, my);
    var qs = [], i;
    for (i = -4; i <= 4; i++) { var yy = my + m * s * i; if (i !== 0 && mx + i >= 1 && yy >= 20 && yy <= 100) qs.push(i); }
    var q0 = qs.length ? r.pick(qs) : 1, x0 = mx + q0, yh = Fr.add(F(my), Fr.mul(d.slope, F(q0)));
    var head = '六位學生' + ct[0] + ' ' + T('x') + '（' + ct[1] + '）與' + ct[2] + ' ' + T('y') + '（' + ct[3] + '）如下：' + T('x:\\ ' + listTex(d.x)) + '；' + T('y:\\ ' + listTex(d.y)) + '。';
    var hb = '先寫偏差表：$\\mu_x=' + mx + '$、$\\mu_y=' + my + '$，$x$ 偏差 $' + listTex(dx) + '$、$y$ 偏差 $' + listTex(dy) + '$ ⟹ $S_{xx}=' + d.sxx + '$、$S_{yy}=' + d.syy + '$、$S_{xy}=' + d.sxy + '$，$\\sqrt{S_{xx}S_{yy}}=' + Math.sqrt(d.sxx * d.syy) + '$ 恰好開得出來。';
    if (v === 1) return { q: head + '(1) 求 ' + T('\\mu_x') + '、' + T('\\mu_y') + '、' + T('S_{xx}') + '、' + T('S_{yy}') + '、' + T('S_{xy}') + '。　(2) 求相關係數。　(3) 求 ' + T('y') + ' 對 ' + T('x') + ' 的迴歸直線。',
                          a: '(1) ' + T('\\mu_x=' + mx) + '、' + T('\\mu_y=' + my) + '、' + T('S_{xx}=' + d.sxx) + '、' + T('S_{yy}=' + d.syy) + '、' + T('S_{xy}=' + d.sxy) + '　(2) ' + T('r=' + dec(d.r)) + '　(3) ' + T(l3line(d.slope, d.icpt, 'x', 'y')),
                          h: hb, p: { v: 1, x: d.x, y: d.y, ans: { sxx: d.sxx, syy: d.syy, sxy: d.sxy, r: fr2(d.r), a: fr2(d.slope), b: fr2(d.icpt) } } };
    if (v === 2) return { q: head + '(1) 求相關係數。　(2) 求 ' + T('y') + ' 對 ' + T('x') + ' 的迴歸直線。　(3) 某位學生' + ct[0] + '為 ' + T(String(x0)) + ' ' + ct[1] + '，預測他的' + ct[2] + '。',
                          a: '(1) ' + T('r=' + dec(d.r)) + '　(2) ' + T(l3line(d.slope, d.icpt, 'x', 'y')) + '　(3) ' + T('\\hat y=' + my + '+(' + dec(d.slope) + ')(' + x0 + '-' + mx + ')=' + dec(yh)) + ' ' + ct[3],
                          h: hb + '$r=\\dfrac{' + d.sxy + '}{' + Math.sqrt(d.sxx * d.syy) + '}=' + dec(d.r) + '$；斜率 $=\\dfrac{' + d.sxy + '}{' + d.sxx + '}=' + dec(d.slope) + '$，過重心後再代 $x=' + x0 + '$。',
                          p: { v: 2, x: d.x, y: d.y, x0: x0, ans: { r: fr2(d.r), a: fr2(d.slope), b: fr2(d.icpt), yh: fr2(yh) } } };
    return { q: head + '(1) 求 ' + T('x') + ' 與 ' + T('y') + ' 的相關係數。　(2) 求 ' + T('\\mu_x') + '、' + T('\\mu_y') + ' 與 ' + T('y') + ' 對 ' + T('x') + ' 的迴歸直線。',
             a: '(1) ' + T('r=\\dfrac{' + d.sxy + '}{' + Math.sqrt(d.sxx * d.syy) + '}=' + dec(d.r)) + '　(2) ' + T('\\mu_x=' + mx) + '、' + T('\\mu_y=' + my) + '、' + T(l3line(d.slope, d.icpt, 'x', 'y')),
             h: hb + '$r=\\dfrac{S_{xy}}{\\sqrt{S_{xx}S_{yy}}}$；斜率 $=\\dfrac{S_{xy}}{S_{xx}}=' + dec(d.slope) + '$，直線必過 $(' + mx + ',' + my + ')$。',
             p: { v: 0, x: d.x, y: d.y, ans: { r: fr2(d.r), a: fr2(d.slope), b: fr2(d.icpt) } } };
  };

  /* ══ L3-14　線性變換後 r 的正負：只看係數乘積的符號 ══ */
  var L3RHO = [F(83, 100), F(76, 100), F(64, 100), F(45, 100), F(92, 100), F(58, 100), F(3, 5), F(4, 5),
               F(7, 10), F(9, 10), F(37, 50), F(21, 25), F(2, 5), F(1, 2), F(53, 100), F(87, 100)];
  L3.corrSigns = function (r) {
    var A = [2, 3, 4, 5, -2, -3, -4, -5], a = r.pick(A), c = r.pick([2, 3, 4, 6, -2, -3, -4, -6]), e = r.pick([2, 3, 5, 7, -2, -3, -5, -7]);
    var b = r.nz(-9, 9), dd = r.nz(-9, 9), f = r.nz(-9, 9), rho = r.pick(L3RHO), v = r.int(0, 2);
    if (a > 0 && c > 0 && e > 0) c = -c;
    var sgn = function (t) { return t > 0 ? 1 : -1; };
    var rxy = sgn(a * c) > 0 ? rho : F(-rho.n, rho.d);
    var ruw = sgn(c * e) > 0 ? rho : F(-rho.n, rho.d);
    var rwy = F(sgn(e)), rvw = F(sgn(c * e)), rxw = sgn(a * c * e) > 0 ? rho : F(-rho.n, rho.d);
    var head = '有五組資料 ' + T('x,y,u,v,w') + '，且 ' + T('r(u,v)=' + dec(rho)) + '，其中 ' + T('u=' + l3lin(a, b, 'x')) + '、' + T('v=' + l3lin(c, dd, 'y')) + '、' + T('w=' + l3lin(e, f, 'y')) + '。';
    var hb = '$r(ax+b,\\ cy+d)$ 只看 $ac$ 的正負：同號不變、異號變號，平移量完全沒影響。本題 $r(u,v)=r(' + l3lin(a, b, 'x') + ',\\ ' + l3lin(c, dd, 'y') + ')$，係數乘積 $' + a + '\\times' + l3par(c) + '=' + (a * c) + '$ ⟹ $r(x,y)=' + dec(rxy) + '$。';
    if (v === 1) return { q: head + '求 ' + T('r(x,y)') + ' 與 ' + T('r(u,w)') + '。',
                          a: T('r(x,y)=' + dec(rxy)) + '、' + T('r(u,w)=' + dec(ruw)),
                          h: hb + '再看 $r(u,w)$：係數乘積 $' + a + '\\times' + l3par(e) + '=' + (a * e) + '$，所以 $r(u,w)=' + (a * e > 0 ? '' : '-') + 'r(x,y)=' + dec(ruw) + '$。',
                          p: { v: 1, a: a, b: b, c: c, d: dd, e: e, f: f, rho: fr2(rho), ans: [fr2(rxy), fr2(ruw)] } };
    if (v === 2) return { q: head + '求 ' + T('r(x,w)+r(v,w)') + '。',
                          a: T('r(x,w)=' + dec(rxw)) + '、' + T('r(v,w)=' + dec(rvw)) + ' ⟹ ' + T('r(x,w)+r(v,w)=' + dec(Fr.add(rxw, rvw))),
                          h: hb + '$r(x,w)=r(x,' + l3lin(e, f, 'y') + ')$，係數 $' + e + (e > 0 ? '\\gt' : '\\lt') + '0$ ⟹ $r(x,w)=' + (e > 0 ? '' : '-') + 'r(x,y)=' + dec(rxw) + '$；$v$ 與 $w$ 都是 $y$ 的一次式，完全線性 ⟹ $r(v,w)=' + dec(rvw) + '$（係數 $' + c + '\\times' + l3par(e) + '=' + (c * e) + '$）。',
                          p: { v: 2, a: a, b: b, c: c, d: dd, e: e, f: f, rho: fr2(rho), ans: fr2(Fr.add(rxw, rvw)) } };
    return { q: head + '求 ' + T('r(u,w)+r(w,y)') + '。',
             a: T('r(u,w)=' + dec(ruw)) + '、' + T('r(w,y)=' + dec(rwy)) + ' ⟹ ' + T('r(u,w)+r(w,y)=' + dec(Fr.add(ruw, rwy))),
             h: hb + '$r(u,w)$：係數乘積 $' + a + '\\times' + l3par(e) + '=' + (a * e) + '$ ⟹ $r(u,w)=' + dec(ruw) + '$；$w=' + l3lin(e, f, 'y') + '$ 與 $y$ 完全線性且係數 $' + e + (e > 0 ? '\\gt' : '\\lt') + '0$ ⟹ $r(w,y)=' + dec(rwy) + '$。',
             p: { v: 0, a: a, b: b, c: c, d: dd, e: e, f: f, rho: fr2(rho), ans: fr2(Fr.add(ruw, rwy)) } };
  };

  /* ══ L3-15　由 σ 與最適直線反解 r：直線過重心 ＋ 斜率 = r·σ_y/σ_x ══ */
  L3.lineToCorr = function (r) {
    var RR = [F(3, 4), F(3, 5), F(4, 5), F(1, 2), F(2, 5), F(7, 10), F(9, 10), F(-3, 5), F(-4, 5), F(-1, 2), F(-3, 4)];
    var rr, sx, sy, slope, tries = 0;
    do { rr = r.pick(RR); sx = r.pick([4, 5, 8, 10, 20]); sy = r.pick([4, 5, 6, 8, 10, 12, 15]); slope = Fr.mul(rr, F(sy, sx)); tries++; }
    while (slope.d > 20 && tries < 40);
    if (slope.d > 20) { rr = F(3, 4); sx = 10; sy = 8; slope = F(3, 5); }
    var dd = slope.d, lo = Math.ceil(45 / dd), hi = Math.floor(78 / dd);
    if (hi < lo) hi = lo;
    var mx = dd * r.int(lo, hi);
    var my = r.int(Math.max(35, 2 * sy + 2), Math.min(92, 100 - 2 * sy));
    if (my < 2 * sy + 2) my = 2 * sy + 2;
    var b = Fr.sub(F(my), Fr.mul(slope, F(mx)));
    var v = r.int(0, 2), sub = r.shuffle(SUBJ).slice(0, 2);
    var ln = l3line(slope, b, 'x', 'y');
    var hb = '兩個性質各用一次：① 最適直線必過重心 $(\\mu_x,\\mu_y)$，代 $x=' + mx + '$ 得 $\\mu_y=' + dec(slope) + '(' + mx + ')' + (b.n >= 0 ? '+' : '') + dec(b) + '=' + my + '$；② 斜率 $=r\\cdot\\dfrac{\\sigma_y}{\\sigma_x}$，把 $' + dec(slope) + '=r\\cdot\\dfrac{' + sy + '}{' + sx + '}$ 反解 $r=' + dec(rr) + '$（順便檢查 $|r|\\le1$）。';
    if (v === 1) {
      var n = r.pick([20, 25, 30, 40, 50]), Sxx = n * sx * sx, Syy = n * sy * sy;
      return { q: '某班 ' + T(String(n)) + ' 位學生的' + sub[0] + '成績 ' + T('X') + ' 與' + sub[1] + '成績 ' + T('Y') + ' 滿足 ' + T('\\sum(x_i-\\mu_x)^2=' + Sxx) + '、' + T('\\sum(y_i-\\mu_y)^2=' + Syy) + '，' + sub[0] + '平均 ' + T(String(mx)) + ' 分。已知 ' + T('Y') + ' 對 ' + T('X') + ' 的最適直線為 ' + T(ln) + '。求' + sub[1] + '的平均數與兩科的相關係數 ' + T('r') + '。',
               a: T('\\sigma_x=\\sqrt{\\dfrac{' + Sxx + '}{' + n + '}}=' + sx) + '、' + T('\\sigma_y=\\sqrt{\\dfrac{' + Syy + '}{' + n + '}}=' + sy) + '；' + T('\\mu_y=' + my) + '、' + T('r=' + dec(rr)),
               h: '先由 $\\sigma^2=\\dfrac{\\sum(x_i-\\mu)^2}{n}$ 得 $\\sigma_x=\\sqrt{\\dfrac{' + Sxx + '}{' + n + '}}=' + sx + '$、$\\sigma_y=' + sy + '$。' + hb,
               p: { v: 1, n: n, Sxx: Sxx, Syy: Syy, mx: mx, a: fr2(slope), b: fr2(b), ans: { my: my, r: fr2(rr) } } };
    }
    if (v === 2) {
      var off = slope.d * r.nz(-3, 3), x0 = mx + off, yh = Fr.add(F(my), Fr.mul(slope, F(off)));
      return { q: '某班' + sub[0] + '成績 ' + T('X') + ' 的標準差為 ' + T(String(sx)) + ' 分、' + sub[1] + '成績 ' + T('Y') + ' 的標準差為 ' + T(String(sy)) + ' 分，' + sub[0] + '平均 ' + T(String(mx)) + ' 分。' + T('Y') + ' 對 ' + T('X') + ' 的最適直線為 ' + T(ln) + '。(1) 求' + sub[1] + '的平均數 ' + T('a') + ' 與兩科的相關係數 ' + T('r') + '。　(2) 某生' + sub[0] + '考 ' + T(String(x0)) + ' 分，預測他的' + sub[1] + '成績。',
               a: '(1) ' + T('a=' + my) + '、' + T('r=' + dec(rr)) + '　(2) ' + T('\\hat y=' + my + '+(' + dec(slope) + ')(' + x0 + '-' + mx + ')=' + dec(yh)) + ' 分',
               h: hb + '第 (2) 小題直接把 $x=' + x0 + '$ 代進最適直線（從重心出發：$' + my + '+' + dec(slope) + '\\times(' + x0 + '-' + mx + ')$）。',
               p: { v: 2, sx: sx, sy: sy, mx: mx, x0: x0, a: fr2(slope), b: fr2(b), ans: { my: my, r: fr2(rr), yh: fr2(yh) } } };
    }
    var s2 = Fr.mul(rr, F(sx, sy)), i2 = Fr.sub(F(mx), Fr.mul(s2, F(my)));
    return { q: '某班' + sub[0] + '成績 ' + T('X') + ' 的標準差為 ' + T(String(sx)) + ' 分、' + sub[1] + '成績 ' + T('Y') + ' 的標準差為 ' + T(String(sy)) + ' 分，' + sub[0] + '平均 ' + T(String(mx)) + ' 分。' + T('Y') + ' 對 ' + T('X') + ' 的最適直線為 ' + T(ln) + '。設' + sub[1] + '平均為 ' + T('a') + '、兩科相關係數為 ' + T('r') + '。(1) 求 ' + T('a') + ' 與 ' + T('r') + '。　(2) 求 ' + T('X') + ' 對 ' + T('Y') + ' 的最適直線。',
             a: '(1) ' + T('a=' + my) + '、' + T('r=' + dec(rr)) + '　(2) ' + T(l3line(s2, i2, 'y', 'x')),
             h: hb + '第 (2) 小題換方向：斜率 $=r\\cdot\\dfrac{\\sigma_x}{\\sigma_y}=' + dec(rr) + '\\times\\dfrac{' + sx + '}{' + sy + '}=' + dec(s2) + '$，一樣過重心 $(' + mx + ',' + my + ')$。',
             p: { v: 0, sx: sx, sy: sy, mx: mx, a: fr2(slope), b: fr2(b), ans: { my: my, r: fr2(rr), a2: fr2(s2), b2: fr2(i2) } } };
  };

  var META_L3 = [['pctTop', '由大到小找百分位數（已知門檻以上幾位）'], ['pctSort', '亂序資料排到第 t 筆的百分位數'], ['pctLevels', '五級評分次數分配表的百分位數'],
                 ['sdSums', '由 Σx 與 Σx² 求標準差'], ['sqMean', '平方的平均＝σ²+μ²'], ['addAtMean', '新增一筆恰等於平均'],
                 ['mergeSolveSd', '合併變異數反求一組的 σ'], ['zGap', '標準化分數差求原始分數'], ['growthMean', '平均成長率：倍率相乘開 n 次方'],
                 ['zeroCorr', '哪幾組資料的 r＝0'], ['fitFour', '四點的最適直線與預估'], ['fitFive', '五筆資料的 r、迴歸直線與換單位預測'],
                 ['fitSix', '六筆資料的偏差表與迴歸直線'], ['corrSigns', '線性變換後 r 的正負'], ['lineToCorr', '由 σ 與最適直線反解 r']];
  /* 固定題 L3-n 對應的類似題型 */
  var L3_FIX = { 'L3-1': 'pctTop', 'L3-2': 'pctSort', 'L3-3': 'pctLevels', 'L3-4': 'sdSums', 'L3-5': 'sqMean',
                 'L3-6': 'addAtMean', 'L3-7': 'mergeSolveSd', 'L3-8': 'zGap', 'L3-9': 'growthMean', 'L3-10': 'zeroCorr',
                 'L3-11': 'fitFour', 'L3-12': 'fitFive', 'L3-13': 'fitSix', 'L3-14': 'corrSigns', 'L3-15': 'lineToCorr' };

  /* ══════════════════════════════════════════════════════════
     L0　章首先備診斷（5 型）：平均數與中位數（國中）、根式化簡（高一上 ch1）、兩點的斜率與點斜式（高一上 ch2）、配方求最小值（高一上 ch3）、Σ 記號求和（高一下 ch1）
     ══════════════════════════════════════════════════════════ */
  var L0 = {};
  function l0sg(x) { return x < 0 ? '-' + (-x) : '+' + x; }                 /* 帶正負號的常數項 */
  function l0sn(x) { return x < 0 ? '(' + x + ')' : String(x); }
  L0.meanMedian = function (r) {
    var n = r.pick([5, 6, 7, 8]), a = [], i; for (i = 0; i < n; i++) a.push(r.int(2, 20));
    var s = a.slice().sort(function (u, v) { return u - v; }), mean = F(sumArr(a), n), med = n % 2 ? F(s[(n - 1) / 2]) : F(s[n / 2 - 1] + s[n / 2], 2);
    return { q: '求資料 ' + T(listTex(a)) + ' 的算術平均數與中位數。', a: '平均數 ' + T(Fr.tex(mean)) + '、中位數 ' + T(Fr.tex(med)),
      h: '平均數：總和 $' + sumArr(a) + '$ 除以 $' + n + '$。中位數要<b>先由小到大排</b>：$' + listTex(s) + '$，' + (n % 2 ? '共 $' + n + '$ 筆（奇數），取正中間第 $' + ((n + 1) / 2) + '$ 筆。' : '共 $' + n + '$ 筆（偶數），取第 $' + (n / 2) + '$、$' + (n / 2 + 1) + '$ 筆的平均。') + '本章的百分位數也是「先排序、再數位置」。',
      p: { a: a, ans: { mean: fr2(mean), med: fr2(med) } } };
  };
  L0.sqrtSimp = function (r) {
    var v = r.int(0, 1), k = r.pick([2, 3, 5, 6, 7, 10, 11, 13, 14]), m = r.pick([2, 3, 4, 5, 6]), N = k * m * m;
    if (v === 0) return { q: '化簡 ' + T('\\sqrt{' + N + '}') + '。', a: T(sqrtTex(N)),
      h: '把 $' + N + '$ 拆成「完全平方數 $\\times$ 剩下的」：$' + N + '=' + (m * m) + '\\times' + k + '$，所以 $\\sqrt{' + N + '}=' + m + '\\sqrt{' + k + '}$。本章的標準差幾乎每題都要化簡根號。',
      p: { v: v, N: N, ans: [m, k] } };
    var d = r.pick([2, 3, 5, 6, 7, 10]), n = r.pick([4, 9, 16, 25]) , val = F(1);
    return { q: '化簡 ' + T('\\sqrt{\\dfrac{' + d + '}{' + n + '}}') + '。', a: T('\\dfrac{\\sqrt{' + d + '}}{' + Math.round(Math.sqrt(n)) + '}'),
      h: '分子分母分開開根號：$\\dfrac{\\sqrt{' + d + '}}{\\sqrt{' + n + '}}=\\dfrac{\\sqrt{' + d + '}}{' + Math.round(Math.sqrt(n)) + '}$。本章「變異數是分數、標準差要開根號」時就是這個動作。',
      p: { v: v, d: d, n: n, ans: [d, Math.round(Math.sqrt(n))] } };
  };
  L0.lineSlope = function (r) {
    var x1 = r.int(-4, 4), y1 = r.int(-5, 8), dx = r.pick([1, 2, 3, 4, 5]), dy; do { dy = r.int(-6, 6); } while (dy === 0);
    var x2 = x1 + dx, y2 = y1 + dy, m = F(dy, dx), b = Fr.sub(F(y1), Fr.mul(m, F(x1)));
    var mT = Fr.tex(m), eq = 'y=' + (m.n === m.d ? '' : (m.n === -m.d ? '-' : mT)) + 'x' + (b.n === 0 ? '' : (b.n < 0 ? '-' + Fr.tex(F(-b.n, b.d)) : '+' + Fr.tex(b)));
    return { q: '求通過 ' + T('A(' + x1 + ',' + y1 + ')') + '、' + T('B(' + x2 + ',' + y2 + ')') + ' 兩點的直線斜率，並把直線寫成 ' + T('y=mx+k') + ' 的形式。', a: '斜率 ' + T(mT) + '，' + T(eq),
      h: '斜率 $=\\dfrac{' + y2 + '-' + l0sn(y1) + '}{' + x2 + '-' + l0sn(x1) + '}=' + mT + '$；再用點斜式 $y' + (y1 === 0 ? '' : '-' + l0sn(y1)) + '=' + mT + (x1 === 0 ? 'x' : '(x-' + l0sn(x1) + ')') + '$ 整理。本章的最適直線就是「斜率＋通過重心」的點斜式。',
      p: { A: [x1, y1], B: [x2, y2], ans: { m: fr2(m), k: fr2(b) } } };
  };
  L0.quadMin = function (r) {
    var a = r.pick([1, 2, 3, 4, 5]), h = r.int(-5, 6), k = r.int(1, 30), bq = -2 * a * h, cq = a * h * h + k; if (h === 0) { h = 2; bq = -4 * a; cq = 4 * a + k; }
    var poly = (a === 1 ? '' : a) + 't^2' + l0sg(bq) + 't' + l0sg(cq);
    return { q: '設 ' + T('t') + ' 為實數，求 ' + T(poly) + ' 的最小值，以及此時的 ' + T('t') + '。', a: T('t=' + h) + ' 時，最小值 ' + T(String(k)),
      h: '配方：' + (a === 1 ? '' : '先把 $' + a + '$ 提出來，') + '一次項係數的一半是 $' + (-h) + '$，湊成 $' + (a === 1 ? '' : a) + '(t' + l0sg(-h) + ')^2+' + k + '$。本章「離差平方和在 $t=\\mu$ 時最小」「最適直線讓誤差平方和最小」都是這個配方。',
      p: { a: a, b: bq, c: cq, ans: [h, k] } };
  };
  L0.sigmaSum = function (r) {
    var v = r.int(0, 1), n = r.int(4, 8), a = r.int(1, 4), b = r.int(-3, 5);
    if (v === 0) {
      var s = 0, terms = []; for (var k = 1; k <= n; k++) { s += a * k + b; terms.push(a * k + b); }
      var body = (a === 1 ? '' : a) + 'k' + (b === 0 ? '' : l0sg(b));
      return { q: '求 ' + T('\\displaystyle\\sum_{k=1}^{' + n + '}' + (b === 0 ? body : '(' + body + ')')) + ' 的值。', a: T(String(s)),
        h: '把 $k=1,2,\\dots,' + n + '$ 逐一代入再相加：$' + terms.map(l0sn).join('+') + '=' + s + '$；也可以拆成 $' + (a === 1 ? '' : a) + '\\sum k' + (b === 0 ? '' : l0sg(b * n)) + '$' + (b === 0 ? '' : '（常數 $' + b + '$ 加了 $' + n + '$ 次）') + '。本章 $\\sum x_i$、$\\sum x_i^2$、$\\sum x_iy_i$ 都是這種「一項一項加」。',
        p: { v: v, n: n, a: a, b: b, ans: s } };
    }
    var xs = [], i; for (i = 0; i < 5; i++) xs.push(r.int(1, 9)); var s1 = sumArr(xs), s2 = 0; xs.forEach(function (x) { s2 += x * x; });
    return { q: '設五筆資料 ' + T('x_1,\\dots,x_5') + ' 為 ' + T(listTex(xs)) + '，求 ' + T('\\displaystyle\\sum_{i=1}^{5}x_i') + ' 與 ' + T('\\displaystyle\\sum_{i=1}^{5}x_i^2') + '。', a: T('\\sum x_i=' + s1) + '、' + T('\\sum x_i^2=' + s2),
      h: '$\\sum x_i$ 是五個數直接相加；$\\sum x_i^2$ 是<b>先平方再相加</b>：$' + xs.map(function (x) { return x * x; }).join('+') + '=' + s2 + '$，它不等於 $(\\sum x_i)^2=' + s1 * s1 + '$。本章變異數公式 $\\dfrac{\\sum x_i^2}{n}-\\mu^2$ 靠它。',
      p: { v: v, xs: xs, ans: [s1, s2] } };
  };
  var META_L0 = [['meanMedian', '平均數與中位數'], ['sqrtSimp', '根式化簡'], ['lineSlope', '兩點的斜率與直線方程式'], ['quadMin', '配方求最小值'], ['sigmaSum', 'Σ 記號求和']];
  /* 先備題型 → 該去哪裡複習 */
  var PREREQ = {
    meanMedian: { txt: '算術平均數與中位數（國中）——本章的集中趨勢、百分位數都從「排序、數位置」開始', link: null },
    sqrtSimp: { txt: '根式化簡（高一上第一章 數與式）——標準差幾乎每題都要化簡根號', link: '../g10a-ch01/practice.html#L1' },
    lineSlope: { txt: '兩點的斜率與點斜式（高一上第二章 直線與圓）——最適直線＝斜率＋通過重心', link: '../g10a-ch02/practice.html#L1' },
    quadMin: { txt: '配方求最小值（高一上第三章 多項式）——離差平方和、最小平方法都是配方', link: '../g10a-ch03/practice.html#L1' },
    sigmaSum: { txt: 'Σ 記號與逐項求和（高一下第一章 數列與級數）——Σx、Σx²、Σxy 是本章所有公式的原料', link: '../g10b-ch01/practice.html#L1' }
  };
  /* ══════════════════════════════════════════════════════════
     對照題：同一型抽兩題，只差一個關鍵特徵（f 由 p 算出；keep 的欄位要相同）
     ══════════════════════════════════════════════════════════ */
  function sign3(x) { return x > 0 ? 1 : x < 0 ? -1 : 0; }
  var CONTRAST = {
    'L1.pctPosition': { f: function (p) { return p.ans.t[1] === 1; }, why: '百分位數先算 $t=\\dfrac{nk}{100}$：$t$ 是整數時取第 $t$ 筆與第 $t+1$ 筆的平均；$t$ 不是整數時無條件進位、取那一筆。兩題的差別只在 $t$ 是不是整數——這是百分位數唯一會錯的地方。' },
    'L1.meanShift': { f: function (p) { return p.kind; }, why: '加入一筆資料：新總和 $=$ 舊總和 $+$ 新資料，除以 $n+1$；剔除兩個分數：總和減掉它們，除以 $n-2$。不管加或剔除，都是「回到總和」再重新平均，不能直接對平均數加減。' },
    'L1.addOne': { f: function (p) { return p.v === p.mu; }, why: '新加的資料恰好等於平均時，平均不變、離差平方和也不變，只有分母多 $1$，變異數變小；不等於平均時，平均會被拉動，要用 $\\sum x^2=n(\\sigma^2+\\mu^2)$ 回到平方和重算。' },
    'L1.linearTrans': { f: function (p) { return p.a[0] < 0; }, why: '$y=ax+b$：平均數 $\\mu_y=a\\mu_x+b$（$a$ 的正負照乘）；標準差 $\\sigma_y=|a|\\sigma_x$——標準差永遠非負，$a$ 是負的也要取絕對值，加的常數 $b$ 完全不影響分散程度。' },
    'L1.zCompare': { f: function (p) { return p.ans.better; }, why: '跨科比較不看原始分數、要看標準化分數 $z=\\dfrac{x-\\mu}{\\sigma}$：同樣高出平均 $10$ 分，在 $\\sigma$ 小的那一科代表贏過更多人。哪一科的 $z$ 大，哪一科就相對比較好。' },
    'L1.zInverse': { f: function (p) { return p.kind; }, why: '標準化是 $z=\\dfrac{x-\\mu}{\\sigma}$，反過來就是 $x=\\mu+z\\sigma$：一題由 $z$ 求原始分數、一題由原始分數求 $z$，用的是同一條式子的兩個方向。' },
    'L1.tScore': { f: function (p) { return p.kind; }, why: '$T$ 分數是把 $z$ 再做一次線性變換（$T=50+10z$ 之類）：由原始分數求 $T$ 是「先標準化、再變換」，由 $T$ 反求原始分數是「先還原成 $z$、再乘回 $\\sigma$ 加 $\\mu$」。' },
    'L1.corrData': { f: function (p) { return sign3(p.ans[0]); }, why: '相關係數的正負只看 $\\sum(x-\\mu_x)(y-\\mu_y)$ 的正負：一個大另一個也大（偏差同號居多）⟹ 正相關，一個大另一個小 ⟹ 負相關；分母永遠是正的。' },
    'L1.corrPerfect': { f: function (p) { return p.ans.r; }, why: '資料完全落在直線 $y=ax+b$ 上時 $r=\\pm1$：$a\\gt0$ 是 $+1$、$a\\lt0$ 是 $-1$，與斜率的大小無關——相關係數量的是「多像一條直線」，不是「多陡」。' },
    'L1.fitData': { f: function (p) { return sign3(p.ans.a[0]); }, why: '最適直線的斜率 $=\\dfrac{S_{xy}}{S_{xx}}$，正負與相關係數相同；直線一定通過重心 $(\\mu_x,\\mu_y)$，所以斜率定了之後截距就由重心決定。' },
    'L1.fitStats': { f: function (p) { return sign3(p.r[0]); }, why: '只給統計量時斜率 $=r\\cdot\\dfrac{\\sigma_y}{\\sigma_x}$：$r$ 為負時斜率是負的，$x$ 比平均每多 $1$，預測的 $y$ 就少 $|r|\\dfrac{\\sigma_y}{\\sigma_x}$。預測值一律從重心出發再加減。' },
    'L2.regUnits': { f: function (p) { return p.kind; }, why: '換單位 $u=px$、$v=qy$ 時新斜率 $=$ 舊斜率 $\\times\\dfrac qp$；若是 $u=100-x$ 這種「反向」的變換，斜率還要再變號，而且相關係數的正負也跟著翻。先看 $p,q$ 的正負，再算大小。' },
    'L2.pctFreqSquare': { f: function (p) { return p.kind; }, why: '次數分配表求百分位數都是「累積次數第一次 $\\ge t$ 的那一級」：次數是 $k^2$ 時累積是 $\\sum k^2$、次數是 $k+1$ 時累積是等差級數——公式不同，找位置的方法相同。' },
    'L2.growthMixed': { f: function (p) { return p.kind; }, why: '平均成長率是「倍率相乘再開 $n$ 次方」：漲「幾元」要先換成倍率才能相乘；反求第三年的成長率則是把目標倍率的 $n$ 次方除以前幾年的倍率。成長率不能直接相加平均。' }
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
      /* 原始 <>（瀏覽器會當標籤）、全形頓號（KaTeX 嚴格模式拒收）、\times 後接字母（變成未定義指令）一律在這裡修 */
      return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ').replace(/、/g, ',\\ ').replace(/\\times(?=[A-Za-z])/g, '\\times ') + '$';
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

  return { makeRng: makeRng, L0: L0, L1: L1, L2: L2, L3: L3, L3_FIX: L3_FIX, META: META, PREREQ: PREREQ, CONTRAST: CONTRAST, contrastPair: contrastPair, _util: { gcd: gcd, F: F, Fr: Fr, dec: dec, sqrtTex: sqrtTex, sqrtFracTex: sqrtFracTex } };
}));
