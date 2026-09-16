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
             h: '先由小到大排好：$7$ 筆的中位數是第 $4$ 筆；出現最多次的是眾數；平均數 $=$ 總和 $\\div7$。',
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
    return { q: '某科學期成績的計算方式：' + parts.join('、') + '。' + NAMES[r.int(0, 5)] + '目前' + given.join('、') + '。若學期成績要達到 ' + T(String(target)) + ' 分（含）以上，' + names[idx] + '至少要考幾分？（分數為整數）',
             a: '至少 ' + T(String(ans)) + ' 分' + (need.d === 1 ? '' : '（不等式解得 ' + T('\\ge' + dec(need)) + '，取整數）'),
             h: '列加權平均的不等式 $\\sum(\\text{權重}\\times\\text{分數})\\ge' + target + '$，未知數只有一個；權重加總要是 $100\\%$。',
             p: { w: w, s: s, idx: idx, target: target, ans: ans } };
  };
  L1.freqTable = function (r) {
    var base = r.pick([[1, 2, 3, 4, 5], [60, 70, 80, 90, 100], [0, 1, 2, 3, 4], [2, 4, 6, 8, 10]]);
    var vals = base.slice(0, 4), cnts = [], n;
    do { cnts = [r.int(1, 8), r.int(1, 8), r.int(1, 8), r.int(1, 8)]; n = sumArr(cnts); } while (n < 8);
    var data = []; for (var i = 0; i < 4; i++) for (var j = 0; j < cnts[i]; j++) data.push(vals[i]);
    var mu = meanF(data), me = pctF(data, 50);
    var rows = []; for (i = 0; i < 4; i++) rows.push(T(String(vals[i])) + ' 出現 ' + T(String(cnts[i])) + ' 次');
    return { q: '某組資料共 ' + T(String(n)) + ' 筆：' + rows.join('、') + '。求此組資料的算術平均數與中位數。',
             a: T('\\mu=' + dec(mu)) + '、' + T('Me=' + dec(me)),
             h: '平均數 $=\\dfrac{\\sum(\\text{數值}\\times\\text{次數})}{' + n + '}$；中位數先看 $n$ 的奇偶，再用累積次數找第 $\\frac{n}{2}$、$\\frac{n}{2}+1$ 筆落在哪一格。',
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
    var rem = [mu + r.int(16, 30), mu - r.int(16, 30)], mu3 = F(n * mu - rem[0] - rem[1], n - 2);
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
    return { q: '某組資料為 ' + T(listTex(data)) + '。求 (1) 全距　(2) 算術平均數　(3) 變異數與標準差。',
             a: '(1) ' + T(String(mx - mn)) + '　(2) ' + T('\\mu=' + dec(mu)) + '　(3) ' + T('\\sigma^2=' + dec(va)) + '、' + T('\\sigma=' + sqrtBoth(va)),
             h: '先算平均，再把每筆的「偏差」寫出來（總和必為 $0$，可當檢查），偏差平方和除以 $n$ 就是變異數。',
             p: { data: data, ans: { range: mx - mn, mu: fr2(mu), var: fr2(va) } } };
  };
  L1.sdFromSums = function (r) {
    var n = r.pick([5, 6, 8, 10, 12]), data = devData(r, n), sx = sumArr(data), sxx = sumArr(data.map(function (v) { return v * v; }));
    var mu = meanF(data), va = varF(data);
    return { q: '已知 ' + T(String(n)) + ' 筆資料滿足 ' + T('\\displaystyle\\sum_{i=1}^{' + n + '}x_i=' + sx) + ' 且 ' + T('\\displaystyle\\sum_{i=1}^{' + n + '}x_i^2=' + sxx) + '。求此組資料的平均數與標準差。',
             a: T('\\mu=' + dec(mu)) + '、' + T('\\sigma^2=\\dfrac{' + sxx + '}{' + n + '}-' + (mu.d === 1 ? mu.n + '^2' : '\\left(' + Fr.tex(mu, true) + '\\right)^2') + '=' + dec(va)) + '、' + T('\\sigma=' + sqrtBoth(va)),
             h: '$\\sigma^2=\\dfrac{\\sum x_i^2}{n}-\\mu^2$（平方的平均減平均的平方），不必知道每一筆是多少。',
             p: { n: n, sx: sx, sxx: sxx, ans: { mu: fr2(mu), var: fr2(va) } } };
  };
  L1.sumSqFromStats = function (r) {
    var n = r.pick([5, 8, 10, 12, 15, 20]), mu = r.int(5, 60), sg = r.int(2, 12), a = mu + r.pick([-5, -4, -3, -2, 2, 3, 4, 5]);
    var s2 = n * (sg * sg + mu * mu), sa = n * sg * sg + n * (mu - a) * (mu - a);
    return { q: '某 ' + T(String(n)) + ' 筆資料的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。求 (1) ' + T('\\displaystyle\\sum_{i=1}^{' + n + '}x_i^2') + '　(2) ' + T('\\displaystyle\\sum_{i=1}^{' + n + '}(x_i-' + a + ')^2') + '。',
             a: '(1) ' + T(n + '(' + sg + '^2+' + mu + '^2)=' + s2) + '　(2) ' + T(n + '\\cdot' + sg + '^2+' + n + '(' + mu + '-' + a + ')^2=' + sa),
             h: '$\\sum x_i^2=n(\\sigma^2+\\mu^2)$；$\\sum(x_i-a)^2=n\\sigma^2+n(\\mu-a)^2$（拆成「對平均的平方和」加「平均離 $a$ 多遠」）。',
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
             h: '兩步：先用人數加權算合併平均；再套 $\\sigma^2=\\dfrac{n_1[\\sigma_1^2+(\\mu_1-\\mu)^2]+n_2[\\sigma_2^2+(\\mu_2-\\mu)^2]}{n_1+n_2}$。',
             p: { n1: n1, m1: m1, s1: s1, n2: n2, m2: m2, s2: s2, ans: { mu: fr2(mu), var: fr2(va) } } };
  };

  /* ── §1-4 線性變換與標準化 ── */
  L1.linearTrans = function (r) {
    var mu = r.int(20, 80), sg = r.pick([3, 4, 5, 6, 8, 10, 12]);
    var a = r.pick([F(2), F(3), F(-2), F(-1), F(1, 2), F(3, 2), F(-1, 2), F(4, 5), F(6, 5)]), b = r.nz(-20, 40);
    var muy = Fr.add(Fr.mul(a, F(mu)), F(b)), sgy = Fr.mul(Fr.abs(a), F(sg)), vy = Fr.mul(sgy, sgy);
    var ax = Fr.eq(a, F(1)) ? '' : (Fr.eq(a, F(-1)) ? '-' : dec(a));
    return { q: '某組資料 ' + T('x') + ' 的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。令 ' + T('y=' + ax + 'x' + (b > 0 ? '+' + b : String(b))) + '，求 ' + T('y') + ' 的平均數、標準差與變異數。',
             a: T('\\mu_y=' + dec(muy)) + '、' + T('\\sigma_y=' + dec(sgy)) + '、' + T('\\sigma_y^2=' + dec(vy)),
             h: '$\\mu_y=a\\mu_x+b$，$\\sigma_y=|a|\\sigma_x$（平移不改變標準差；係數要取絕對值）。',
             p: { mu: mu, sg: sg, a: fr2(a), b: b, ans: { mu: fr2(muy), sg: fr2(sgy) } } };
  };
  L1.inverseTrans = function (r) {
    var a = r.pick([F(1, 2), F(3, 5), F(4, 5), F(3, 4), F(6, 5), F(3, 2), F(2)]);
    var s1 = a.d * r.pick([2, 3, 4, 5]), mu1 = r.int(35, 60), b = r.int(8, 40);
    var s2 = Fr.mul(a, F(s1)), mu2 = Fr.add(Fr.mul(a, F(mu1)), F(b)), s = r.int(20, 90), y = Fr.add(Fr.mul(a, F(s)), F(b));
    return { q: '老師把全班成績依 ' + T('y=ax+b') + '（' + T('a\\gt0') + '）調整後，平均數由 ' + T(String(mu1)) + ' 變成 ' + T(dec(mu2)) + '、標準差由 ' + T(String(s1)) + ' 變成 ' + T(dec(s2)) + '。(1) 求 ' + T('a') + ' 與 ' + T('b') + '。　(2) 原本考 ' + T(String(s)) + ' 分的同學，調整後是幾分？',
             a: '(1) ' + T('a=\\dfrac{' + dec(s2) + '}{' + s1 + '}=' + dec(a)) + '、' + T('b=' + dec(mu2) + '-' + dec(a) + '(' + mu1 + ')=' + b) + '　(2) ' + T(dec(y)) + ' 分',
             h: '標準差只跟 $a$ 有關：$a=\\dfrac{\\sigma_y}{\\sigma_x}$；再用平均數 $\\mu_y=a\\mu_x+b$ 求 $b$。',
             p: { mu1: mu1, s1: s1, mu2: fr2(mu2), s2: fr2(s2), s: s, ans: { a: fr2(a), b: b, y: fr2(y) } } };
  };
  L1.zCompare = function (r) {
    var sub = r.shuffle(SUBJ).slice(0, 2), z1, z2, x1, x2, m1, m2, g1, g2, tries = 0;
    do {
      m1 = r.int(55, 80); m2 = r.int(55, 80); g1 = r.pick([4, 5, 8, 10, 12]); g2 = r.pick([4, 5, 8, 10, 12]);
      x1 = m1 + g1 * r.pick([-1, 1, 2]) + r.pick([0, g1 / 2 | 0]); x2 = m2 + g2 * r.pick([-1, 1, 2]) + r.pick([0, g2 / 2 | 0]);
      z1 = F(x1 - m1, g1); z2 = F(x2 - m2, g2); tries++;
    } while (Fr.eq(z1, z2) && tries < 30);
    var better = Fr.lt(z2, z1) ? 0 : 1;
    return { q: NAMES[r.int(0, 5)] + '的' + sub[0] + '考 ' + T(String(x1)) + ' 分（全班平均 ' + T(String(m1)) + '、標準差 ' + T(String(g1)) + '），' + sub[1] + '考 ' + T(String(x2)) + ' 分（全班平均 ' + T(String(m2)) + '、標準差 ' + T(String(g2)) + '）。(1) 求兩科的標準化分數 ' + T('z') + '。　(2) 哪一科在班上的相對表現較好？',
             a: '(1) ' + sub[0] + ' ' + T('z=\\dfrac{' + x1 + '-' + m1 + '}{' + g1 + '}=' + dec(z1)) + '、' + sub[1] + ' ' + T('z=\\dfrac{' + x2 + '-' + m2 + '}{' + g2 + '}=' + dec(z2)) + '　(2) ' + sub[better] + '（' + T('z') + ' 較大）',
             h: '$z=\\dfrac{x-\\mu}{\\sigma}$ 量的是「高出平均幾個標準差」；比原始分數沒有意義。',
             p: { x1: x1, m1: m1, g1: g1, x2: x2, m2: m2, g2: g2, ans: { z1: fr2(z1), z2: fr2(z2), better: better } } };
  };
  L1.zInverse = function (r) {
    var mu = r.int(55, 80), sg = r.pick([4, 5, 6, 8, 10, 12]), kind = r.int(0, 1);
    if (kind === 0) {
      var z = r.pick([F(-2), F(-3, 2), F(-1), F(-1, 2), F(1, 2), F(1), F(3, 2), F(2), F(5, 2)]), x = Fr.add(F(mu), Fr.mul(z, F(sg)));
      return { q: '某科成績的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。某生的標準化分數 ' + T('z=' + dec(z)) + '，求他的原始分數。',
               a: T('x=' + mu + '+(' + dec(z) + ')(' + sg + ')=' + dec(x)) + ' 分', h: '由 $z=\\dfrac{x-\\mu}{\\sigma}$ 反解 $x=\\mu+z\\sigma$。',
               p: { kind: 0, mu: mu, sg: sg, z: fr2(z), ans: fr2(x) } };
    }
    var xv = mu + sg * r.pick([-2, -1, 1, 2]) + r.pick([0, 0, sg / 2 | 0, -(sg / 2 | 0)]), zz = F(xv - mu, sg);
    return { q: '某科成績的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。考 ' + T(String(xv)) + ' 分的同學，標準化分數 ' + T('z') + ' 是多少？標準化之後全班成績的平均數與標準差各是多少？',
             a: T('z=\\dfrac{' + xv + '-' + mu + '}{' + sg + '}=' + dec(zz)) + '；標準化後平均 ' + T('0') + '、標準差 ' + T('1'),
             h: '$z=\\dfrac{x-\\mu}{\\sigma}$；任何資料標準化後都是 $\\mu_z=0$、$\\sigma_z=1$。',
             p: { kind: 1, mu: mu, sg: sg, x: xv, ans: fr2(zz) } };
  };
  L1.tScore = function (r) {
    var mu = r.int(55, 75), sg = r.pick([4, 5, 8, 10, 12, 15]), kind = r.int(0, 1);
    if (kind === 0) {
      var s = mu + sg * r.pick([-2, -1, 1, 2]) + r.pick([0, sg / 2 | 0, -(sg / 2 | 0)]), Tv = Fr.add(F(50), Fr.mul(F(10), F(s - mu, sg)));
      return { q: T('T') + ' 分數定義為 ' + T('T=50+10\\cdot\\dfrac{S-\\mu}{\\sigma}') + '。某科平均 ' + T(String(mu)) + ' 分、標準差 ' + T(String(sg)) + ' 分，某生考 ' + T(String(s)) + ' 分，求他的 ' + T('T') + ' 分數。',
               a: T('T=50+10\\cdot\\dfrac{' + s + '-' + mu + '}{' + sg + '}=' + dec(Tv)), h: '先算 $z$，再 $T=50+10z$：$T$ 分數就是把 $z$ 放大 $10$ 倍後搬到 $50$。',
               p: { kind: 0, mu: mu, sg: sg, s: s, ans: fr2(Tv) } };
    }
    var Tg = r.pick([30, 35, 40, 45, 55, 60, 65, 70, 75]), S = Fr.add(F(mu), Fr.mul(F(Tg - 50, 10), F(sg)));
    return { q: T('T') + ' 分數定義為 ' + T('T=50+10\\cdot\\dfrac{S-\\mu}{\\sigma}') + '。某科平均 ' + T(String(mu)) + ' 分、標準差 ' + T(String(sg)) + ' 分。' + T('T') + ' 分數為 ' + T(String(Tg)) + ' 的同學，原始成績是幾分？',
             a: T('z=\\dfrac{' + Tg + '-50}{10}=' + dec(F(Tg - 50, 10))) + ' ⟹ ' + T('S=' + mu + '+(' + dec(F(Tg - 50, 10)) + ')(' + sg + ')=' + dec(S)) + ' 分',
             h: '由 $T$ 反推 $z=\\dfrac{T-50}{10}$，再 $S=\\mu+z\\sigma$。',
             p: { kind: 1, mu: mu, sg: sg, T: Tg, ans: fr2(S) } };
  };

  /* ── §1-5 平均成長率 ── */
  var GROW2 = [[60, -10, 20], [80, -20, 20], [-20, 80, 20], [44, 0, 20], [21, 0, 10], [80, 25, 50], [150, -10, 50], [200, -25, 50], [125, 0, 50], [69, 0, 30], [160, -35, 30], [96, 21, 54], [10, 10, 10], [25, 25, 25], [-40, -40, -40], [-20, -20, -20]];
  var GROW3 = [[8, 25, 28, 20], [60, 20, -10, 20], [50, 28, -10, 20], [60, 35, -20, 20], [-2, 12, 28, 12], [10, 21, 0, 10], [80, 25, 50, 50], [170, 25, 0, 50], [44, 20, 0, 20], [20, 20, 20, 20], [-10, -10, -10, -10]];
  L1.growthRate = function (r) {
    var row = r.pick(r.int(0, 1) ? GROW2 : GROW3), rates = row.slice(0, row.length - 1), g = row[row.length - 1];
    var item = r.pick(['某商品的價格', '某公司的營收', '某城市的人口', '某股票的價格']);
    var txt = rates.map(function (v) { return T((v < 0 ? '-' : '') + Math.abs(v) + '\\%'); }).join('、');
    var prod = rates.map(function (v) { return '(1' + (v < 0 ? '-' : '+') + dec(F(Math.abs(v), 100)) + ')'; }).join('');
    var pf = F(1); rates.forEach(function (v) { pf = Fr.mul(pf, F(100 + v, 100)); });
    return { q: item + '連續 ' + T(String(rates.length)) + ' 年的成長率依序為 ' + txt + '。求這 ' + T(String(rates.length)) + ' 年的平均成長率。',
             a: T('(1+\\bar r)^' + rates.length + '=' + prod + '=' + dec(pf) + '=(' + dec(F(100 + g, 100)) + ')^' + rates.length) + ' ⟹ ' + T('\\bar r=' + (g < 0 ? '-' : '') + Math.abs(g) + '\\%'),
             h: '成長率要用「乘」的：$(1+\\bar r)^n=(1+r_1)(1+r_2)\\cdots$，右邊乘出來會恰好是某個數的 $n$ 次方——不能把成長率直接平均。',
             p: { rates: rates, ans: g } };
  };
  var GROWT = [[100, 121, 2, 10], [1000, 1331, 3, 10], [100, 144, 2, 20], [200, 288, 2, 20], [500, 720, 2, 20], [1000, 1728, 3, 20], [500, 864, 3, 20], [400, 625, 2, 25], [800, 1250, 2, 25], [512, 1000, 3, 25], [100, 225, 2, 50], [400, 900, 2, 50], [200, 675, 3, 50], [400, 1350, 3, 50], [100, 64, 2, -20], [500, 320, 2, -20], [1000, 512, 3, -20], [100, 81, 2, -10], [1000, 729, 3, -10], [400, 196, 2, -30], [1000, 343, 3, -30]];
  L1.growthTotal = function (r) {
    var row = r.pick(GROWT), A = row[0], B = row[1], n = row[2], g = row[3], kind = r.int(0, 1);
    var item = r.pick(['某商品的價格', '某地區的房價指數', '某公司的年營收（萬元）', '某社團的人數']);
    var q = kind === 0
      ? item + '從 ' + T(String(A)) + ' 經過 ' + T(String(n)) + ' 次調整後變成 ' + T(String(B)) + '。求平均每次的成長率。'
      : item + '經過 ' + T(String(n)) + ' 年後變成原來的 ' + T(dec(F(B, A))) + ' 倍。求平均每年的成長率。';
    return { q: q, a: T('(1+\\bar r)^' + n + '=\\dfrac{' + B + '}{' + A + '}=' + dec(F(B, A)) + '=(' + dec(F(100 + g, 100)) + ')^' + n) + ' ⟹ ' + T('\\bar r=' + (g < 0 ? '-' : '') + Math.abs(g) + '\\%'),
             h: '只看首尾：$(1+\\bar r)^n=\\dfrac{\\text{末}}{\\text{初}}$，開 $n$ 次方根；比值小於 $1$ 就是負成長。',
             p: { A: A, B: B, n: n, ans: g } };
  };

  /* ── §2-1 相關係數 ── */
  L1.corrData = function (r) {
    var d = makeXY(r, false);
    return { q: '五筆二維資料 ' + T('(x,y)') + ' 為 ' + T(pairsTex(d.x, d.y)) + '。求 ' + T('x') + ' 與 ' + T('y') + ' 的相關係數 ' + T('r') + '。',
             a: T('\\mu_x=' + d.mx + '、\\mu_y=' + d.my) + '；' + T('S_{xx}=' + d.sxx + '、S_{yy}=' + d.syy + '、S_{xy}=' + d.sxy) + ' ⟹ ' + T('r=\\dfrac{' + d.sxy + '}{\\sqrt{' + d.sxx + '\\times' + d.syy + '}}=' + dec(d.r)),
             h: '先算兩個平均，把兩排偏差寫出來；$r=\\dfrac{\\sum(x_i-\\mu_x)(y_i-\\mu_y)}{\\sqrt{\\sum(x_i-\\mu_x)^2\\sum(y_i-\\mu_y)^2}}$，段考的數字一定開得出來。',
             p: { x: d.x, y: d.y, ans: fr2(d.r) } };
  };
  L1.corrSums = function (r) {
    var d = makeXY(r, false), sx = sumArr(d.x), sy = sumArr(d.y), sxx = sumArr(d.x.map(function (v) { return v * v; })), syy = sumArr(d.y.map(function (v) { return v * v; }));
    var sxy = 0; for (var i = 0; i < 5; i++) sxy += d.x[i] * d.y[i];
    return { q: '有 ' + T('5') + ' 組資料 ' + T('(x_i,y_i)') + '，已知 ' + T('\\sum x_i=' + sx + ',\\ \\sum x_i^2=' + sxx + ',\\ \\sum y_i=' + sy + ',\\ \\sum y_i^2=' + syy + ',\\ \\sum x_iy_i=' + sxy) + '。求相關係數 ' + T('r') + '。',
             a: T('S_{xx}=' + sxx + '-\\dfrac{' + sx + '^2}{5}=' + d.sxx + '、S_{yy}=' + syy + '-\\dfrac{' + sy + '^2}{5}=' + d.syy + '、S_{xy}=' + sxy + '-\\dfrac{' + sx + '\\cdot' + sy + '}{5}=' + d.sxy) + ' ⟹ ' + T('r=' + dec(d.r)),
             h: '$S_{xx}=\\sum x^2-\\dfrac{(\\sum x)^2}{n}$、$S_{yy}=\\sum y^2-\\dfrac{(\\sum y)^2}{n}$、$S_{xy}=\\sum xy-\\dfrac{\\sum x\\sum y}{n}$，三個都是「減掉平均的貢獻」。',
             p: { n: 5, sx: sx, sxx: sxx, sy: sy, syy: syy, sxy: sxy, ans: fr2(d.r) } };
  };
  L1.corrTransform = function (r) {
    var rr = r.pick([F(3, 5), F(-3, 5), F(4, 5), F(-4, 5), F(1, 2), F(-1, 2), F(3, 4), F(-3, 4), F(9, 10), F(-9, 10), F(7, 10), F(-7, 10)]);
    var pairs = [], anss = [], texs = [];
    for (var i = 0; i < 3; i++) {
      var a = r.pick([2, 3, -1, -2, -3, 5]), c = r.pick([1, 2, 3, -1, -2, -4]), b = r.nz(-9, 9), dd = r.nz(-9, 9);
      pairs.push([a, c]);
      var rv = a * c > 0 ? rr : F(-rr.n, rr.d); anss.push(rv);
      texs.push('(' + (a === 1 ? '' : a === -1 ? '-' : a) + 'x' + (b > 0 ? '+' + b : b) + ',\\ ' + (c === 1 ? '' : c === -1 ? '-' : c) + 'y' + (dd > 0 ? '+' + dd : dd) + ')');
    }
    return { q: '已知 ' + T('x') + ' 與 ' + T('y') + ' 的相關係數為 ' + T(dec(rr)) + '。求下列各組新資料的相關係數：(1) ' + T(texs[0]) + '　(2) ' + T(texs[1]) + '　(3) ' + T(texs[2]),
             a: '(1) ' + T(dec(anss[0])) + '　(2) ' + T(dec(anss[1])) + '　(3) ' + T(dec(anss[2])),
             h: '$(ax+b,\\ cy+d)$ 的相關係數只看 $ac$ 的正負：$ac\\gt0$ 不變、$ac\\lt0$ 變號；平移 $b,d$ 完全沒影響。',
             p: { r: fr2(rr), ac: pairs, ans: anss.map(fr2) } };
  };
  L1.corrPerfect = function (r) {
    var a = r.pick([F(2), F(-2), F(3), F(-3), F(1, 2), F(-1, 2), F(3, 2), F(-3, 4), F(4, 5)]), b = r.nz(-10, 20), mu = r.int(10, 60), sg = r.pick([2, 4, 5, 6, 8, 10]);
    var muy = Fr.add(Fr.mul(a, F(mu)), F(b)), sgy = Fr.mul(Fr.abs(a), F(sg)), rv = a.n > 0 ? 1 : -1;
    return { q: '設 ' + T('n') + ' 筆二維資料滿足 ' + T('y_i=' + (Fr.eq(a, F(1)) ? '' : dec(a)) + 'x_i' + (b > 0 ? '+' + b : String(b))) + '，且 ' + T('x') + ' 的平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。求 ' + T('y') + ' 的平均數、標準差、' + T('x') + ' 與 ' + T('y') + ' 的相關係數，以及 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線。',
             a: T('\\mu_y=' + dec(muy)) + '、' + T('\\sigma_y=' + dec(sgy)) + '、' + T('r=' + rv) + '、最適直線就是 ' + T(lineTex(a, F(b))),
             h: '所有點都在同一條直線上 ⟹ $r=\\pm1$（正負看斜率），最適直線就是那條直線本身；$\\sigma_y=|a|\\sigma_x$。',
             p: { a: fr2(a), b: b, mu: mu, sg: sg, ans: { mu: fr2(muy), sg: fr2(sgy), r: rv } } };
  };

  /* ── §2-2 最適直線 ── */
  L1.fitData = function (r) {
    var d = makeXY(r, false);
    return { q: '五筆二維資料 ' + T('(x,y)') + ' 為 ' + T(pairsTex(d.x, d.y)) + '。求 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線（以 ' + T('y=ax+b') + ' 作答）。',
             a: T('\\mu_x=' + d.mx + '、\\mu_y=' + d.my + '、S_{xx}=' + d.sxx + '、S_{xy}=' + d.sxy) + ' ⟹ 斜率 ' + T('a=\\dfrac{' + d.sxy + '}{' + d.sxx + '}=' + dec(d.slope)) + '，直線 ' + T(lineTex(d.slope, d.icpt)),
             h: '斜率 $=\\dfrac{S_{xy}}{S_{xx}}$，再用「必過重心 $(\\mu_x,\\mu_y)$」寫出直線：$y-\\mu_y=a(x-\\mu_x)$。',
             p: { x: d.x, y: d.y, ans: { a: fr2(d.slope), b: fr2(d.icpt) } } };
  };
  L1.fitStats = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(3, 4), F(1, 2), F(-3, 5), F(-4, 5), F(-1, 2), F(7, 10)]);
    var sx = r.pick([4, 5, 8, 10]), sy = r.pick([4, 6, 8, 10, 12]), mx = r.int(40, 70), my = r.int(40, 80);
    var slope = Fr.mul(rr, F(sy, sx)), icpt = Fr.sub(F(my), Fr.mul(slope, F(mx))), x0 = mx + r.pick([-10, -5, 5, 10, 20]), yh = Fr.add(F(my), Fr.mul(slope, F(x0 - mx)));
    return { q: '已知 ' + T('\\mu_x=' + mx + '、\\mu_y=' + my + '、\\sigma_x=' + sx + '、\\sigma_y=' + sy) + '，相關係數 ' + T('r=' + dec(rr)) + '。(1) 求 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線。　(2) 當 ' + T('x=' + x0) + ' 時，' + T('y') + ' 的預測值是多少？',
             a: '(1) 斜率 ' + T('=r\\dfrac{\\sigma_y}{\\sigma_x}=' + dec(rr) + '\\times\\dfrac{' + sy + '}{' + sx + '}=' + dec(slope)) + '，過 ' + T('(' + mx + ',' + my + ')') + ' ⟹ ' + T(lineTex(slope, icpt)) + '　(2) ' + T('\\hat y=' + my + '+' + dec(slope) + '(' + x0 + '-' + mx + ')=' + dec(yh)),
             h: '斜率 $=r\\dfrac{\\sigma_y}{\\sigma_x}$；直線必過 $(\\mu_x,\\mu_y)$。預測時直接從重心出發：$\\hat y=\\mu_y+\\text{斜率}\\times(x_0-\\mu_x)$。',
             p: { r: fr2(rr), sx: sx, sy: sy, mx: mx, my: my, x0: x0, ans: { a: fr2(slope), b: fr2(icpt), yh: fr2(yh) } } };
  };
  L1.fitCentroid = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(3, 4), F(1, 2), F(2, 5), F(-3, 5), F(-4, 5), F(-1, 2)]);
    var sx = r.pick([4, 5, 8, 10, 12]), sy = r.pick([4, 5, 6, 8, 10, 12]), a = Fr.mul(rr, F(sy, sx));
    var mx = r.int(40, 75), b = r.int(-30, 60), my = Fr.add(Fr.mul(a, F(mx)), F(b));
    return { q: '某班數學成績 ' + T('x') + ' 的平均數為 ' + T(String(mx)) + '、標準差為 ' + T(String(sx)) + '；英文成績 ' + T('y') + ' 的標準差為 ' + T(String(sy)) + '。已知 ' + T('y') + ' 對 ' + T('x') + ' 的最適直線為 ' + T(lineTex(a, F(b))) + '。(1) 求英文成績的平均數。　(2) 求兩科的相關係數 ' + T('r') + '。',
             a: '(1) 直線過重心 ⟹ ' + T('\\mu_y=' + dec(a) + '(' + mx + ')' + (b >= 0 ? '+' + b : b) + '=' + dec(my)) + '　(2) ' + T(dec(a) + '=r\\cdot\\dfrac{' + sy + '}{' + sx + '}') + ' ⟹ ' + T('r=' + dec(rr)),
             h: '兩個性質：直線必過 $(\\mu_x,\\mu_y)$（代 $\\mu_x$ 就得 $\\mu_y$）；斜率 $=r\\dfrac{\\sigma_y}{\\sigma_x}$（反解 $r$）。',
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
             h: '線性變換後 $\\sigma$ 各乘 $|p|$、$|s|$，$r$ 看 $ps$ 的正負；新斜率 $=\\dfrac{s}{p}\\times$ 舊斜率，新直線過新重心 $(p\\mu_x+q,\\ s\\mu_y+t)$。',
             p: { r: fr2(rr), sx: sx, sy: sy, mx: mx, my: my, p: fr2(p), q: q, s: fr2(s), t: t, ans: { a: fr2(slope2), b: fr2(icpt2) } } };
  };
  L1.stdFit = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(1, 2), F(7, 10), F(9, 10), F(-3, 5), F(-4, 5), F(-1, 2), F(-7, 10)]), c = r.pick([F(-2), F(-3, 2), F(-1), F(-1, 2), F(1, 2), F(1), F(3, 2), F(2)]);
    var yh = Fr.mul(rr, c);
    return { q: '某二維資料的相關係數為 ' + T('r=' + dec(rr)) + '。把 ' + T('x') + '、' + T('y') + ' 都標準化為 ' + T("x''") + '、' + T("y''") + '。(1) 求 ' + T("y''") + ' 對 ' + T("x''") + ' 的最適直線。　(2) 某筆資料的 ' + T("x''=" + dec(c)) + '，用此直線預測它的 ' + T("y''") + '。',
             a: '(1) ' + T("y''=" + dec(rr) + "x''") + '（過原點，斜率就是 ' + T('r') + '）　(2) ' + T("\\hat y''=" + dec(rr) + '\\times(' + dec(c) + ')=' + dec(yh)),
             h: '標準化後 $\\mu=0$、$\\sigma=1$ ⟹ 斜率 $=r\\cdot\\frac11=r$，且必過 $(0,0)$。',
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
             h: '兩個條件、兩個未知數：① 直線必過 $(\\mu_x,\\mu_y)$ 給 $a+b$；② 斜率 $=\\dfrac{S_{xy}}{S_{xx}}$，$x$ 只取兩個值，偏差是 $\\mp\\frac{' + gap + '}{2}$，展開後 $\\mu_y$ 會消掉，只剩 $a-b$。',
             p: { x: xs, y: ys, slope: fr2(s), icpt: fr2(c), ans: { a: a, b: yb, my: fr2(my) } } };
  };
  /* 2-2 由 r、迴歸直線與 y 的統計量反推 x 的平均與標準差（例題 30 型） */
  L2.regReverse = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(3, 4), F(1, 2), F(2, 5)]), sy = r.pick([4, 5, 6, 8, 10]), sx = r.pick([4, 5, 8, 10]);
    var s = Fr.mul(rr, F(sy, sx)), mx = r.int(40, 70), my = r.int(50, 85), b = Fr.sub(F(my), Fr.mul(s, F(mx)));
    return { q: '某班 ' + T('x') + '（數學）與 ' + T('y') + '（英文）成績的相關係數為 ' + T(dec(rr)) + '，' + T('y') + ' 對 ' + T('x') + ' 的最適直線為 ' + T(lineTex(s, b)) + '。已知英文的平均數為 ' + T(String(my)) + '、標準差為 ' + T(String(sy)) + '。求數學的平均數 ' + T('\\mu_x') + ' 與標準差 ' + T('\\sigma_x') + '。',
             a: '直線過重心：' + T(my + '=' + dec(s) + '\\mu_x' + (b.n >= 0 ? '+' : '') + dec(b)) + ' ⟹ ' + T('\\mu_x=' + mx) + '；斜率 ' + T(dec(s) + '=' + dec(rr) + '\\cdot\\dfrac{' + sy + '}{\\sigma_x}') + ' ⟹ ' + T('\\sigma_x=' + sx),
             h: '把 $\\mu_y$ 代進直線解出 $\\mu_x$；再用斜率 $=r\\dfrac{\\sigma_y}{\\sigma_x}$ 反解 $\\sigma_x$。',
             p: { r: fr2(rr), sy: sy, my: my, slope: fr2(s), icpt: fr2(b), ans: { mx: mx, sx: sx } } };
  };
  /* 2-3 兩條迴歸直線：y 對 x 與 x 對 y ⟹ 斜率相乘 = r²，交點 = 重心 */
  L2.regBothLines = function (r) {
    var rr = r.pick([F(3, 5), F(4, 5), F(1, 2), F(-3, 5), F(-4, 5), F(-1, 2)]), sx = r.pick([2, 4, 5, 10]), sy = r.pick([2, 4, 5, 10]);
    var mx = r.int(20, 60), my = r.int(20, 80);
    var b1 = Fr.mul(rr, F(sy, sx)), c1 = Fr.sub(F(my), Fr.mul(b1, F(mx)));       // y = b1 x + c1
    var b2 = Fr.mul(rr, F(sx, sy)), c2 = Fr.sub(F(mx), Fr.mul(b2, F(my)));       // x = b2 y + c2
    return { q: '某二維數據中，' + T('y') + ' 對 ' + T('x') + ' 的最適直線為 ' + T(lineTex(b1, c1)) + '，' + T('x') + ' 對 ' + T('y') + ' 的最適直線為 ' + T(lineTex(b2, c2).replace(/^y=/, 'x=').replace(/x(?=[+\\-]|$)/, 'y')) + '。(1) 求 ' + T('(\\mu_x,\\mu_y)') + '。　(2) 求相關係數 ' + T('r') + '。',
             a: '(1) 兩直線都過重心，解聯立得 ' + T('(\\mu_x,\\mu_y)=(' + mx + ',' + my + ')') + '　(2) 兩斜率相乘 ' + T(dec(b1) + '\\times' + dec(b2) + '=r^2=' + dec(Fr.mul(rr, rr))) + '，且 ' + T('r') + ' 與斜率同號 ⟹ ' + T('r=' + dec(rr)),
             h: '$y$ 對 $x$ 的斜率是 $r\\frac{\\sigma_y}{\\sigma_x}$、$x$ 對 $y$ 的斜率是 $r\\frac{\\sigma_x}{\\sigma_y}$，相乘恰為 $r^2$；兩條線都通過 $(\\mu_x,\\mu_y)$。',
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
    var sx = r.pick([F(1, 2), F(1), F(2), F(1, 5), F(3, 10), F(4)]), a = Fr.mul(rr, Fr.div(sy, sx));
    var mx = r.pick([F(5), F(6), F(52, 10), F(8), F(10), F(12)]), b = r.pick([F(-6, 10), F(4, 10), F(1), F(-2), F(3), F(-1, 2)]), my = Fr.add(Fr.mul(a, mx), b);
    var px = Fr.add(mx, r.pick([F(4, 10), F(-4, 10), F(1), F(-1), F(1, 2)])), py = Fr.add(my, r.pick([F(-12, 10), F(12, 10), F(3, 2), F(-1, 2), F(2)]));
    var within = !Fr.lt(sy, Fr.abs(Fr.sub(py, my)));   // |py-my| ≤ σy
    return { q: '某物種身長 ' + T('x') + ' 與體重 ' + T('y') + ' 的相關係數為 ' + T(dec(rr)) + '，' + T('\\mu_x=' + dec(mx)) + '、' + T('\\sigma_x=' + dec(sx)) + '，' + T('y') + ' 對 ' + T('x') + ' 的迴歸直線為 ' + T(lineTex(a, b)) + '。(1) 求 ' + T('\\mu_y') + ' 與 ' + T('\\sigma_y') + '。　(2) 個體 ' + T('P(' + dec(px) + ',' + dec(py) + ')') + ' 的體重與 ' + T('\\mu_y') + ' 之差的絕對值是否超過一個標準差？',
             a: '(1) ' + T('\\mu_y=' + dec(a) + '(' + dec(mx) + ')' + (b.n >= 0 ? '+' : '') + dec(b) + '=' + dec(my)) + '；' + T(dec(a) + '=' + dec(rr) + '\\cdot\\dfrac{\\sigma_y}{' + dec(sx) + '}') + ' ⟹ ' + T('\\sigma_y=' + dec(sy)) + '　(2) ' + T('|' + dec(py) + '-' + dec(my) + '|=' + dec(Fr.abs(Fr.sub(py, my)))) + (within ? '，沒有超過' : '，超過了') + ' ' + T('\\sigma_y=' + dec(sy)),
             h: '重心在直線上 ⟹ 代 $\\mu_x$ 得 $\\mu_y$；斜率 $=r\\dfrac{\\sigma_y}{\\sigma_x}$ ⟹ 反解 $\\sigma_y$。',
             p: { r: fr2(rr), sx: fr2(sx), mx: fr2(mx), slope: fr2(a), icpt: fr2(b), px: fr2(px), py: fr2(py), ans: { my: fr2(my), sy: fr2(sy), within: within } } };
  };
  /* 2-6 新增恰在重心的一筆（例題 33 型） */
  L2.addCentroid = function (r) {
    var n = r.pick([9, 19, 24, 49, 99]), mx = r.int(50, 80), my = r.int(30, 70), sx = r.pick([2, 4, 5, 6, 10]), sy = r.pick([2, 3, 4, 5, 8]), rr = r.pick([F(3, 5), F(4, 5), F(1, 2), F(-3, 5), F(7, 10)]);
    var vx = F(n * sx * sx, n + 1), vy = F(n * sy * sy, n + 1);
    return { q: '某檢定 ' + T(String(n)) + ' 人的筆試 ' + T('x') + ' 與實作 ' + T('y') + ' 成績：' + T('\\mu_x=' + mx + '、\\sigma_x=' + sx + '、\\mu_y=' + my + '、\\sigma_y=' + sy + '、r=' + dec(rr)) + '。後來補登一位成績恰為 ' + T('(' + mx + ',' + my + ')') + ' 的考生。求新的 ' + T(String(n + 1)) + ' 筆資料的 ' + T('\\mu_x') + '、' + T('\\sigma_x^2') + '、' + T('\\sigma_y^2') + ' 與相關係數 ' + T('r') + '。',
             a: T('\\mu_x=' + mx) + '（不變）、' + T('\\sigma_x^2=\\dfrac{' + n + '\\times' + (sx * sx) + '}{' + (n + 1) + '}=' + dec(vx)) + '、' + T('\\sigma_y^2=' + dec(vy)) + '、' + T('r=' + dec(rr)) + '（不變：三個和 ' + T('S_{xx},S_{yy},S_{xy}') + ' 都沒有增加）',
             h: '新的一筆與重心重合 ⟹ 兩個平均不變、三個偏差和都不變；分母從 $n$ 變 $n+1$ 所以變異數乘 $\\frac{n}{n+1}$，而 $r$ 的分母分子同時約掉 $n$。',
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
             h: '最小值必為 $' + (M - R) + '$。先平移成 $0$ 與 $' + R + '$ 兩端固定，其餘 $' + (n - 2) + '$ 筆全部擠到最靠近中間的整數（$' + Math.floor(R / 2) + '$ 或 $' + Math.ceil(R / 2) + '$），變異數才最小。',
             p: { n: n, M: M, R: R, ans: fr2(best) } };
  };
  /* 2-8 由 f(x)=Σ(x-x_i)² 的兩個函數值反推 μ 與 σ（107 全國模考 型） */
  L2.sumSqShift = function (r) {
    var n = r.pick([5, 8, 10, 12, 20]), mu = r.int(4, 12), sg = r.pick([2, 3, 4, 5]), d1 = r.pick([-3, -2, -1, 1]), d2 = d1 + r.pick([2, 3, 4]);
    var x1 = mu + d1, x2 = mu + d2, f1 = n * (d1 * d1 + sg * sg), f2 = n * (d2 * d2 + sg * sg);
    return { q: '設 ' + T('x_1,x_2,\\dots,x_{' + n + '}') + ' 為實數，二次函數 ' + T('f(x)=(x-x_1)^2+(x-x_2)^2+\\cdots+(x-x_{' + n + '})^2') + '。已知 ' + T('f(' + x1 + ')=' + f1) + '、' + T('f(' + x2 + ')=' + f2) + '。求這 ' + T(String(n)) + ' 個數的平均數 ' + T('\\mu') + ' 與標準差 ' + T('\\sigma') + '。',
             a: T('f(x)=' + n + '(x-\\mu)^2+' + n + '\\sigma^2') + '，兩式相減解得 ' + T('\\mu=' + mu) + '，再代回得 ' + T(n + '\\sigma^2=' + (n * sg * sg)) + ' ⟹ ' + T('\\sigma=' + sg),
             h: '$\\sum(x-x_i)^2=n(x-\\mu)^2+n\\sigma^2$：頂點在 $x=\\mu$、最小值 $n\\sigma^2$。兩個函數值相減會消掉 $\\sigma$，先解 $\\mu$。',
             p: { n: n, x1: x1, f1: f1, x2: x2, f2: f2, ans: { mu: mu, sg: sg } } };
  };
  /* 2-9 新增一筆後標準差已知，反推那一筆（台南女中 112 下 填 19 型，數字設計成整數） */
  L2.reverseAdd = function (r) {
    var m = r.pick([9, 16, 25, 36]), n = m - 1, c = r.pick([1, 1, 4]), sg = Math.sqrt(m * c), k = r.pick([1, 2]), mu = r.int(50, 75), d = m * k, y = mu + d;
    var var2 = n * (c + k * k);
    return { q: '有 ' + T(String(n)) + ' 個數據的算術平均數為 ' + T(String(mu)) + '、標準差為 ' + T(String(sg)) + '。若再加入一個數據 ' + T('y') + '（' + T('y\\gt' + mu) + '），這 ' + T(String(m)) + ' 個數據的變異數變為 ' + T(String(var2)) + '。求 ' + T('y') + '。',
             a: '令 ' + T('d=y-' + mu) + '，新平均 ' + T('=' + mu + '+\\dfrac{d}{' + m + '}') + '；新平方和 ' + T('=' + n + '\\cdot' + (sg * sg) + '+\\dfrac{' + n + '}{' + m + '}d^2=' + m + '\\times' + var2) + ' ⟹ ' + T('d^2=' + (d * d)) + ' ⟹ ' + T('y=' + y),
             h: '對新平均的平方和 $=n\\sigma^2+\\dfrac{n}{n+1}d^2$（$d$ 是新資料離舊平均的距離）；令它等於 $(n+1)\\sigma\'^2$ 解 $d$，取正根。',
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
             h: '兩個未知數各用一條式子：平均數的加權式解 $x$；合併變異數公式裡只剩 $y^2$ 未知。',
             p: { n1: n1, s1: s1, n2: n2, m2: m2, mu: mu, var: fr2(va), ans: { x: fr2(m1), y: s2 } } };
  };
  /* 2-11 線性調分：把最高分與最低分拉到指定值（103 指考乙 2 型） */
  L2.linearReverse = function (r) {
    var mn = r.int(15, 35), M = mn + r.pick([50, 60, 70, 75, 80]), mu = r.int(mn + 20, M - 15);
    var L = r.pick([40, 50, 60]), H = 100, b = F(H - L, M - mn), a = Fr.sub(F(L), Fr.mul(b, F(mn))), mu2 = Fr.add(a, Fr.mul(b, F(mu)));
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
      for (var i = 0; i < 5; i++) { var m = r.int(60, 85), g = r.pick([F(2), F(4), F(5), F(8), F(10)]); var s = m + Fr.toNum(g) * r.pick([-2, -1, 0, 1, 2]) + r.pick([0, 0, 1, -1]); sc.push(s); mu.push(m); sg.push(g); z.push(Fr.div(F(s - m), g)); }
      var vals = z.map(Fr.toNum), srt = vals.slice().sort(function (a, b) { return b - a; }); ok = srt[0] > srt[1] && srt[3] > srt[4]; tries++;
    } while (!ok && tries < 40);
    var best = 0, worst = 0; for (i = 1; i < 5; i++) { if (Fr.lt(z[best], z[i])) best = i; if (Fr.lt(z[i], z[worst])) worst = i; }
    var rows = subs.map(function (s, i) { return s + '：' + T(String(sc[i])) + ' 分（平均 ' + T(String(mu[i])) + '、標準差 ' + T(dec(sg[i])) + '）'; });
    return { q: NAMES[r.int(0, 5)] + '五科段考成績如下——' + rows.join('；') + '。哪一科在班上的相對表現最好？哪一科最差？',
             a: T('z') + ' 依序為 ' + T(z.map(dec).join(',\\ ')) + ' ⟹ 最好：' + subs[best] + '、最差：' + subs[worst],
             h: '五科各算 $z=\\dfrac{x-\\mu}{\\sigma}$；標準差小的科目，同樣高出幾分會換到更大的 $z$。',
             p: { sc: sc, mu: mu, sg: sg.map(fr2), ans: { best: best, worst: worst } } };
  };
  /* 2-13 次數呈規律的百分位數：k² 位／k+1 位（中山女高 113 下 單 2、成功 113 下 填 6 型） */
  L2.pctFreqSquare = function (r) {
    var kind = r.int(0, 1), m = kind === 0 ? r.int(6, 10) : r.int(8, 15), data = [];
    for (var v = 1; v <= m; v++) for (var j = 0; j < (kind === 0 ? v * v : v + 1); j++) data.push(v);
    var n = data.length, k = r.pick([10, 12, 20, 25, 30, 40, 50, 60, 70, 75, 80, 90]), ans = pctF(data, k), mu = meanF(data);
    var desc = kind === 0 ? '持有 $1$ 顆的有 $1$ 位、持有 $2$ 顆的有 $4$ 位、持有 $3$ 顆的有 $9$ 位，依此類推（持有 $k$ 顆的有 $k^2$ 位），持有 $' + m + '$ 顆的有 $' + (m * m) + '$ 位'
                          : '$1$ 出現 $2$ 次、$2$ 出現 $3$ 次、$3$ 出現 $4$ 次，依此類推，$' + m + '$ 出現 $' + (m + 1) + '$ 次';
    return { q: (kind === 0 ? '某遊戲共有 ' + T(String(n)) + ' 位玩家，每位都持有寶石：' : '某組資料共 ' + T(String(n)) + ' 筆：') + desc + '。(1) 求第 ' + T(String(k)) + ' 百分位數。　(2) 求算術平均數。',
             a: '(1) ' + T('t=\\dfrac{' + n + '\\times' + k + '}{100}=' + dec(tOf(n, k))) + ' ⟹ ' + T('P_{' + k + '}=' + dec(ans)) + '　(2) ' + T('\\mu=' + dec(mu)),
             h: '先算總筆數（$\\sum k^2=\\frac{m(m+1)(2m+1)}{6}$ 或 $\\sum(k+1)$），再列累積次數表看第 $t$ 筆落在哪個值；平均數用 $\\sum(\\text{值}\\times\\text{次數})$。',
             p: { kind: kind, m: m, k: k, ans: { pk: fr2(ans), mu: fr2(mu) } } };
  };
  /* 2-14 成長率混合題：金額漲幅＋百分比／反推最後一年至少（竹科實中 113 下 單 4、例題 17 型） */
  /* [P0, ΔP, r2%, r3%, 平均 g%]：(1+ΔP/P0)(1+r2)(1+r3) = (1+g)³，全部驗過 */
  var GROWM = [[50, 4, 25, 28, 20], [25, 2, 25, 28, 20], [100, 8, 25, 28, 20], [50, 30, 20, -10, 20], [20, 10, 28, -10, 20], [100, 60, 35, -20, 20], [100, 10, 21, 0, 10], [50, 40, 25, 50, 50], [25, 11, 20, 0, 20], [50, 10, 20, 20, 20]];
  var GROWR = [[25, 28, 40, 71.5], [20, 20, 20, 20], [10, 21, 10, 0], [60, 20, 20, -10], [8, 25, 20, 28], [80, 25, 50, 50], [44, 20, 20, 0], [50, 28, 20, -10], [60, 35, 20, -20], [-2, 12, 12, 28]];
  L2.growthMixed = function (r) {
    var kind = r.int(0, 1);
    if (kind === 0) {
      var row = r.pick(GROWM), P0 = row[0], dP = row[1], r2 = row[2], r3 = row[3], g = row[4], r1 = F(dP * 100, P0);
      return { q: '某商品去年底單價 ' + T(String(P0)) + ' 元。今年一月比去年底漲 ' + T(String(dP)) + ' 元，二月比一月漲 ' + T(r2 + '\\%') + '，三月比二月' + (r3 >= 0 ? '漲 ' + T(r3 + '\\%') : '跌 ' + T((-r3) + '\\%')) + '。求這三個月平均每月的成長率。',
               a: '第一個月的漲幅是 ' + T('\\dfrac{' + dP + '}{' + P0 + '}=' + dec(r1) + '\\%') + '；' + T('(1+\\bar r)^3=' + dec(Fr.add(F(1), F(dP, P0))) + '\\times' + dec(F(100 + r2, 100)) + '\\times' + dec(F(100 + r3, 100)) + '=' + dec(F(Math.round(Math.pow(1 + g / 100, 3) * 1e6), 1e6))) + ' ⟹ ' + T('\\bar r=' + g + '\\%'),
               h: '「漲多少錢」要先換成「漲幾成」：$\\frac{' + dP + '}{' + P0 + '}$；然後三個倍率相乘開三次方根。',
               p: { kind: 0, P0: P0, dP: dP, r2: r2, r3: r3, ans: g } };
    }
    var rw = r.pick(GROWR), a1 = rw[0], a2 = rw[1], g2 = rw[2], need = rw[3];
    return { q: '某公司前兩年的營業額成長率分別為 ' + T(a1 + '\\%') + '、' + T(a2 + '\\%') + '。若這三年的平均成長率要達到 ' + T(g2 + '\\%') + '（含）以上，則第三年的成長率至少要多少？',
             a: T('(1+r_3)\\ge\\dfrac{(' + dec(F(100 + g2, 100)) + ')^3}{' + dec(F(100 + a1, 100)) + '\\times' + dec(F(100 + a2, 100)) + '}=' + dec(F(Math.round((100 + need) * 10), 1000))) + ' ⟹ 至少 ' + T(need + '\\%'),
             h: '平均成長率 $\\ge g$ ⟺ 三個倍率的乘積 $\\ge(1+g)^3$，把已知的兩個倍率除過去。',
             p: { kind: 1, a1: a1, a2: a2, g: g2, ans: need } };
  };
  /* 2-15 等差資料的統計量：μ、Me、P_k 與 σ²=d²(n²−1)/12（竹科實中 113 下 多 5、板橋 112 下 填 10 型） */
  L2.apStats = function (r) {
    var n = r.pick([10, 12, 15, 16, 20, 24, 25]), a1 = r.int(1, 9), d = r.pick([2, 3, 4, 5, 6]), data = [];
    for (var i = 0; i < n; i++) data.push(a1 + d * i);
    var k = r.pick([20, 25, 30, 40, 60, 70, 75, 80]), mu = meanF(data), pk = pctF(data, k), va = varF(data);
    return { q: '設等差資料 ' + T('X:\\ ' + a1 + ',\\ ' + (a1 + d) + ',\\ ' + (a1 + 2 * d) + ',\\ \\dots,\\ ' + data[n - 1]) + '（共 ' + T(String(n)) + ' 筆）。求 (1) 算術平均數與中位數　(2) 第 ' + T(String(k)) + ' 百分位數　(3) 變異數。',
             a: '(1) ' + T('\\mu=Me=\\dfrac{' + a1 + '+' + data[n - 1] + '}{2}=' + dec(mu)) + '　(2) ' + T('t=' + dec(tOf(n, k))) + ' ⟹ ' + T('P_{' + k + '}=' + dec(pk)) + '　(3) ' + T('\\sigma^2=\\dfrac{d^2(n^2-1)}{12}=\\dfrac{' + (d * d) + '(' + (n * n) + '-1)}{12}=' + dec(va)),
             h: '等差資料左右對稱 ⟹ $\\mu=Me=$ 首尾平均；$P_k$ 照 $t$ 的規則取；變異數有公式 $\\dfrac{d^2(n^2-1)}{12}$（把資料平移成 $0,d,2d,\\dots$ 再用 $\\sum k^2$ 推得）。',
             p: { n: n, a1: a1, d: d, k: k, ans: { mu: fr2(mu), pk: fr2(pk), var: fr2(va) } } };
  };
  /* 2-16 由「兩兩乘積和」與「平方和」求變異數（板橋 113 下 填 13 型） */
  L2.pairProdVar = function (r) {
    var xs, s;
    do { xs = []; for (var i = 0; i < 6; i++) xs.push(r.int(1, 9)); s = sumArr(xs); } while (s % 6 !== 0);
    var S2 = sumArr(xs.map(function (v) { return v * v; })), P = (s * s - S2) / 2, mu = s / 6, va = F(S2, 6); va = Fr.sub(va, F(mu * mu));
    return { q: '有六個正數，若任意兩數的乘積總和為 ' + T(String(P)) + '，且這六個數的平方和為 ' + T(String(S2)) + '。求這六個數的變異數。',
             a: T('\\left(\\sum x_i\\right)^2=' + S2 + '+2(' + P + ')=' + (s * s)) + ' ⟹ ' + T('\\sum x_i=' + s) + '、' + T('\\mu=' + mu) + '；' + T('\\sigma^2=\\dfrac{' + S2 + '}{6}-' + mu + '^2=' + dec(va)),
             h: '「和的平方」展開：$(\\sum x_i)^2=\\sum x_i^2+2\\sum_{i\\lt j}x_ix_j$，六個數都是正的所以總和取正根；再用 $\\sigma^2=\\frac{\\sum x^2}{n}-\\mu^2$。',
             p: { P: P, S2: S2, ans: fr2(va) } };
  };
  /* 2-17 T 分數的及格門檻（115 學測 A 9 型） */
  L2.tThreshold = function (r) {
    var mu = r.int(55, 70), s1 = r.pick([8, 10, 12, 15]), s2 = r.pick([4, 5, 6, 8]); if (s1 === s2) s1 += 4;
    var T0 = r.pick([35, 40, 45]), z0 = F(T0 - 50, 10), p1 = Fr.add(F(mu), Fr.mul(z0, F(s1))), p2 = Fr.add(F(mu), Fr.mul(z0, F(s2)));
    var st = mu + s2 * r.pick([-1, -2, 1]), Tst = Fr.add(F(50), Fr.mul(F(10), F(st - mu, s2)));
    return { q: T('T') + ' 分數定義為 ' + T('T=50+10\\cdot\\dfrac{S-\\mu}{\\sigma}') + '。某班數學與英文的平均皆為 ' + T(String(mu)) + ' 分，數學標準差 ' + T(String(s1)) + '、英文標準差 ' + T(String(s2)) + '。(1) 甲生英文考 ' + T(String(st)) + ' 分，求其英文 ' + T('T') + ' 分數。　(2) 若兩科及格標準皆為「' + T('T\\ge' + T0) + '」，求兩科各自的及格原始分數，並說明哪一科的門檻較低。',
             a: '(1) ' + T('T=' + dec(Tst)) + '　(2) ' + T('z\\ge' + dec(z0)) + ' ⟹ 數學 ' + T('S\\ge' + mu + '+(' + dec(z0) + ')(' + s1 + ')=' + dec(p1)) + '、英文 ' + T('S\\ge' + dec(p2)) + '；' + (Fr.lt(p1, p2) ? '數學' : '英文') + '的門檻較低，因為它的標準差較大（同樣的 $z$ 對應到離平均更遠的分數）',
             h: '$T\\ge' + T0 + '$ ⟺ $z\\ge' + dec(z0) + '$ ⟺ $S\\ge\\mu+(' + dec(z0) + ')\\sigma$：$\\sigma$ 越大，門檻被拉得越低。',
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
             h: '兩層加權：先算裡面那層（取較高的 $' + k + '$ 次平均），再列外層不等式解 $E$，非整數要無條件進位。',
             p: { quiz: quiz, k: k, s1: s1, s2: s2, target: target, ans: ans } };
  };

  /* ══════════════════════════════════════════════════════════ */
  var META = {
    L1: [
      ['centralTrio', '§1-1 平均數、中位數、眾數'], ['weightedMean', '§1-1 兩班合併的平均'], ['weightedScore', '§1-1 加權平均：至少要考幾分'], ['freqTable', '§1-1 次數分配表的平均與中位數'], ['meanShift', '§1-1 新增／剔除資料後的平均'],
      ['pctPosition', '§1-2 百分位數取第幾筆'], ['pctData', '§1-2 排序資料的百分位數'], ['pctFreq', '§1-2 「持 k 顆的有 k 位」的百分位數'],
      ['sdBasic', '§1-3 全距、變異數、標準差'], ['sdFromSums', '§1-3 由 Σx、Σx² 求標準差'], ['sumSqFromStats', '§1-3 由 μ、σ 求平方和'], ['addOne', '§1-3 新增一筆資料的影響'], ['mergeTwo', '§1-3 兩組資料合併'],
      ['linearTrans', '§1-4 線性變換 y=ax+b'], ['inverseTrans', '§1-4 由變換前後反推 a、b'], ['zCompare', '§1-4 標準化：跨科比較'], ['zInverse', '§1-4 z 分數與原始分數互換'], ['tScore', '§1-4 T 分數'],
      ['growthRate', '§1-5 平均成長率'], ['growthTotal', '§1-5 由首尾值求平均成長率'],
      ['corrData', '§2-1 由資料算相關係數'], ['corrSums', '§2-1 只給 Σ 的相關係數'], ['corrTransform', '§2-1 線性變換對 r 的影響'], ['corrPerfect', '§2-1 完全線性關係'],
      ['fitData', '§2-2 由資料求最適直線'], ['fitStats', '§2-2 由統計量求最適直線與預測'], ['fitCentroid', '§2-2 由最適直線反推 μ_y 與 r'], ['fitTransform', '§2-2 線性變換後的最適直線'], ['stdFit', '§2-2 標準化後的最適直線']
    ],
    L2: [
      ['regMissing', '§2 由迴歸直線反推缺失資料'], ['regReverse', '§2 由 r、直線反推 μ_x、σ_x'], ['regBothLines', '§2 兩條迴歸直線：交點與 r²'], ['regUnits', '§2 換單位後的迴歸直線'], ['corrFromSlope', '§2 由斜率反推 σ_y、μ_y'], ['addCentroid', '§2 新增重心那一筆'],
      ['minVarRange', '§1 固定全距的最小變異數'], ['sumSqShift', '§1 由 f(x)=Σ(x−x_i)² 反推 μ、σ'], ['reverseAdd', '§1 新增一筆後 σ 已知，反推那一筆'], ['mergeReverse', '§1 合併結果已知，反推 (x,y)'], ['linearReverse', '§1 把最高分最低分拉到指定值'], ['zRank', '§1 五科 z 分數排名'],
      ['pctFreqSquare', '§1 k² 位／k+1 次的百分位數'], ['growthMixed', '§1 成長率：金額漲幅、反推最後一年'], ['apStats', '§1 等差資料的 μ、P_k、σ²'], ['pairProdVar', '§1 兩兩乘積和求變異數'], ['tThreshold', '§1 T 分數的及格門檻'], ['weightedMin', '§1 兩層加權：期末至少幾分']
    ]
  };

  function escMath(s) {
    return String(s).replace(/\$([^$]*)\$/g, function (m, inner) {
      /* 原始 <>（瀏覽器會當標籤）、全形頓號（KaTeX 嚴格模式拒收）、\times 後接字母（變成未定義指令）一律在這裡修 */
      return '$' + inner.replace(/</g, '\\lt ').replace(/>/g, '\\gt ').replace(/、/g, ',\\ ').replace(/\\times(?=[A-Za-z])/g, '\\times ') + '$';
    });
  }
  function wrapAll(group) {
    Object.keys(group).forEach(function (k) {
      var f = group[k];
      group[k] = function (r) { var o = f(r); o.q = escMath(o.q); o.a = escMath(o.a); o.h = escMath(o.h); return o; };
    });
  }
  wrapAll(L1); wrapAll(L2);

  return { makeRng: makeRng, L1: L1, L2: L2, META: META, _util: { gcd: gcd, F: F, Fr: Fr, dec: dec, sqrtTex: sqrtTex, sqrtFracTex: sqrtFracTex } };
}));
