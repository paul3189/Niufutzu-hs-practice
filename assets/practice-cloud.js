/* 分級練習本 — 雲端同步（2026-09-24 起）
 *
 * 練習本的紀錄本來只存在該裝置的 localStorage（pgen_rec_<章>）。這個檔在頁面載入 assets/reflex-cloud.js 之後掛上去：
 *   1. 攔截 localStorage 對 pgen_rec_<章> 的寫入 → 登入時去抖動上傳（practiceSave）
 *   2. 登入後把雲端那份拿下來比對：雲端較新（或本機沒有）就覆蓋本機並重新載入一次頁面；本機較新就上傳
 *   3. 在「📊 我的練習紀錄」面板前面放一個小的帳號區（Email 連結登入／登出／狀態）
 * 頁面自己的腳本一行都不用改；沒有 reflex-cloud.js 或雲端未設定時，這個檔什麼都不做。
 */
(function () {
  "use strict";
  var C = window.ReflexCloud;
  if (!C) return;
  var m = (location.pathname.match(/(g\d\d[ab]-ch\d\d)/) || [])[1];   /* handouts/<章>/practice.html */
  if (!m) return;
  var CH = m, KEY = "pgen_rec_" + CH, FLAG = "hsmath.practice.synced." + CH;
  var on = false, timer = null, lastUp = "";

  function $(id) { return document.getElementById(id); }
  function esc(s) { return String(s == null ? "" : s).replace(/&/g, "&amp;").replace(/</g, "&lt;"); }
  function localRec() { try { return JSON.parse(localStorage.getItem(KEY) || "null"); } catch (e) { return null; } }
  function localTs() { try { return +localStorage.getItem(KEY + ".ts") || 0; } catch (e) { return 0; } }
  function stampLocal(ts) { try { localStorage.setItem(KEY + ".ts", String(ts)); } catch (e) {} }
  function attemptsOf(r) { return (r && r.attempts && r.attempts.length) || 0; }

  /* 1. 攔截寫入：頁面每次 saveRec() 都會 setItem(KEY, …) */
  var origSet = localStorage.setItem.bind(localStorage);
  localStorage.setItem = function (k, v) {
    origSet(k, v);
    if (k !== KEY) return;
    var now = Date.now(); stampLocal(now);
    if (!on || !C.user()) return;
    clearTimeout(timer);
    timer = setTimeout(function () {
      if (v === lastUp) return;
      C.practiceSave(CH, JSON.parse(v)).then(function () { lastUp = v; setStatus("☁️ 已同步 " + new Date().toLocaleTimeString()); })
        .catch(function (e) { setStatus("⚠ 上傳失敗：" + esc(e && e.message)); });
    }, 1500);
  };

  /* 2. 登入後合併 */
  function reconcile() {
    if (!C.user()) return;
    C.practiceLoad(CH).then(function (cloud) {
      var loc = localRec(), lts = localTs();
      if (!cloud || !cloud.rec) {
        if (loc && attemptsOf(loc)) return C.practiceSave(CH, loc).then(function () { setStatus("☁️ 已把這台裝置的紀錄上傳"); });
        setStatus("☁️ 已登入，紀錄會自動同步");
        return;
      }
      var cloudNewer = cloud.ts > lts || !loc || (attemptsOf(cloud.rec) > attemptsOf(loc));
      if (cloudNewer && JSON.stringify(cloud.rec) !== JSON.stringify(loc)) {
        /* 只在這一頁載入後還沒同步過時才重新載入，避免無限重載 */
        if (sessionStorage.getItem(FLAG)) { setStatus("☁️ 雲端有較新的紀錄，重新整理後套用"); return; }
        origSet(KEY, JSON.stringify(cloud.rec)); stampLocal(cloud.ts || Date.now());
        sessionStorage.setItem(FLAG, "1");
        location.reload();
        return;
      }
      if (!cloudNewer && loc) return C.practiceSave(CH, loc).then(function () { setStatus("☁️ 已同步"); });
      setStatus("☁️ 已同步");
    }).catch(function (e) { setStatus("⚠ 讀取雲端失敗：" + esc(e && e.message)); });
  }

  /* 3. 帳號區 */
  var box = null;
  function setStatus(t) { var s = box && box.querySelector(".pc-status"); if (s) s.innerHTML = t; }
  function render() {
    if (!box) {
      var anchor = $("myrec") || document.querySelector(".howto") || document.body.firstElementChild;
      box = document.createElement("div");
      box.className = "pc-cloud";
      box.style.cssText = "margin:14px 0;padding:12px 14px;border:1px solid #cbd5e1;border-radius:12px;background:#f8fafc;font-size:.92rem;line-height:1.7";
      anchor.parentNode.insertBefore(box, anchor);
    }
    var u = C.user();
    if (u) {
      box.innerHTML = '<b>☁️ 練習紀錄同步</b>　' + esc(u.email) + '（' + esc(C.nick() || "") + '）' +
        '<button type="button" class="pc-out" style="margin-left:8px">登出</button>' +
        '<div class="pc-status" style="color:#155e75"></div>' +
        '<div style="color:#64748b;font-size:.85rem">登入後這一章的檢測、錯題本、精熟進度會存到你的帳號，換裝置也看得到；老師也能在後台看到你的進度。</div>';
      box.querySelector(".pc-out").onclick = function () { C.signOut(); };
      reconcile();
    } else {
      box.innerHTML = '<b>☁️ 練習紀錄同步</b>　目前只存在這台裝置。用 Email 登入後會跨裝置同步，老師也看得到你的進度。' +
        '<div style="margin-top:6px"><input type="email" class="pc-email" placeholder="你的 Email" value="' + esc(C.rememberedEmail()) + '" style="padding:4px 8px;border:1px solid #cbd5e1;border-radius:8px;width:220px;max-width:60%">' +
        '<button type="button" class="pc-send" style="margin-left:6px">寄登入連結</button></div>' +
        '<div class="pc-status" style="color:#155e75"></div>';
      box.querySelector(".pc-send").onclick = function () {
        var em = box.querySelector(".pc-email").value.trim();
        if (!C.validEmail(em)) { setStatus("請輸入正確的 Email"); return; }
        setStatus("寄送中…");
        C.sendLink(em).then(function () { setStatus("✉️ 已寄出，打開信裡的連結就會登入（同一台裝置）。"); })
          .catch(function (e) { setStatus("⚠ 寄送失敗：" + esc(e && e.message)); });
      };
    }
  }

  C.ready.then(function (ok) {
    if (!ok) return;
    on = true;
    return C.finishLink().then(function (r) {
      if (r === "need-email") {
        var em = prompt("請輸入你申請登入連結時用的 Email：");
        if (em) return C.finishLink(em);
      }
    }).catch(function (e) { if (window.console) console.warn("[practice-cloud] 登入連結處理失敗", e); })
    .then(function () { C.onAuth(render); });
  });
})();
