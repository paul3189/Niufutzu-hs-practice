/* 外站頁首「牛夫子錯題本」導流條（2026-11-24，T-261124-hs1；老師 11-24 圈選表乙 17）
 * 只在高中外站（精簡版 Niufutzu-hs-math、練習本 Niufutzu-hs-practice）由 build-mini.ps1／build-practice.ps1 加進頁面；
 * 錯題本裡的講義鏡像不會有這支。
 * 從錯題本連過來的人（wb-back.js 記的 sessionStorage wb.back）不顯示；按 × 收起後，這個分頁裡換頁都不再顯示。
 * 連結帶 ?from=hs_site，錯題本那邊可以看出是從高中外站來的。 */
(function () {
  "use strict";
  var URL = "https://wrongbook.niufutzu.com/?from=hs_site", KEY = "wb.promo.x";
  /* 網址與上一頁的判斷放在 try 外面：無痕視窗、App 內建瀏覽器擋 sessionStorage 時也要照判斷（R-1124-11，國中同步改） */
  if (/[?&]wb=/.test(location.search) || /^https:\/\/wrongbook\.niufutzu\.com\//.test(document.referrer || "")) return;
  try {
    if (sessionStorage.getItem("wb.back") || sessionStorage.getItem(KEY)) return;
  } catch (e) {}
  function add() {
    if (document.getElementById("wbPromo")) return;
    var bar = document.createElement("div");
    bar.id = "wbPromo";
    bar.setAttribute("style", "display:flex;align-items:center;gap:8px;background:#5c222b;color:#fff;" +
      "font:600 14px/1.45 'Noto Sans TC','Microsoft JhengHei',sans-serif;padding:7px 12px;position:relative;z-index:60");
    var a = document.createElement("a");
    a.href = URL;
    a.setAttribute("style", "color:#fff;text-decoration:none;flex:1;min-width:0;text-align:center");
    a.innerHTML = "<b>牛夫子錯題本</b>：拍照收錯題、五級模擬卷 <span style=\"text-decoration:underline\">去看看 →</span>";
    var x = document.createElement("button");
    x.type = "button"; x.setAttribute("aria-label", "收起"); x.textContent = "×";
    x.setAttribute("style", "flex:none;background:none;border:0;color:#fff;font:400 20px/1 sans-serif;padding:0 4px;cursor:pointer;opacity:.8");
    x.onclick = function () { try { sessionStorage.setItem(KEY, "1"); } catch (e) {} bar.remove(); };
    bar.appendChild(a); bar.appendChild(x);
    var st = document.createElement("style");
    st.textContent = "@media print{#wbPromo{display:none!important}}";
    bar.appendChild(st);
    document.body.insertBefore(bar, document.body.firstChild);
  }
  if (document.body) add(); else document.addEventListener("DOMContentLoaded", add);
})();
