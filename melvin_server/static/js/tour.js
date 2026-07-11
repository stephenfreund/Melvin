/* Guided tour of the Melvin demo, built on driver.js (vendored).
 *
 * The tour drives the app itself through window.MelvinApp (load examples,
 * verify, run, switch tabs); the user just presses Next.  Each step has an
 * async `prepare` that establishes the full app state it needs, so stepping
 * backward across a state boundary (e.g. from the broken program back to the
 * verified one) re-runs whatever is necessary — repeat verifies are served
 * from the demo server's cache.
 *
 * Entry points: the navbar Tour button, a #tour URL hash, and a one-time
 * first-visit toast (dismissal remembered in localStorage).
 */
(function () {
  "use strict";

  var App = window.MelvinApp;
  var driverFactory = window.driver && window.driver.js && window.driver.js.driver;
  if (!App || !driverFactory) return;

  var $ = function (sel) { return document.querySelector(sel); };
  var SEEN_KEY = "melvin-tour-seen";

  // What the *tour* has done so far; lets prepare() skip redundant work when
  // consecutive steps share state.  Any example load resets the flags.
  var state = { file: null, verified: false, ran: false };

  function ensureLoaded(name) {
    if (state.file === name) return Promise.resolve();
    return App.loadExample(name).then(function () {
      state.file = name;
      state.verified = false;
      state.ran = false;
    });
  }

  function ensureVerified(name) {
    return ensureLoaded(name).then(function () {
      if (state.verified) { App.selectTab("output"); return; }
      return App.verify().then(function () { state.verified = true; });
    });
  }

  function ensureRun(name) {
    return ensureLoaded(name).then(function () {
      if (state.ran) { App.selectTab("trace"); return; }
      return App.run().then(function () { state.ran = true; });
    });
  }

  // ------------------------------------------------- mover-chip helpers

  function chipForLine(pattern) {
    var ed = App.editor();
    for (var i = 0; i < ed.lineCount(); i++) {
      if (pattern.test(ed.getLine(i))) {
        var info = ed.lineInfo(i);
        var chip = info && info.gutterMarkers && info.gutterMarkers["melvin-movers"];
        if (chip) return chip;
      }
    }
    return null;
  }

  function hoverChip(pattern) {
    var chip = chipForLine(pattern);
    if (!chip) return;
    var ed = App.editor();
    for (var i = 0; i < ed.lineCount(); i++) {
      if (pattern.test(ed.getLine(i))) { ed.scrollIntoView({ line: i, ch: 0 }, 120); break; }
    }
    chip.dispatchEvent(new MouseEvent("mouseenter", { bubbles: true }));
  }

  function unhoverChips() {
    document.querySelectorAll(".mover-chip").forEach(function (c) {
      c.dispatchEvent(new MouseEvent("mouseleave", { bubbles: true }));
    });
  }

  function openExamplesMenu() {
    // just the dropdown, no flyout: the tour popover sits to its right,
    // where an open flyout would collide with it
    var menu = $("#menu-examples");
    if (menu) menu.classList.add("open");
  }

  function el(selectors) {
    // element resolver with fallbacks: first selector that matches wins
    return function () {
      for (var i = 0; i < selectors.length; i++) {
        var e = $(selectors[i]);
        if (e) return e;
      }
      return undefined;   // driver.js shows the popover as a centered modal
    };
  }

  // ------------------------------------------------------------- steps

  var STEPS = [
    {
      popover: {
        title: "Welcome to Melvin",
        description:
          "Melvin verifies concurrent programs with <b>Mover Logic</b> " +
          "(ECOOP&nbsp;2024): it proves code atomic by showing its actions " +
          "commute past other threads&rsquo;, then checks specifications " +
          "against that atomicity.<br><br>This two-minute tour verifies a " +
          "correct program, breaks it, and watches a real bug happen.",
      },
    },
    {
      element: "#editor-pane",
      prepare: function () { return ensureLoaded("counter.mml"); },
      popover: {
        title: "The paper's running example",
        side: "right",
        description:
          "A shared counter <code>x</code> protected by lock <code>m</code>. " +
          "The clause <code>both-mover if m == tid</code> is a <i>mover " +
          "specification</i>: accesses to <code>x</code> commute with other " +
          "threads&rsquo; steps whenever the accessing thread holds the lock.",
      },
    },
    {
      element: "#examples-menu",
      prepare: function () {
        return ensureLoaded("counter.mml").then(openExamplesMenu);
      },
      onLeave: function () { App.closeMenus(); },
      popover: {
        title: "Curated examples",
        side: "right",
        align: "start",
        description:
          "Synchronization idioms, heap objects and arrays, single-feature " +
          "programs &mdash; and deliberately broken ones, so you can see " +
          "what a rejection looks like.",
      },
    },
    {
      element: "#btn-verify",
      prepare: function () { return ensureLoaded("counter.mml"); },
      popover: {
        title: "Press Verify",
        side: "bottom",
        description:
          "<b>Verify</b> checks the whole program: mover-spec validity, " +
          "atomicity of <code>add()</code>, the client&rsquo;s " +
          "rely-guarantee. Each obligation becomes one Boogie procedure. " +
          "<br><br><b>Next</b> presses the button for you &mdash; watch " +
          "the status spinner in the file bar while the prover works.",
      },
    },
    {
      element: el(["#tab-output .result-banner", "#tab-output"]),
      prepare: function () { return ensureVerified("counter.mml"); },
      popover: {
        title: "Verified",
        side: "left",
        description:
          "The prover discharged every obligation. Because " +
          "<code>add()</code> is atomic, it earns the strong postcondition " +
          "<code>x == \\old(x) + n</code>, with no reasoning about " +
          "interleavings inside it.",
      },
    },
    {
      element: el([".mover-popup", "#editor-pane"]),
      prepare: function () {
        return ensureVerified("counter.mml").then(function () {
          hoverChip(/^\s*x = t;/);
        });
      },
      onLeave: unhoverChips,
      popover: {
        title: "Why each line moves",
        side: "bottom",
        description:
          "Every statement gets its mover letter in the gutter &mdash; " +
          "<b>B</b>oth, <b>R</b>ight, <b>L</b>eft, <b>N</b>on-mover, " +
          "<b>Y</b>ield. Hovering a chip shows <i>why</i>: which spec " +
          "clauses matched. This write to <code>x</code> is a both-mover " +
          "because the lock is held here. (After the tour, hover any chip.)",
      },
    },
    {
      element: "#tab-boogie",
      prepare: function () {
        return ensureVerified("counter.mml").then(function () {
          App.selectTab("boogie");
        });
      },
      popover: {
        title: "Under the hood: Boogie",
        side: "left",
        description:
          "The exact Boogie program the prover saw, one procedure per " +
          "obligation. Nothing is hidden &mdash; <b>Download .bpl</b> saves " +
          "it for a closer look.",
      },
    },
    {
      element: "#editor-pane",
      prepare: function () { return ensureLoaded("racy_bad.mml"); },
      popover: {
        title: "Now break it",
        side: "right",
        description:
          "The same counter, but <code>bad_add()</code> touches " +
          "<code>x</code> <i>without</i> holding the lock, so the access " +
          "no longer commutes with other threads. <b>Next</b> presses " +
          "<b>Verify</b> again.",
      },
    },
    {
      element: el(["#tab-output .result-banner", "#tab-output"]),
      prepare: function () { return ensureVerified("racy_bad.mml"); },
      popover: {
        title: "Rejected",
        side: "left",
        description:
          "The racing sequence is not reducible, so verification fails " +
          "&mdash; with the diagnostic pointing at the racing line (note " +
          "the squiggle in the editor).",
      },
    },
    {
      element: el(["#tab-output .diag-cex", "#tab-output .diag-list", "#tab-output"]),
      prepare: function () { return ensureVerified("racy_bad.mml"); },
      popover: {
        title: "Counterexamples",
        side: "left",
        description:
          "Each failed obligation carries a store decoded from the " +
          "prover&rsquo;s model: concrete values under which it fails. " +
          "Clicking a diagnostic jumps to the offending line.",
      },
    },
    {
      element: "#btn-run",
      prepare: function () { return ensureLoaded("obj_oracle_unsafe.mml"); },
      popover: {
        title: "Press Run",
        side: "bottom",
        description:
          "<b>Run</b> is independent of the verifier: a reference " +
          "interpreter that exhaustively explores <i>all</i> thread " +
          "interleavings. We&rsquo;ve loaded a program that publishes a " +
          "heap object with a race &mdash; <b>Next</b> presses the button.",
      },
    },
    {
      element: el(["#tab-trace .result-banner", "#tab-trace"]),
      prepare: function () { return ensureRun("obj_oracle_unsafe.mml"); },
      popover: {
        title: "Every interleaving, explored",
        side: "left",
        description:
          "Some interleaving reaches <code>wrong</code> &mdash; the " +
          "exhaustive search found it and kept one failing schedule.",
      },
    },
    {
      element: el(["#tab-trace .trace-wrap", "#tab-trace"]),
      prepare: function () { return ensureRun("obj_oracle_unsafe.mml"); },
      popover: {
        title: "Replay the failing interleaving",
        side: "left",
        description:
          "One failing schedule, step by step. Click any step to see the " +
          "store after it &mdash; heap objects draw as box-and-arrow " +
          "diagrams &mdash; and the editor follows along. Distinct final " +
          "states are listed below the trace.",
      },
    },
    {
      popover: {
        title: "Go explore",
        description:
          "Everything is editable: change a program and re-verify. " +
          "<b>Share</b> copies a permalink to your code, and the Mover " +
          "Logic paper and language reference are under <b>Docs</b>. Enjoy!",
      },
    },
  ];

  // ------------------------------------------------------------- driver

  var tour = null;
  var moving = false;   // an async prepare is in flight; ignore clicks

  function cleanupStep(i) {
    var s = STEPS[i];
    if (s && s.onLeave) s.onLeave();
  }

  function goTo(delta) {
    if (moving) return;
    var idx = tour.getActiveIndex();
    if (idx === undefined) return;
    var target = idx + delta;
    if (target < 0) return;
    if (target >= STEPS.length) { tour.destroy(); return; }
    moving = true;
    cleanupStep(idx);
    var prep = STEPS[target].prepare;
    Promise.resolve(prep ? prep() : null)
      .catch(function () {})    // a failed prepare still shows the step
      .then(function () {
        moving = false;
        if (delta > 0) tour.moveNext(); else tour.movePrevious();
      });
  }

  function startTour() {
    if (tour) tour.destroy();
    state = { file: null, verified: false, ran: false };
    dismissToast();
    tour = driverFactory({
      showProgress: true,
      progressText: "{{current}} of {{total}}",
      nextBtnText: "Next &rarr;",
      prevBtnText: "&larr; Back",
      doneBtnText: "Done",
      overlayOpacity: 0.6,
      stagePadding: 6,
      onNextClick: function () { goTo(+1); },
      onPrevClick: function () { goTo(-1); },
      onDestroyed: function () {
        unhoverChips();
        App.closeMenus();
        localStorage.setItem(SEEN_KEY, "1");
        tour = null;
      },
      steps: STEPS.map(function (s) {
        return { element: s.element, popover: s.popover };
      }),
    });
    tour.drive();
  }

  // ------------------------------------------------- first-visit toast

  var toast = null;

  function dismissToast() {
    if (toast) { toast.remove(); toast = null; }
  }

  function offerTour() {
    if (localStorage.getItem(SEEN_KEY)) return;
    if (location.hash && location.hash !== "#tour") return;  // deep link
    if (window.innerWidth <= 800) return;
    toast = document.createElement("div");
    toast.className = "tour-toast";
    var msg = document.createElement("div");
    msg.textContent = "New here? Take a two-minute guided tour of the demo.";
    var actions = document.createElement("div");
    actions.className = "tour-toast-actions";
    var start = document.createElement("button");
    start.className = "btn primary";
    start.textContent = "Take the tour";
    start.addEventListener("click", startTour);
    var later = document.createElement("button");
    later.className = "btn";
    later.textContent = "No thanks";
    later.addEventListener("click", function () {
      localStorage.setItem(SEEN_KEY, "1");
      dismissToast();
    });
    actions.appendChild(start);
    actions.appendChild(later);
    toast.appendChild(msg);
    toast.appendChild(actions);
    document.body.appendChild(toast);
  }

  // ------------------------------------------------------------- boot

  $("#btn-tour").addEventListener("click", startTour);

  if (location.hash === "#tour") {
    startTour();
  } else {
    offerTour();
  }
})();
