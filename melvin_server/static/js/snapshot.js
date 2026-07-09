/* Snapshot: renders a store-JSON value
 *   { globals: {x: v, ...}, threads: {"1": [{fn, locals}, ...]}, objects: [...] }
 * as a DOM element.  Without heap objects, scalars render as small HTML
 * tables (a thread's call stack as stacked cards, innermost call on top).
 * With heap objects, the whole store becomes one Anchor-style box-and-arrow
 * diagram, laid out with the vendored dagre and drawn in plain SVG: a
 * globals box, one stack box per thread (one section per call frame,
 * innermost on top), and one box per heap object.  A reference-valued row
 * draws as "name •" with an arrow from its own box to the object.
 */
var Snapshot = (function () {
  "use strict";

  var ROW_H = 18, PAD = 6, CHAR_W = 7.2, TITLE_H = 20;

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text != null) e.textContent = text;
    return e;
  }

  function kvTable(title, kv) {
    var wrap = el("div", "snap-table");
    if (title) wrap.appendChild(el("div", "snap-table-title", title));
    var t = el("table");
    Object.keys(kv).forEach(function (k) {
      var tr = el("tr");
      tr.appendChild(el("td", "snap-k", k));
      tr.appendChild(el("td", "snap-v", String(kv[k])));
      t.appendChild(tr);
    });
    wrap.appendChild(t);
    return wrap;
  }

  function svgEl(tag, attrs) {
    var e = document.createElementNS("http://www.w3.org/2000/svg", tag);
    Object.keys(attrs || {}).forEach(function (k) { e.setAttribute(k, attrs[k]); });
    return e;
  }

  // Box/table heading for a heap object: "Counter  #1  (alloc t1)".
  // A `title` property overrides it (used for the identityless "this" box).
  function objTitle(o) {
    if (o.title) return o.title;
    var t = o.class + "  " + o.id;
    if (o.allocated_by != null) t += "  (alloc t" + o.allocated_by + ")";
    return t;
  }

  // Heading for one call frame in a thread's stack.
  function frameTitle(t, fr) {
    return "t" + t + ": " + fr.fn + (fr.fn === "thread" ? "" : "()");
  }

  // Each diagram gets its own arrowhead marker id: url(#id) resolves against
  // the whole document, and a duplicate id inside a hidden subtree would make
  // every other diagram's arrowheads vanish.
  var markerSeq = 0;

  /* Generic box-and-arrow drawing.  Each box is
   *   { id, kind: "obj" | "scope", sections: [{title, rows: [...]}] }
   * where a row is {label, value, ref}; a row whose `ref` names another box
   * draws as "label •" plus an arrow to that box. */
  function diagram(boxes) {
    var g = new dagre.graphlib.Graph({ multigraph: true });
    g.setGraph({ rankdir: "LR", nodesep: 24, ranksep: 40, marginx: 8, marginy: 8 });
    g.setDefaultEdgeLabel(function () { return {}; });

    var byId = {};
    boxes.forEach(function (b) { byId[b.id] = b; });

    function rowText(r) {
      return (r.ref != null && byId[r.ref]) ? r.label + " •"
                                            : r.label + " = " + r.value;
    }

    boxes.forEach(function (b) {
      var widest = 8, height = PAD;
      b.sections.forEach(function (s) {
        widest = Math.max(widest, s.title.length);
        height += TITLE_H + s.rows.length * ROW_H;
        s.rows.forEach(function (r) {
          widest = Math.max(widest, rowText(r).length);
        });
      });
      g.setNode(b.id, {
        width: Math.max(90, widest * CHAR_W + 2 * PAD),
        height: height,
      });
    });
    var eidx = 0;
    boxes.forEach(function (b) {
      b.sections.forEach(function (s) {
        s.rows.forEach(function (r) {
          if (r.ref != null && byId[r.ref])
            g.setEdge(b.id, r.ref, { field: r.label }, "e" + (eidx++));
        });
      });
    });

    dagre.layout(g);

    var gr = g.graph();
    var svg = svgEl("svg", {
      class: "snap-heap",
      width: Math.ceil(gr.width || 10), height: Math.ceil(gr.height || 10),
      viewBox: "0 0 " + Math.ceil(gr.width || 10) + " " + Math.ceil(gr.height || 10),
    });
    var arrowId = "snap-arrow-" + (++markerSeq);
    var defs = svgEl("defs", {});
    var marker = svgEl("marker", {
      id: arrowId, viewBox: "0 0 8 8", refX: 7, refY: 4,
      markerWidth: 7, markerHeight: 7, orient: "auto",
    });
    marker.appendChild(svgEl("path", { d: "M0,0 L8,4 L0,8 z", class: "snap-arrowhead" }));
    defs.appendChild(marker);
    svg.appendChild(defs);

    // edges under the boxes
    g.edges().forEach(function (e) {
      var pts = g.edge(e).points;
      var d = pts.map(function (p, i) {
        return (i === 0 ? "M" : "L") + p.x.toFixed(1) + "," + p.y.toFixed(1);
      }).join(" ");
      svg.appendChild(svgEl("path", {
        d: d, class: "snap-edge", "marker-end": "url(#" + arrowId + ")",
      }));
      var lbl = g.edge(e).field;
      if (lbl && pts.length) {
        var mid = pts[Math.floor(pts.length / 2)];
        var t = svgEl("text", { x: mid.x, y: mid.y - 3, class: "snap-edge-label" });
        t.textContent = lbl;
        svg.appendChild(t);
      }
    });

    boxes.forEach(function (b) {
      var n = g.node(b.id);
      var x = n.x - n.width / 2, y = n.y - n.height / 2;
      var scope = b.kind === "scope";
      var grp = svgEl("g", {});
      grp.appendChild(svgEl("rect", {
        x: x, y: y, width: n.width, height: n.height, rx: 4,
        class: scope ? "snap-box snap-scope" : "snap-box",
      }));
      var cy = y;
      b.sections.forEach(function (s, si) {
        grp.appendChild(svgEl("rect", {
          x: x, y: cy, width: n.width, height: TITLE_H, rx: si === 0 ? 4 : 0,
          class: scope ? "snap-box-title-bg snap-scope-title-bg"
                       : "snap-box-title-bg",
        }));
        var title = svgEl("text", {
          x: x + PAD, y: cy + TITLE_H - 6, class: "snap-box-title",
        });
        title.textContent = s.title;
        grp.appendChild(title);
        cy += TITLE_H;
        s.rows.forEach(function (r) {
          var row = svgEl("text", {
            x: x + PAD, y: cy + ROW_H - 5, class: "snap-field",
          });
          row.textContent = rowText(r);
          grp.appendChild(row);
          cy += ROW_H;
        });
      });
      svg.appendChild(grp);
    });
    return svg;
  }

  /* store: store-JSON; opts.title: optional heading */
  function render(store, opts) {
    opts = opts || {};
    var root = el("div", "snapshot");
    if (opts.title) root.appendChild(el("div", "snap-title", opts.title));
    var objects = ((store && store.objects) || []).slice();
    var globals = (store && store.globals) || {};
    // Receiver-relative facts ("this.f", from the hover schematic) have no
    // heap identity to hang a real diagram on; draw them as one "this" box
    // rather than rows in the globals table.
    var thisFields = null, plain = {};
    Object.keys(globals).forEach(function (k) {
      if (k.lastIndexOf("this.", 0) === 0) {
        (thisFields = thisFields || {})[k.slice(5)] = globals[k];
      } else {
        plain[k] = globals[k];
      }
    });
    globals = plain;
    if (thisFields)
      objects.push({ id: "this", class: "this", title: "this", fields: thisFields });
    var threads = (store && store.threads) || {};

    if (!(objects.length && typeof dagre !== "undefined")) {
      // no heap (or dagre missing): scalars as small HTML tables
      var scalars = el("div", "snap-scalars");
      if (Object.keys(globals).length)
        scalars.appendChild(kvTable("globals", globals));
      Object.keys(threads).sort().forEach(function (t) {
        var frames = threads[t];
        if (!Array.isArray(frames)) {           // legacy flat locals
          if (Object.keys(frames).length)
            scalars.appendChild(kvTable("t" + t + " locals", frames));
          return;
        }
        // a call stack: one table per frame, innermost call on top
        var stackEl = el("div", "snap-stack");
        for (var i = frames.length - 1; i >= 0; i--) {
          stackEl.appendChild(kvTable(frameTitle(t, frames[i]),
                                      frames[i].locals || {}));
        }
        if (frames.length) scalars.appendChild(stackEl);
      });
      if (scalars.childNodes.length) root.appendChild(scalars);
      objects.forEach(function (o) {   // dagre missing: fall back to tables
        root.appendChild(kvTable(objTitle(o), o.fields || {}));
      });
      if (!root.childNodes.length ||
          (root.childNodes.length === 1 && opts.title)) {
        root.appendChild(el("div", "snap-empty", "(empty store)"));
      }
      return root;
    }

    // heap present: one diagram holding globals, thread stacks, and objects
    var byId = {};
    objects.forEach(function (o) { byId[o.id] = o; });
    function rowsOf(kv) {
      return Object.keys(kv).map(function (k) {
        var v = String(kv[k]);
        return { label: k, value: v, ref: byId[v] ? v : null };
      });
    }
    var boxes = [];
    if (Object.keys(globals).length)
      boxes.push({ id: "@globals", kind: "scope",
                   sections: [{ title: "globals", rows: rowsOf(globals) }] });
    Object.keys(threads).sort().forEach(function (t) {
      var frames = threads[t];
      if (!Array.isArray(frames)) frames = [{ fn: "locals", locals: frames }];
      var sections = [];
      for (var i = frames.length - 1; i >= 0; i--) {   // innermost on top
        sections.push({ title: frameTitle(t, frames[i]),
                        rows: rowsOf(frames[i].locals || {}) });
      }
      if (sections.length)
        boxes.push({ id: "@t" + t, kind: "scope", sections: sections });
    });
    objects.forEach(function (o) {
      boxes.push({ id: o.id, kind: "obj",
                   sections: [{ title: objTitle(o), rows: rowsOf(o.fields || {}) }] });
    });
    root.appendChild(diagram(boxes));
    return root;
  }

  return { render: render };
})();
