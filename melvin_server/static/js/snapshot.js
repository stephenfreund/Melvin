/* Snapshot: renders a store-JSON value
 *   { globals: {x: v, ...}, threads: {"1": {t: v, ...}}, objects: [...] }
 * as a DOM element.  Scalars become small tables; heap objects
 * ({id: "#1", class: "C", fields: {...}}) become Anchor-style box-and-arrow
 * diagrams, laid out with the vendored dagre and drawn in plain SVG.
 * Reference-valued fields are strings like "#2" (drawn as arrows) or "null".
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

  // Each diagram gets its own arrowhead marker id: url(#id) resolves against
  // the whole document, and a duplicate id inside a hidden subtree would make
  // every other diagram's arrowheads vanish.
  var markerSeq = 0;

  /* objects: heap boxes; refs: [{label, target}] — reference-valued variables
     drawn as labeled source nodes with an arrow to their object. */
  function objectDiagram(objects, refs) {
    refs = refs || [];
    var g = new dagre.graphlib.Graph();
    g.setGraph({ rankdir: "LR", nodesep: 24, ranksep: 40, marginx: 8, marginy: 8 });
    g.setDefaultEdgeLabel(function () { return {}; });

    var byId = {};
    objects.forEach(function (o) { byId[o.id] = o; });

    objects.forEach(function (o) {
      var fields = Object.keys(o.fields || {});
      var widest = objTitle(o).length;
      fields.forEach(function (f) {
        widest = Math.max(widest, (f + " = " + o.fields[f]).length);
      });
      g.setNode(o.id, {
        width: Math.max(90, widest * CHAR_W + 2 * PAD),
        height: TITLE_H + fields.length * ROW_H + PAD,
      });
    });
    refs.forEach(function (r) {
      g.setNode("$" + r.label, {
        width: r.label.length * CHAR_W + 3 * PAD,
        height: ROW_H + PAD,
      });
      g.setEdge("$" + r.label, r.target, {});
    });
    objects.forEach(function (o) {
      Object.keys(o.fields || {}).forEach(function (f) {
        var v = String(o.fields[f]);
        if (byId[v]) g.setEdge(o.id, v, { field: f });
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

    objects.forEach(function (o) {
      var n = g.node(o.id);
      var x = n.x - n.width / 2, y = n.y - n.height / 2;
      var grp = svgEl("g", {});
      grp.appendChild(svgEl("rect", {
        x: x, y: y, width: n.width, height: n.height, rx: 4, class: "snap-box",
      }));
      grp.appendChild(svgEl("rect", {
        x: x, y: y, width: n.width, height: TITLE_H, rx: 4, class: "snap-box-title-bg",
      }));
      var title = svgEl("text", {
        x: x + PAD, y: y + TITLE_H - 6, class: "snap-box-title",
      });
      title.textContent = objTitle(o);
      grp.appendChild(title);
      Object.keys(o.fields || {}).forEach(function (f, i) {
        var v = String(o.fields[f]);
        var row = svgEl("text", {
          x: x + PAD, y: y + TITLE_H + (i + 1) * ROW_H - 5, class: "snap-field",
        });
        row.textContent = byId[v] ? f + " •" : f + " = " + v;
        grp.appendChild(row);
      });
      svg.appendChild(grp);
    });

    refs.forEach(function (r) {
      var n = g.node("$" + r.label);
      var x = n.x - n.width / 2, y = n.y - n.height / 2;
      var grp = svgEl("g", {});
      grp.appendChild(svgEl("rect", {
        x: x, y: y, width: n.width, height: n.height,
        rx: n.height / 2, class: "snap-var-box",
      }));
      var t = svgEl("text", {
        x: x + n.width / 2, y: y + n.height / 2 + 4,
        "text-anchor": "middle", class: "snap-var",
      });
      t.textContent = r.label;
      grp.appendChild(t);
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
    var drawing = objects.length && typeof dagre !== "undefined";
    var byId = {};
    objects.forEach(function (o) { byId[o.id] = o; });
    // Reference-valued variables move from the tables into the diagram, as
    // labeled nodes with an arrow to their object.
    var refs = [];
    function splitRefs(kv, prefix) {
      if (!drawing) return kv;
      var rest = {};
      Object.keys(kv).forEach(function (k) {
        if (byId[String(kv[k])]) refs.push({ label: prefix + k, target: String(kv[k]) });
        else rest[k] = kv[k];
      });
      return rest;
    }
    var scalars = el("div", "snap-scalars");
    globals = splitRefs(globals, "");
    if (Object.keys(globals).length) scalars.appendChild(kvTable("globals", globals));
    var threads = (store && store.threads) || {};
    Object.keys(threads).sort().forEach(function (t) {
      var kv = splitRefs(threads[t], "t" + t + ".");
      if (Object.keys(kv).length)
        scalars.appendChild(kvTable("t" + t + " locals", kv));
    });
    if (scalars.childNodes.length) root.appendChild(scalars);
    if (drawing) {
      root.appendChild(objectDiagram(objects, refs));
    } else if (objects.length) {
      // dagre missing: fall back to tables
      objects.forEach(function (o) {
        root.appendChild(kvTable(objTitle(o), o.fields || {}));
      });
    }
    if (!root.childNodes.length ||
        (root.childNodes.length === 1 && opts.title)) {
      root.appendChild(el("div", "snap-empty", "(empty store)"));
    }
    return root;
  }

  return { render: render };
})();
