/* CodeMirror mode for the Mover Logic Language (MLL).
 * Token classes follow melvin/lexer.py KEYWORDS; hyphenated movers
 * (both-mover etc.) are matched as single keywords. */
(function () {
  "use strict";

  var KEYWORDS = new Set([
    "var", "lock", "thread", "func", "init", "invariant",
    "atomic", "relies", "guarantees", "requires", "ensures",
    "read", "write",
    "both-mover", "right-mover", "left-mover", "non-mover",
    "if", "else", "while", "skip", "yield", "wrong", "assert",
    "forall", "exists", "in",
  ]);
  var TYPES = new Set(["int", "bool", "lock_t", "value"]);
  var ATOMS = new Set(["true", "false", "Nil", "None", "Some", "tid", "result"]);
  var BUILTINS = new Set(["acquire", "release", "cas", "head", "tail", "even"]);

  CodeMirror.defineMode("mml", function () {
    return {
      token: function (stream) {
        if (stream.match("//")) { stream.skipToEnd(); return "comment"; }
        if (stream.match(/^\\old\b/)) return "keyword";
        if (stream.match(/^[0-9]+/)) return "number";
        if (stream.match(/^[A-Za-z_][A-Za-z0-9_]*(?:-mover)?/)) {
          var w = stream.current();
          if (KEYWORDS.has(w)) return "keyword";
          if (TYPES.has(w)) return "type";
          if (ATOMS.has(w)) return "atom";
          if (BUILTINS.has(w)) return "builtin";
          return "variable";
        }
        if (stream.match(/^(==>|<==>|&&|\|\||==|!=|<=|>=|::|->)/)) return "operator";
        stream.next();
        return null;
      },
      lineComment: "//",
    };
  });

  CodeMirror.defineMIME("text/x-mml", "mml");
})();
