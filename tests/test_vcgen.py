"""Unit tests for moverlogic.vcgen (translation + lowering internals)."""

import pytest

from moverlogic.parser import parse, Parser
from moverlogic.lexer import lex
from moverlogic.types import check_types
from moverlogic.effects import Effect
from moverlogic.vcgen import Translator, Lowerer, lower_program
from moverlogic.diagnostics import TypeError_


def tr_of(text, cur=None, old=None):
    cur = cur or {"x": "v_x", "y": "v_y", "tid": "tid", "result": "v_result"}
    old = old or {"x": "o_x", "y": "o_y", "tid": "tid", "result": "o_result"}
    e = Parser(lex(text)).parse_expr()
    t = Translator(check_types(parse("var int x both-mover;")))
    return t.tr(e, cur, old)


# ------------------------------------------------------------ Translator

def test_translate_literals_and_specials():
    assert tr_of("42") == "42"
    assert tr_of("true") == "true"
    assert tr_of("false") == "false"
    assert tr_of("Nil") == "Nil"
    assert tr_of("None") == "None"
    assert tr_of("tid") == "tid"
    assert tr_of("result") == "v_result"


def test_translate_var_current_vs_old():
    assert tr_of("x") == "v_x"
    assert tr_of(r"\old(x)") == "o_x"


def test_translate_nested_old_is_idempotent():
    assert tr_of(r"\old(\old(x))") == "o_x"


def test_translate_arithmetic_and_div_mod():
    assert tr_of("x + 1") == "(v_x + 1)"
    assert tr_of("x / 2") == "(v_x div 2)"
    assert tr_of("x % 2") == "(v_x mod 2)"


def test_translate_logical_and_implies():
    assert tr_of("x ==> y") == "(v_x ==> v_y)"
    assert tr_of("x <==> y") == "(v_x <==> v_y)"


def test_translate_unary():
    assert tr_of("!x") == "(!v_x)"
    assert tr_of("-x") == "(-v_x)"


def test_translate_cons_and_calls():
    assert tr_of("x :: Nil") == "cons(v_x, Nil)"
    assert tr_of("head(y)") == "head(v_y)"
    assert tr_of("even(x)") == "even(v_x)"


def test_translate_index():
    cur = {"a": "v_a", "i": "v_i", "tid": "tid", "result": "v_result"}
    assert tr_of("a[i]", cur=cur, old=cur) == "v_a[v_i]"


def test_translate_quantifier():
    cur = {"tid": "tid", "N": "v_N", "a": "v_a", "result": "v_result"}
    out = tr_of("forall i in [0, N) . a[i] == 0", cur=cur, old=cur)
    assert out.startswith("(forall i: int ::")
    assert "0 <= i" in out and "i < v_N" in out
    out2 = tr_of("exists i in [0, N) . a[i] == tid", cur=cur, old=cur)
    assert out2.startswith("(exists i: int ::")


def test_unknown_function_is_recorded():
    t = Translator(check_types(parse("var int x both-mover;")))
    cur = {"x": "v_x", "tid": "tid", "result": "v_result"}
    e = Parser(lex("mypred(x)")).parse_expr()
    t.tr(e, cur, cur)
    assert t.unknown_funcs == {"mypred": 1}


def test_unbound_variable_raises():
    with pytest.raises(TypeError_):
        tr_of("zzz", cur={"tid": "tid", "result": "v_result"},
              old={"tid": "tid", "result": "o_result"})


# ------------------------------------------------- static effect helpers

def _lowerer(src):
    prog = parse(src)
    ti = check_types(prog)
    return Lowerer(prog, ti), prog


def test_mover_static_joins_clauses():
    low, _ = _lowerer(r"""
        lock m write right-mover if \old(m)==0 && m==tid
               write left-mover if \old(m)==tid && m==0;
    """)
    # join of R and L write clauses is N
    assert low._mover_static("m", "write") == Effect.N


def test_stmt_static_read_write_local():
    src = r"""
        var int x both-mover if m == tid;
        lock m write right-mover if \old(m)==0 && m==tid
               write left-mover if \old(m)==tid && m==0;
        atomic requires true ensures true f() { t = x; x = t; t = t + 1; }
    """
    low, prog = _lowerer(src)
    from moverlogic.vcgen import _Ctx
    ctx = _Ctx("fn:f", prog.find_func("f"), atomic=True)
    body = prog.find_func("f").body
    assert low._stmt_static(body[0], ctx) == Effect.B     # read of x (both-mover)
    assert low._stmt_static(body[1], ctx) == Effect.B     # write of x
    assert low._stmt_static(body[2], ctx) == Effect.B     # local


# ------------------------------------------------------- program lowering

def test_lower_program_emits_expected_procedures():
    src = r"""
        var int x both-mover if m == tid;
        lock m write right-mover if \old(m)==0 && m==tid
               write left-mover if \old(m)==tid && m==0;
        atomic requires true ensures m == \old(m) f() { acquire(m); release(m); }
    """
    prog = parse(src)
    em = lower_program(prog, check_types(prog))
    text = em.text()
    assert "procedure {:entrypoint} Def_f()" in text
    assert "function {:inline} seqEff" in text          # prelude present
    # validity procedures for all four conditions
    for cond in (1, 2, 4):
        assert f"Valid{cond}_" in text
    assert "Valid3_" in text
    assert em.obligations                                # at least one obligation


def test_lower_records_unknown_functions_in_header():
    src = "var int x both-mover if userpred(x);"
    prog = parse(src)
    em = lower_program(prog, check_types(prog))
    assert "function userpred(int) returns (bool);" in em.text()


def test_both_mover_loop_rejected_at_lowering():
    # A loop that is entirely both-movers violates left-mover termination.
    src = r"""
        var int x both-mover if m == tid;
        lock m write right-mover if \old(m)==0 && m==tid
               write left-mover if \old(m)==tid && m==0;
        atomic requires true ensures true f() {
            acquire(m);
            while (x < 3) invariant true { skip; }
            release(m);
        }
    """
    prog = parse(src)
    with pytest.raises(TypeError_) as exc:
        lower_program(prog, check_types(prog))
    assert "terminate" in str(exc.value)


def test_lower_nonatomic_call_path():
    # main_fn (non-atomic) calls helper (non-atomic): exercises M-call-non-atomic.
    src = r"""
        var int x both-mover if m == tid;
        lock m write right-mover if \old(m)==0 && m==tid
               write left-mover if \old(m)==tid && m==0;
        relies \old(x) <= x guarantees \old(x) <= x
        requires x >= 0 ensures x >= 0
        helper() { yield; }
        relies \old(x) <= x guarantees \old(x) <= x
        requires x >= 0 ensures x >= 0
        main_fn() { helper(); yield; }
    """
    prog = parse(src)
    em = lower_program(prog, check_types(prog))
    text = em.text()
    assert "procedure {:entrypoint} Def_helper()" in text
    assert "procedure {:entrypoint} Def_main_fn()" in text


def test_stmt_static_control_flow_and_call():
    src = r"""
        var int x both-mover if m == tid;
        lock m write right-mover if \old(m)==0 && m==tid
               write left-mover if \old(m)==tid && m==0;
        atomic requires true ensures true g() { skip; }
        atomic requires true ensures true f() {
            if (b) { t = x; } else { skip; }
            while (b) invariant true { skip; }
            g();
        }
    """
    low, prog = _lowerer(src)
    from moverlogic.vcgen import _Ctx
    ctx = _Ctx("fn:f", prog.find_func("f"), atomic=True)
    body = prog.find_func("f").body
    assert low._stmt_static(body[0], ctx) == Effect.B     # if: join(B, B)
    assert low._stmt_static(body[1], ctx) == Effect.B     # while over both-movers
    assert low._stmt_static(body[2], ctx) == Effect.N     # call to atomic g (default N)
