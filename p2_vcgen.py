"""
CS292C Homework 2 — Problem 2: Hoare Logic VCG for IMP (30 points)
===================================================================
Implement weakest-precondition-based verification condition generation
for a simple IMP language, using Z3 to discharge the VCs.

Part (a): Compute wp using your VCG and analyze preconditions with Z3.
          NOTE: Part (a) depends on Part (b). Implement Part (b) first, then come back to Part (a).
Part (b): Implement wp() and verify() below.
Part (c): Discover loop invariants for three programs.
Part (d): Find and fix a bug in a provided invariant.
"""

from z3 import *
from dataclasses import dataclass
from typing import Union

# ============================================================================
# IMP Abstract Syntax Tree
# ============================================================================

@dataclass
class IntConst:
    value: int

@dataclass
class Var:
    name: str

@dataclass
class BinOp:
    """op ∈ {'+', '-', '*'}"""
    op: str
    left: 'AExp'
    right: 'AExp'

AExp = Union[IntConst, Var, BinOp]

@dataclass
class BoolConst:
    value: bool

@dataclass
class Compare:
    """op ∈ {'<', '<=', '>', '>=', '==', '!='}"""
    op: str
    left: AExp
    right: AExp

@dataclass
class ImpNot:
    expr: 'BExp'

@dataclass
class ImpAnd:
    left: 'BExp'
    right: 'BExp'

@dataclass
class ImpOr:
    left: 'BExp'
    right: 'BExp'

BExp = Union[BoolConst, Compare, ImpNot, ImpAnd, ImpOr]

@dataclass
class Assign:
    var: str
    expr: AExp

@dataclass
class Seq:
    s1: 'Stmt'
    s2: 'Stmt'

@dataclass
class If:
    cond: BExp
    then_branch: 'Stmt'
    else_branch: 'Stmt'

@dataclass
class While:
    cond: BExp
    invariant: 'BExp'
    body: 'Stmt'

@dataclass
class Assert:
    cond: BExp

@dataclass
class Assume:
    cond: BExp

Stmt = Union[Assign, Seq, If, While, Assert, Assume]

# ============================================================================
# IMP AST → Z3 Translation
# ============================================================================

_z3_vars: dict[str, ArithRef] = {}

def z3_var(name: str) -> ArithRef:
    if name not in _z3_vars:
        _z3_vars[name] = Int(name)
    return _z3_vars[name]

def aexp_to_z3(e: AExp) -> ArithRef:
    match e:
        case IntConst(v):   return IntVal(v)
        case Var(name):     return z3_var(name)
        case BinOp('+', l, r): return aexp_to_z3(l) + aexp_to_z3(r)
        case BinOp('-', l, r): return aexp_to_z3(l) - aexp_to_z3(r)
        case BinOp('*', l, r): return aexp_to_z3(l) * aexp_to_z3(r)
        case _: raise ValueError(f"Unknown AExp: {e}")

def bexp_to_z3(e: BExp) -> BoolRef:
    match e:
        case BoolConst(v):   return BoolVal(v)
        case Compare(op, l, r):
            lz, rz = aexp_to_z3(l), aexp_to_z3(r)
            return {'<': lz < rz, '<=': lz <= rz, '>': lz > rz,
                    '>=': lz >= rz, '==': lz == rz, '!=': lz != rz}[op]
        case ImpNot(inner):  return z3.Not(bexp_to_z3(inner))
        case ImpAnd(l, r):   return z3.And(bexp_to_z3(l), bexp_to_z3(r))
        case ImpOr(l, r):    return z3.Or(bexp_to_z3(l), bexp_to_z3(r))
        case _: raise ValueError(f"Unknown BExp: {e}")

def z3_substitute_var(formula: ExprRef, var_name: str, replacement: ArithRef) -> ExprRef:
    """Replace every occurrence of z3 variable `var_name` with `replacement`."""
    return substitute(formula, (z3_var(var_name), replacement))


# ============================================================================
# Part (b): Weakest Precondition + VCG — 12 pts
# ============================================================================

side_vcs: list[tuple[str, BoolRef]] = []

def wp(stmt: Stmt, Q: BoolRef) -> BoolRef:
    """
    Compute the weakest precondition of `stmt` w.r.t. postcondition `Q`.
    For while loops, append side VCs to the global `side_vcs` list.
    """
    global side_vcs

    match stmt:
        case Assign(var, expr):
            # Q[var ↦ expr]: substitute the z3 variable for `var` with the
            # z3 translation of `expr` everywhere in Q.
            return z3_substitute_var(Q, var, aexp_to_z3(expr))

        case Seq(s1, s2):
            # wp(s1; s2, Q) = wp(s1, wp(s2, Q))
            return wp(s1, wp(s2, Q))

        case If(cond, s1, s2):
            # wp(if b then s1 else s2, Q) = (b → wp(s1,Q)) ∧ (¬b → wp(s2,Q))
            b = bexp_to_z3(cond)
            return And(Implies(b, wp(s1, Q)),
                       Implies(Not(b), wp(s2, Q)))

        case While(cond, inv, body):
            # The wp of a loop is its invariant. We additionally emit two side
            # verification conditions that the invariant is preserved by the
            # body and is strong enough to imply the postcondition on exit.
            b = bexp_to_z3(cond)
            I = bexp_to_z3(inv)
            # Preservation: I ∧ b → wp(body, I)
            wp_body_I = wp(body, I)
            side_vcs.append(("preservation", Implies(And(I, b), wp_body_I)))
            # Exit/postcondition: I ∧ ¬b → Q
            side_vcs.append(("postcondition", Implies(And(I, Not(b)), Q)))
            return I

        case Assert(cond):
            # wp(assert P, Q) = P ∧ Q   — P must hold AND Q must follow.
            return And(bexp_to_z3(cond), Q)

        case Assume(cond):
            # wp(assume P, Q) = P → Q   — only worry about Q when P holds.
            return Implies(bexp_to_z3(cond), Q)

        case _:
            raise ValueError(f"Unknown statement: {stmt}")


def _is_valid(formula: BoolRef) -> tuple[bool, object]:
    """Return (valid?, model_or_None). A formula is valid iff its negation is UNSAT."""
    s = Solver()
    s.add(Not(formula))
    r = s.check()
    if r == unsat:
        return True, None
    if r == sat:
        return False, s.model()
    return False, None  # unknown


def verify(pre: BExp, stmt: Stmt, post: BExp, label: str = "Program"):
    """
    Verify the Hoare triple {pre} stmt {post}.
    1. Clear side_vcs.  2. Compute wp.  3. Check pre → wp is valid.
    4. Check each side VC.  5. Print results.
    """
    global side_vcs
    side_vcs = []

    pre_z3 = bexp_to_z3(pre)
    post_z3 = bexp_to_z3(post)

    wp_result = wp(stmt, post_z3)

    print(f"=== {label} ===")
    all_ok = True

    # Entry VC: pre → wp(stmt, post)
    entry_vc = Implies(pre_z3, wp_result)
    valid, model = _is_valid(entry_vc)
    print(f"  entry        : {'OK' if valid else 'FAIL'}")
    if not valid:
        all_ok = False
        if model is not None:
            print(f"    counterexample: {model}")

    # Side VCs (one or more per while loop)
    for name, vc in side_vcs:
        valid, model = _is_valid(vc)
        print(f"  {name:13s}: {'OK' if valid else 'FAIL'}")
        if not valid:
            all_ok = False
            if model is not None:
                print(f"    counterexample: {model}")

    print(f"  ==> {'Verified' if all_ok else 'NOT verified'}")
    print()
    return all_ok


# ============================================================================
# Test Programs for Part (b) — verify your VCG works on these
# ============================================================================

def test_swap():
    """{ x == a ∧ y == b }  t:=x; x:=y; y:=t  { x == b ∧ y == a }"""
    pre = ImpAnd(Compare('==', Var('x'), Var('a')),
                 Compare('==', Var('y'), Var('b')))
    stmt = Seq(Assign('t', Var('x')),
               Seq(Assign('x', Var('y')), Assign('y', Var('t'))))
    post = ImpAnd(Compare('==', Var('x'), Var('b')),
                  Compare('==', Var('y'), Var('a')))
    verify(pre, stmt, post, "Swap")


def test_abs():
    """{ true }  if x<0 then r:=0-x else r:=x  { r >= 0 ∧ (r==x ∨ r==0-x) }"""
    pre = BoolConst(True)
    stmt = If(Compare('<', Var('x'), IntConst(0)),
              Assign('r', BinOp('-', IntConst(0), Var('x'))),
              Assign('r', Var('x')))
    post = ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                  ImpOr(Compare('==', Var('r'), Var('x')),
                        Compare('==', Var('r'), BinOp('-', IntConst(0), Var('x')))))
    verify(pre, stmt, post, "Absolute Value")


# ============================================================================
# Part (c): Invariant Discovery — 8 pts
# ============================================================================

def test_mult():
    """
    Program C1 — Multiplication by addition:
      { a >= 0 }
      i := 0; r := 0;
      while i < a  invariant ???  do
        r := r + b;  i := i + 1;
      { r == a * b }

    [EXPLAIN] How I found this invariant: the loop body increments i by one
    and adds b to r each iteration, so after k iterations we have i = k and
    r = k*b. The relationship r == i*b is therefore invariant. To make it
    strong enough to imply the postcondition on exit, I additionally need the
    bounds 0 <= i <= a — the upper bound combined with ¬(i < a) at exit gives
    i == a, which together with r == i*b yields r == a*b.
    """
    pre = Compare('>=', Var('a'), IntConst(0))

    # Invariant: r == i*b ∧ 0 <= i ∧ i <= a
    inv = ImpAnd(
        Compare('==', Var('r'), BinOp('*', Var('i'), Var('b'))),
        ImpAnd(
            Compare('>=', Var('i'), IntConst(0)),
            Compare('<=', Var('i'), Var('a')),
        ),
    )

    body = Seq(Assign('r', BinOp('+', Var('r'), Var('b'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', IntConst(0)),
                   While(Compare('<', Var('i'), Var('a')), inv, body)))
    post = Compare('==', Var('r'), BinOp('*', Var('a'), Var('b')))
    verify(pre, stmt, post, "C1: Multiplication by Addition")


def test_add():
    """
    Program C2 — Addition by loop:
      { n >= 0 ∧ m >= 0 }
      i := 0; r := n;
      while i < m  invariant ???  do
        r := r + 1;  i := i + 1;
      { r == n + m }

    [EXPLAIN] How I found this invariant: each iteration adds 1 to both r and
    i, and r starts at n while i starts at 0, so r - n always equals i, i.e.
    r == n + i. To imply r == n + m on exit I also need the loop bounds
    0 <= i <= m so that ¬(i < m) at exit forces i == m.
    """
    pre = ImpAnd(Compare('>=', Var('n'), IntConst(0)),
                 Compare('>=', Var('m'), IntConst(0)))

    # Invariant: r == n + i ∧ 0 <= i ∧ i <= m
    inv = ImpAnd(
        Compare('==', Var('r'), BinOp('+', Var('n'), Var('i'))),
        ImpAnd(
            Compare('>=', Var('i'), IntConst(0)),
            Compare('<=', Var('i'), Var('m')),
        ),
    )

    body = Seq(Assign('r', BinOp('+', Var('r'), IntConst(1))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', Var('n')),
                   While(Compare('<', Var('i'), Var('m')), inv, body)))
    post = Compare('==', Var('r'), BinOp('+', Var('n'), Var('m')))
    verify(pre, stmt, post, "C2: Addition by Loop")


def test_sum():
    """
    Program C3 — Sum of 1..n:
      { n >= 1 }
      i := 1; s := 0;
      while i <= n  invariant ???  do
        s := s + i;  i := i + 1;
      { 2 * s == n * (n + 1) }

    [EXPLAIN] How I found this invariant: at the head of the loop, s holds
    1 + 2 + ... + (i-1) = (i-1)*i/2, so 2*s == (i-1)*i is a polynomial
    equality that avoids division. I verified preservation by hand:
    2*(s+i) = (i-1)i + 2i = i^2 + i = i(i+1) = ((i+1)-1)(i+1). The bounds
    1 <= i <= n+1 are needed so that ¬(i <= n) at exit gives i == n+1, which
    plugs into 2*s == (i-1)*i to yield 2*s == n*(n+1).
    """
    pre = Compare('>=', Var('n'), IntConst(1))

    # Invariant: 2*s == (i-1)*i ∧ 1 <= i ∧ i <= n+1
    inv = ImpAnd(
        Compare('==',
                BinOp('*', IntConst(2), Var('s')),
                BinOp('*', BinOp('-', Var('i'), IntConst(1)), Var('i'))),
        ImpAnd(
            Compare('>=', Var('i'), IntConst(1)),
            Compare('<=', Var('i'), BinOp('+', Var('n'), IntConst(1))),
        ),
    )

    body = Seq(Assign('s', BinOp('+', Var('s'), Var('i'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(1)),
               Seq(Assign('s', IntConst(0)),
                   While(Compare('<=', Var('i'), Var('n')), inv, body)))
    post = Compare('==', BinOp('*', IntConst(2), Var('s')),
                   BinOp('*', Var('n'), BinOp('+', Var('n'), IntConst(1))))
    verify(pre, stmt, post, "C3: Sum of 1..n")


# ============================================================================
# Part (d): Find the Bug — 4 pts
# ============================================================================

def test_buggy_div():
    """
    Integer division with a BUGGY invariant.
      { x >= 0 ∧ y > 0 }
      q := 0; r := x;
      while r >= y  invariant (q * y + r == x)  do    ← TOO WEAK!
        r := r - y;  q := q + 1;
      { q * y + r == x ∧ 0 <= r ∧ r < y }

    [EXPLAIN] Which side VC fails and why?
      The POSTCONDITION VC fails. The buggy invariant only asserts the
      arithmetic identity q*y + r == x; it says nothing about the sign of r
      or that y is positive. On loop exit we know ¬(r >= y), i.e. r < y,
      and we still know q*y + r == x — but the postcondition demands r >= 0
      as well, which the invariant alone does not entail.

      Concrete state where the invariant holds but the postcondition does
      not:  q = 0, y = 5, r = -1, x = -1.  Here q*y + r = 0 + (-1) = -1 = x
      (invariant ✓) and r < y (loop exited), but r = -1 < 0, so the
      postcondition r >= 0 fails.

      Note: preservation actually still holds for the weak invariant —
      assuming r >= y, the body produces q' = q+1, r' = r - y, and
      q'*y + r' = q*y + y + r - y = q*y + r = x. The bug is that the
      invariant fails to track enough state to prove the EXIT condition.

      FIX: Add the missing conjuncts r >= 0 and y > 0. r >= 0 directly
      gives the missing postcondition conjunct; y > 0 is needed so that
      preservation of r >= 0 goes through (r' = r - y is non-negative when
      r >= y AND y > 0).
    """
    pre = ImpAnd(Compare('>=', Var('x'), IntConst(0)),
                 Compare('>', Var('y'), IntConst(0)))

    # BUGGY invariant — intentionally too weak
    inv_buggy = Compare('==',
        BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
        Var('x'))

    body = Seq(Assign('r', BinOp('-', Var('r'), Var('y'))),
               Assign('q', BinOp('+', Var('q'), IntConst(1))))
    stmt_buggy = Seq(Assign('q', IntConst(0)),
                     Seq(Assign('r', Var('x')),
                         While(Compare('>=', Var('r'), Var('y')),
                               inv_buggy, body)))
    post = ImpAnd(Compare('==',
                       BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
                       Var('x')),
                  ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                         Compare('<', Var('r'), Var('y'))))

    verify(pre, stmt_buggy, post, "Buggy Division (should FAIL)")

    # ----- FIXED invariant -----
    # I = (q*y + r == x) ∧ (r >= 0) ∧ (y > 0)
    inv_fixed = ImpAnd(
        Compare('==',
                BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
                Var('x')),
        ImpAnd(
            Compare('>=', Var('r'), IntConst(0)),
            Compare('>', Var('y'), IntConst(0)),
        ),
    )
    stmt_fixed = Seq(Assign('q', IntConst(0)),
                     Seq(Assign('r', Var('x')),
                         While(Compare('>=', Var('r'), Var('y')),
                               inv_fixed, body)))
    ok = verify(pre, stmt_fixed, post, "Fixed Division")
    if ok:
        print("FIXED: Verified")
        print()


# ============================================================================
# Part (a): WP Derivation via Z3 — 6 pts
# ============================================================================

def test_wp_derivation():
    """
    Part (a): Use your VCG to compute wp, then check candidate preconditions.

      x := x + 1;
      if x > 0 then y := x * 2 else y := 0 - x;
      { y > 0 }
    """
    print("=== Part (a): WP Derivation ===")

    # Build the IMP AST.
    stmt = Seq(
        Assign('x', BinOp('+', Var('x'), IntConst(1))),
        If(Compare('>', Var('x'), IntConst(0)),
           Assign('y', BinOp('*', Var('x'), IntConst(2))),
           Assign('y', BinOp('-', IntConst(0), Var('x'))))
    )
    post = Compare('>', Var('y'), IntConst(0))
    post_z3 = bexp_to_z3(post)

    # Reset side_vcs (no loops here, but keep state clean).
    global side_vcs
    side_vcs = []

    wp_result = wp(stmt, post_z3)
    print(f"  wp = {wp_result}")
    print(f"  wp (simplified) = {simplify(wp_result)}")

    # Mathematically: after x := x+1 and case-split on x' > 0:
    #   if x' > 0:  need x'*2 > 0  ⟺  x' > 0          (always true here)
    #   else:       need (0 - x') > 0  ⟺  x' < 0
    # So wp[x'/x+1] = (x+1 > 0) ∨ (x+1 < 0) = (x >= 0) ∨ (x <= -2) = x ≠ -1.

    candidates = [
        ("x >= 0",  z3_var('x') >= 0),
        ("x >= -1", z3_var('x') >= -1),
        ("x == -1", z3_var('x') == -1),
    ]
    for name, pre in candidates:
        s = Solver()
        s.add(Not(Implies(pre, wp_result)))
        result = s.check()
        valid = (result == unsat)
        if valid:
            print(f"  {name}: VALID precondition")
        else:
            m = s.model()
            print(f"  {name}: INVALID precondition — counterexample: {m}")

    # [EXPLAIN] precondition results:
    # • {x >= 0}  is VALID. Then x' = x+1 >= 1 > 0, so we take the 'then'
    #   branch and y = 2*x' >= 2 > 0. Postcondition holds.
    # • {x >= -1} is INVALID. The single value x = -1 satisfies the precondition
    #   but produces x' = 0; the 'then' branch is NOT taken (x' > 0 is false),
    #   we go to 'else' and y = 0 - 0 = 0, which violates y > 0. Z3 returns
    #   x = -1 as the counterexample.
    # • {x == -1} is INVALID and is in fact the WORST possible precondition:
    #   it forces exactly the bad case above. The wp itself is x ≠ -1, so any
    #   precondition that admits x = -1 is unsound; one that forces x = -1 is
    #   maximally unsound.
    print()


# ============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("Part (b): VCG Correctness Tests")
    print("=" * 60)
    test_swap()
    test_abs()

    print("=" * 60)
    print("Part (a): WP Derivation via Z3")
    print("=" * 60)
    test_wp_derivation()

    print("=" * 60)
    print("Part (c): Invariant Discovery")
    print("=" * 60)
    test_mult()
    test_add()
    test_sum()

    print("=" * 60)
    print("Part (d): Find the Bug")
    print("=" * 60)
    test_buggy_div()
