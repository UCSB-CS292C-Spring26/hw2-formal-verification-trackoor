"""
CS292C Homework 2 — Problem 1: Z3 Warm-Up + EUF Puzzle (15 points)
===================================================================
Complete each function below. Run this file to check your answers.
"""

from z3 import *


# ---------------------------------------------------------------------------
# Part (a) — 3 pts
# Find integers x, y, z such that x + 2y = z, z > 10, x > 0, y > 0.
# ---------------------------------------------------------------------------
def part_a():
    x, y, z = Ints('x y z')
    s = Solver()

    s.add(x + 2 * y == z)
    s.add(z > 10)
    s.add(x > 0)
    s.add(y > 0)

    print("=== Part (a) ===")
    if s.check() == sat:
        m = s.model()
        print(f"SAT: x={m[x]}, y={m[y]}, z={m[z]}")
    else:
        print("UNSAT (unexpected!)")
    print()


# ---------------------------------------------------------------------------
# Part (b) — 3 pts
# Prove validity of: ∀x. x > 5 → x > 3
# Hint: A formula F is valid iff ¬F is unsatisfiable.
# ---------------------------------------------------------------------------
def part_b():
    x = Int('x')
    s = Solver()

    # Negation of (x > 5 -> x > 3) is (x > 5 ∧ ¬(x > 3)) i.e. (x > 5 ∧ x <= 3).
    # If this is UNSAT, the original implication is valid for all integers x.
    s.add(And(x > 5, Not(x > 3)))

    print("=== Part (b) ===")
    result = s.check()
    if result == unsat:
        print("Valid! (negation is UNSAT)")
    else:
        print(f"Not valid — counterexample: {s.model()}")
    print()


# ---------------------------------------------------------------------------
# Part (c) — 5 pts: The EUF Puzzle
#
# Formula:  f(f(x)) = x  ∧  f(f(f(x))) = x  ∧  f(x) ≠ x
#
# STEP 1: Check satisfiability with Z3. (2 pts)
#
# STEP 2: Use Z3 to derive WHY the result holds. (3 pts)
#   Write a series of Z3 validity checks that demonstrate the key reasoning
#   steps. For example, from f(f(x)) = x, what can you derive about f(f(f(x)))?
#   Each check should print what it's testing and whether it holds.
#   Hint: Apply f to both sides of the first equation.
# ---------------------------------------------------------------------------
def part_c():
    S = DeclareSort('S')
    x = Const('x', S)
    f = Function('f', S, S)
    s = Solver()

    s.add(f(f(x)) == x)
    s.add(f(f(f(x))) == x)
    s.add(f(x) != x)

    print("=== Part (c) ===")
    result = s.check()
    if result == sat:
        print(f"SAT: {s.model()}")
    else:
        print("UNSAT")

    # ---------------- STEP 2: Z3-driven derivation of WHY UNSAT ----------------
    # The conjunction is UNSAT. Here is the chain of reasoning, each step
    # encoded as an independent Z3 validity check (we assert the negation of
    # the implication and expect UNSAT).
    #
    # Step (i):  Functions are congruent: a = b → f(a) = f(b). This is a
    #            consequence of EUF (the theory of equality with uninterpreted
    #            functions). We verify the special instance we need:
    #              f(f(x)) = x  →  f(f(f(x))) = f(x)
    #            i.e. apply f to both sides of f(f(x)) = x.
    #
    # Step (ii): Combine (i) with the second hypothesis f(f(f(x))) = x to
    #            conclude f(x) = x:
    #              f(f(x)) = x  ∧  f(f(f(x))) = x  →  f(x) = x
    #
    # Step (iii): Conclude UNSAT — the third hypothesis f(x) ≠ x directly
    #             contradicts (ii):
    #              f(f(x)) = x ∧ f(f(f(x))) = x ∧ f(x) ≠ x  is UNSAT.

    def check_valid(name: str, hyp, conclusion):
        v = Solver()
        v.add(hyp)
        v.add(Not(conclusion))
        r = v.check()
        verdict = "VALID" if r == unsat else f"INVALID ({r})"
        print(f"  {name}: {verdict}")

    print("  Z3 derivation of why the puzzle is UNSAT:")
    # Step (i): congruence — apply f to both sides of f(f(x)) = x.
    check_valid(
        "(i)   f(f(x))=x  ⊢  f(f(f(x))) = f(x)",
        f(f(x)) == x,
        f(f(f(x))) == f(x),
    )
    # Step (ii): combine with f(f(f(x))) = x to derive f(x) = x.
    check_valid(
        "(ii)  f(f(x))=x ∧ f(f(f(x)))=x  ⊢  f(x) = x",
        And(f(f(x)) == x, f(f(f(x))) == x),
        f(x) == x,
    )
    # Step (iii): with f(x) ≠ x added, the whole conjunction implies False.
    check_valid(
        "(iii) f(f(x))=x ∧ f(f(f(x)))=x ∧ f(x)≠x  ⊢  False",
        And(f(f(x)) == x, f(f(f(x))) == x, f(x) != x),
        BoolVal(False),
    )
    print()


# ---------------------------------------------------------------------------
# Part (d) — 4 pts: Array Axioms
#
# Prove BOTH axioms (two separate solver checks):
#   (1) Read-over-write HIT:   i = j  →  Select(Store(a, i, v), j) = v
#   (2) Read-over-write MISS:  i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
#
# [EXPLAIN] in a comment below: Why are these two axioms together sufficient
# to fully characterize Store/Select behavior? (2–3 sentences)
# ---------------------------------------------------------------------------
def part_d():
    a = Array('a', IntSort(), IntSort())
    i, j, v = Ints('i j v')

    print("=== Part (d) ===")

    # Axiom 1: Read-over-write HIT — negate and check UNSAT.
    s1 = Solver()
    s1.add(Not(Implies(i == j, Select(Store(a, i, v), j) == v)))
    r1 = s1.check()
    print(f"Axiom 1 (hit):  {'Valid' if r1 == unsat else 'INVALID'}")

    # Axiom 2: Read-over-write MISS — negate and check UNSAT.
    s2 = Solver()
    s2.add(Not(Implies(i != j, Select(Store(a, i, v), j) == Select(a, j))))
    r2 = s2.check()
    print(f"Axiom 2 (miss): {'Valid' if r2 == unsat else 'INVALID'}")
    print()

    # [EXPLAIN] Why are these two axioms together sufficient?
    # Together the HIT and MISS axioms give a complete case analysis on the
    # equality of i and j: for ANY query Select(Store(a, i, v), j) the index j
    # either equals i (axiom 1 fixes the value to v) or it does not (axiom 2
    # forces the result to agree with the original array a at j). Two arrays
    # are equal iff they agree on every index, so these two axioms uniquely
    # determine the array produced by Store and hence fully characterize the
    # combined behavior of Select and Store — this is exactly McCarthy's
    # extensional theory of arrays.


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
