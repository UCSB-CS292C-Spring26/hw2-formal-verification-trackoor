"""
CS292C Homework 2 — Problem 5 (Bonus): Verified Skill Composition (10 points)
===============================================================================
Verify that two sequentially composed agent skills maintain a filesystem
invariant, then show how a composition bug breaks the invariant.
"""

from z3 import *


# ============================================================================
# Filesystem Model
#
# We model the filesystem as a Z3 array: Array(Int, Int)
#   - Index = file path ID (integer)
#   - Value = content hash (integer)
#
# Two paths are special:
#   INPUT_FILE = 0   (the file Skill A reads)
#   OUTPUT_FILE = 1  (the file Skill B writes to)
# ============================================================================

INPUT_FILE = 0
OUTPUT_FILE = 1


# ============================================================================
# Part (a): Verify correct composition — 4 pts
# ============================================================================

def verify_correct_composition():
    print("=== Part (a): Correct Composition ===")

    fs_initial = Array('fs_initial', IntSort(), IntSort())
    fs_after_A = Array('fs_after_A', IntSort(), IntSort())
    fs_final   = Array('fs_final', IntSort(), IntSort())
    result_content = Int('result_content')
    p = Int('p')

    # Skill A postcondition: filesystem unchanged
    skill_A_post = fs_after_A == fs_initial

    # Skill B postcondition: only OUTPUT_FILE changes
    skill_B_post = And(
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    # Composed postcondition to verify
    composed_post = And(
        # Input file preserved
        Select(fs_final, INPUT_FILE) == Select(fs_initial, INPUT_FILE),
        # Output written
        Select(fs_final, OUTPUT_FILE) == result_content,
        # Nothing else changed
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    # Verify (skill_A_post ∧ skill_B_post) → composed_post by checking the
    # negation is UNSAT.
    s = Solver()
    s.add(skill_A_post)
    s.add(skill_B_post)
    s.add(Not(composed_post))

    result = s.check()
    if result == unsat:
        print("  Composed postcondition VERIFIED — Skill A; Skill B preserves")
        print("  the input file, writes the output, and touches nothing else.")
    else:
        print(f"  UNEXPECTED: composition failed. result={result}")
        if result == sat:
            print(f"  Counterexample: {s.model()}")
    print()


# ============================================================================
# Part (b): Buggy composition — 3 pts
# ============================================================================

def verify_buggy_composition():
    print("=== Part (b): Buggy Composition ===")

    fs_initial = Array('fs_initial', IntSort(), IntSort())
    fs_after_A = Array('fs_after_A', IntSort(), IntSort())
    fs_final   = Array('fs_final', IntSort(), IntSort())
    result_content = Int('result_content')
    p = Int('p')

    skill_A_post = fs_after_A == fs_initial

    # BUGGY Skill B: writes to INPUT_FILE instead of OUTPUT_FILE
    buggy_B_post = And(
        Select(fs_final, INPUT_FILE) == result_content,  # ← BUG
        ForAll([p], Implies(p != INPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    composed_post = And(
        Select(fs_final, INPUT_FILE) == Select(fs_initial, INPUT_FILE),
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    s = Solver()
    s.add(skill_A_post)
    s.add(buggy_B_post)
    s.add(Not(composed_post))

    result = s.check()
    if result == sat:
        m = s.model()
        print("  Composition FAILS — Z3 found a counterexample:")
        # Probe the model on a couple of canonical indices.
        in_initial = m.eval(Select(fs_initial, INPUT_FILE), model_completion=True)
        in_final   = m.eval(Select(fs_final,   INPUT_FILE), model_completion=True)
        out_final  = m.eval(Select(fs_final,   OUTPUT_FILE), model_completion=True)
        rc         = m.eval(result_content, model_completion=True)
        print(f"    fs_initial[INPUT]  = {in_initial}")
        print(f"    fs_final[INPUT]    = {in_final}     ← was overwritten by Skill B")
        print(f"    fs_final[OUTPUT]   = {out_final}")
        print(f"    result_content     = {rc}")
        print("  The composed postcondition demands fs_final[INPUT] = fs_initial[INPUT],")
        print("  but the buggy Skill B clobbered INPUT with `result_content`.")
    else:
        print(f"  UNEXPECTED — buggy composition was proved correct? result={result}")
    print()


# ============================================================================
# Part (c): Real-world connection — 3 pts
#
# [EXPLAIN] How this composition bug shows up in real agent workflows.
#
# This is the classic "skills compose only if you trust their FRAMES (the
# set of memory/files each step promises NOT to touch), and most skills'
# stated frames are weaker than the user's mental model." A concrete case
# I have seen with Claude Code: a "summarize this file" skill reads
# `notes.md`, and a follow-up "save the summary" skill is asked to write
# the result somewhere — if the agent picks the same path it just read
# from (because it's the most salient path in context), the summary
# replaces the original notes. From the agent's view both steps
# individually had reasonable post-conditions; what failed was the JOIN —
# the second skill's "writes to OUTPUT" post-condition collided with the
# first skill's "INPUT unchanged" post-condition because OUTPUT silently
# aliased INPUT.
#
# A runtime monitor that prevents this class of bug must (a) record which
# concrete paths were *read* during Skill A (the input frame), (b) record
# which paths Skill B is about to *write*, and (c) deny any write whose
# target intersects an already-read path unless the user has explicitly
# blessed an in-place modification. In practice this is "no write-back to
# a previously-read file without a transformation marker" — the same idea
# as the write-after-read taint monitor from Problem 4(c). At the SMT
# level it is exactly the disjointness of the read-set of A and the
# write-set of B that we asserted (implicitly) by giving them disjoint
# frame conditions.
# ============================================================================


# ============================================================================
if __name__ == "__main__":
    verify_correct_composition()
    verify_buggy_composition()
