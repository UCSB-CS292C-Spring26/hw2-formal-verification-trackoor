"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
# ============================================================================

def _allowed_definition(include_R4: bool = True) -> BoolRef:
    """
    Build the closed-world definition of `allowed(u, t, r)` as a single
    biconditional ranging over all u, t, r.

    Design notes:
      * R3 says admins may use ANY tool on ANY resource. R4 carves out
        shell_exec on sensitive resources (overriding R3). R5 carves
        network_fetch down to sandbox resources only.
      * Default-deny: any (role, tool, resource) combination not covered by
        R1–R5 is implicitly disallowed by the biconditional.
      * `include_R4=False` is used in Part (b) Q4 to demonstrate what becomes
        possible if the override is removed.
    """
    u = Const('u', User)
    t = Int('t')
    r = Const('r', Resource)

    role_admin   = role(u) == ADMIN
    role_dev     = role(u) == DEVELOPER
    role_viewer  = role(u) == VIEWER

    # ---- Admin clauses (R3, restricted by R4 and R5) ----
    admin_read   = And(role_admin, t == FILE_READ)
    admin_write  = And(role_admin, t == FILE_WRITE)
    if include_R4:
        admin_shell = And(role_admin, t == SHELL_EXEC, Not(is_sensitive(r)))
    else:
        # R4 removed — admin can shell anywhere.
        admin_shell = And(role_admin, t == SHELL_EXEC)
    admin_net    = And(role_admin, t == NETWORK_FETCH, in_sandbox(r))   # R5

    # ---- Developer clauses (R2) ----
    dev_read     = And(role_dev, t == FILE_READ)
    dev_write    = And(role_dev, t == FILE_WRITE,
                       Or(owner(r) == u, in_sandbox(r)))

    # ---- Viewer clauses (R1) ----
    viewer_read  = And(role_viewer, t == FILE_READ, Not(is_sensitive(r)))

    permitted = Or(
        admin_read, admin_write, admin_shell, admin_net,
        dev_read,   dev_write,
        viewer_read,
    )

    return ForAll([u, t, r], allowed(u, t, r) == permitted)


def make_policy():
    """
    Return a list of Z3 constraints encoding rules R1–R5 under a closed-world
    assumption: a (user, tool, resource) triple is allowed iff one of the
    rules below permits it.
    """
    return [_allowed_definition(include_R4=True)]


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """Answer the four policy queries."""
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u  = Const('q_u',  User)
    u2 = Const('q_u2', User)
    r  = Const('q_r',  Resource)

    # ---- Q1: Can a developer write to a sensitive file they don't own
    #         that is in the sandbox? ----
    # R2 lets developers file_write any sandbox resource regardless of
    # ownership or sensitivity. Sensitivity only restricts FILE_READ for
    # viewers (R1) and SHELL_EXEC for everybody (R4) — it does NOT gate
    # FILE_WRITE. So the answer is SAT.
    query(
        "Q1: Developer writes to a sensitive sandbox file they don't own?",
        policy,
        And(
            role(u) == DEVELOPER,
            owner(r) != u,
            is_sensitive(r),
            in_sandbox(r),
            allowed(u, FILE_WRITE, r),
        ),
    )

    # ---- Q2: Can an admin network_fetch a resource outside the sandbox? ----
    # R5 forbids network_fetch outside the sandbox for everyone, even admins,
    # so the conjunction with `allowed` is UNSAT.
    query(
        "Q2: Admin network_fetch a resource outside the sandbox?",
        policy,
        And(
            role(u) == ADMIN,
            Not(in_sandbox(r)),
            allowed(u, NETWORK_FETCH, r),
        ),
    )

    # ---- Q3: Is there ANY role that can shell_exec on a sensitive resource? ----
    # R4 is a global ban. UNSAT for every role.
    query(
        "Q3: Any role shell_exec a sensitive resource?",
        policy,
        And(
            is_sensitive(r),
            allowed(u, SHELL_EXEC, r),
        ),
    )

    # ---- Q4: Drop R4. What becomes possible? ----
    # Without R4 the admin clause becomes "admin may shell_exec on anything",
    # so admins can now shell_exec on a sensitive resource — the precise
    # action R4 was meant to prevent. We re-encode `allowed` without R4 and
    # exhibit a witness.
    print("  Q4: Remove R4 — admins regain shell_exec on sensitive resources.")
    policy_no_R4 = [_allowed_definition(include_R4=False)]
    query(
        "Q4: Without R4, admin shell_exec on a sensitive resource?",
        policy_no_R4,
        And(
            role(u) == ADMIN,
            is_sensitive(r),
            allowed(u, SHELL_EXEC, r),
        ),
    )
    # [EXPLAIN] R4 is the *only* line in the policy that constrains
    # shell_exec on sensitive resources; it removes admin shell_exec on
    # sensitive resources from the otherwise-permissive admin grant in R3.
    # Removing R4 immediately exposes the most dangerous primitive in the
    # system — code execution against sensitive data — to any admin. Z3
    # exhibits a concrete (admin, sensitive resource) pair as the witness.


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
# ============================================================================

def part_c():
    """
    Model the 2-step shell_exec escalation under a new rule R6:
      R6 — developers may shell_exec on non-sensitive sandbox resources.

    Step 1: dev calls shell_exec on r1 (non-sensitive sandbox)         → R6 allows.
            Side effect: this changes r2's sensitivity from True → False.
    Step 2: dev calls shell_exec on r2 (now non-sensitive)             → R6 allows.

    The catch: in step 2, r2 was sensitive in the original world state,
    so R4 should have forbidden shell_exec on it. The 2-step trace lets
    the developer effectively bypass R4.

    We use TWO copies of the sensitivity oracle to model time:
      is_sensitive_before  — sensitivity at the start of the trace
      is_sensitive_after   — sensitivity after step 1 has executed
    """
    print("=== Part (c): Privilege Escalation ===\n")

    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after  = Function('is_sensitive_after',  Resource, BoolSort())

    u  = Const('dev',  User)
    r1 = Const('r1',   Resource)
    r2 = Const('r2',   Resource)

    # The new R6 grants developers shell_exec on non-sensitive sandbox
    # resources. We encode the trace directly rather than redefine `allowed`
    # globally, so that the escalation is visible step by step.
    def step1_ok(is_sens):
        # Step 1: dev shell_exec on r1, evaluated against the current world.
        return And(
            role(u) == DEVELOPER,
            in_sandbox(r1),
            Not(is_sens(r1)),       # R6: r1 must be non-sensitive
        )

    def step2_ok(is_sens):
        # Step 2: dev shell_exec on r2, evaluated against the current world.
        return And(
            role(u) == DEVELOPER,
            in_sandbox(r2),
            Not(is_sens(r2)),       # R6 says non-sensitive in current world
        )

    # ---------- Attack scenario ----------
    # Each step is checked against the world as it appears AT THAT STEP:
    # step 1 against `is_sensitive_before`, step 2 against `is_sensitive_after`.
    # Step 1's side-effect flips r2's sensitivity flag.
    s = Solver()
    s.add(r1 != r2)
    s.add(role(u) == DEVELOPER)
    # Initial world: r1 non-sensitive, r2 SENSITIVE.
    s.add(in_sandbox(r1))
    s.add(in_sandbox(r2))
    s.add(Not(is_sensitive_before(r1)))
    s.add(is_sensitive_before(r2))
    # Side-effect: r1's flag is unchanged; r2's flag is flipped.
    s.add(is_sensitive_after(r1) == is_sensitive_before(r1))
    s.add(is_sensitive_after(r2) == Not(is_sensitive_before(r2)))
    # Both steps individually pass the policy check at the moment they run.
    s.add(step1_ok(is_sensitive_before))
    s.add(step2_ok(is_sensitive_after))

    print("  Attack: 2-step shell_exec escalation under R6 (no fix yet)")
    res = s.check()
    print(f"  → {res}")
    if res == sat:
        m = s.model()
        print(f"    Model: {m}")
        print("    The developer just shell_exec'd a resource that was sensitive")
        print("    at the start of the trace, effectively bypassing R4.")
    print()

    # ---------- Fix ----------
    # [EXPLAIN] The escalation is possible because the policy is checked
    # only against the *current* sensitivity flag. The fix is to require
    # that any shell_exec target was non-sensitive in *every* world state
    # the trace has visited so far — i.e. shell_exec is forbidden on a
    # resource that was EVER sensitive in this trace. Equivalently:
    # sensitivity downgrades may not unlock shell_exec on a previously
    # sensitive resource. (An equivalent operational fix is to forbid
    # shell_exec from mutating sensitivity flags at all — that prevents
    # the side-effect that drives the attack.)
    print("  Fix: a shell_exec target must be non-sensitive at EVERY prior")
    print("       trace point, not just the moment of execution.")

    s_fix = Solver()
    s_fix.add(r1 != r2)
    s_fix.add(role(u) == DEVELOPER)
    s_fix.add(in_sandbox(r1))
    s_fix.add(in_sandbox(r2))
    s_fix.add(Not(is_sensitive_before(r1)))
    s_fix.add(is_sensitive_before(r2))
    s_fix.add(is_sensitive_after(r1) == is_sensitive_before(r1))
    s_fix.add(is_sensitive_after(r2) == Not(is_sensitive_before(r2)))
    # Strengthened R6 for the second step: the target must have been
    # non-sensitive in BOTH the before- and after-states.
    s_fix.add(step1_ok(is_sensitive_before))
    s_fix.add(And(
        in_sandbox(r2),
        Not(is_sensitive_before(r2)),    # ← new: also non-sensitive originally
        Not(is_sensitive_after(r2)),
    ))
    res_fix = s_fix.check()
    print(f"  → {res_fix}")
    if res_fix == unsat:
        print("  ESCALATION BLOCKED")
    else:
        print(f"  Still exploitable! Model: {s_fix.model()}")
    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
