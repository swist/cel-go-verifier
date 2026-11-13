"""Injects the SmtDump hook into the synced cel-java verifier sources."""
import pathlib
import sys

src = pathlib.Path(sys.argv[1])
impl = src / "main/java/dev/cel/verifier/CelVerifierZ3Impl.java"
text = impl.read_text()
replacements = [
    ("Solver solver = ctx.mkSolver();", "Solver solver = SmtDump.newSolver(ctx.mkSolver());"),
    ("solver.push();", "SmtDump.push(solver);"),
    ("solver.pop();", "SmtDump.pop(solver);"),
    ("solver.add(", "SmtDump.add(solver, "),
    ("solver.check()", "SmtDump.check(solver)"),
]
for old, new in replacements:
    if old not in text:
        sys.exit(f"patch.py: '{old}' not found in {impl}")
    text = text.replace(old, new)
impl.write_text(text)

tool = src / "main/java/dev/cel/verifier/tools/CelVerifierTool.java"
text = tool.read_text()
for old, new in [
    (",\n      CelVerifierTool.ReplCommand.class", ""),
    ('"cel-verifier " + CelVersion.VERSION', '"cel-verifier javaref"'),
    ("return CelVerifierRepl.runInteractiveRepl();", "throw new UnsupportedOperationException();"),
]:
    if old not in text:
        sys.exit(f"patch.py: '{old}' not found in {tool}")
    text = text.replace(old, new)
tool.write_text(text)

# dev.cel 0.15.0 defaults enableHeterogeneousNumericComparisons to false, which the planner rejects;
# newer cel-java defaults it to true.
for f in src.rglob("*.java"):
    t = f.read_text()
    if "CelOptions.current()" in t and "javaref-heterogeneous" not in t:
        t = t.replace(
            "CelOptions.current()",
            "CelOptions.current().enableHeterogeneousNumericComparisons(true) /* javaref-heterogeneous */")
        f.write_text(t)
