# Theorem 2 proof search (2026-09-01)

- `rg` over all project Lean sources finds no declaration mentioning `IsNTwoGroup`, `IsOfExceptionalType`, `ExceptionalAmalgam`, or `IsSemidihedralGroup` besides the definitions and `Stellmacher.theorem_two` in `Stellmacher/FinalTheorem.lean`.
- `Stellmacher.theorem_one` is the only nearby classification interface, but `#print axioms Stellmacher.theorem_one` reports `[propext, sorryAx, Classical.choice, Quot.sound]`; using it would violate the no-bridges rule.
- Disposable probe `TheoremTwoProbe.lean` imports `Stellmacher.FinalTheorem` and reproduces the exact theorem_two target. `exact?` suggests only the self-reference `theorem_two hN2 hEven S0`; `aesop` fails after exhaustive search with the full disjunctive goal.
- `#print axioms Stellmacher.theorem_two` likewise reports `sorryAx` (expected while placeholder remains).
- No generic imported theorem supplies the required classification/trichotomy. The existing APIs prove local facts only; deriving the five alternatives requires formalizing substantial missing Stellmacher sections (2-local amalgam classification, semidihedral analysis, strong embedding branch, etc.).

Conclusion: no sorry-free proof route is available from current imports without adding a new classification theorem/interface or formalizing the source proof. Keep theorem_two as a statement-level `sorry` until that infrastructure exists; do not use theorem_one as a bridge.

Source complexity evidence: PDF pp. 12--14 says Theorem 2's proof depends on Gomi's amalgam pair (properties (1)--(3)), analysis of `V₁(Z(S₀))`, structures of `Pᵢ/O₂(Pᵢ)`, and Sections 7--10's case analyses. None of these hypotheses/conclusions are formalized in current Stellmacher modules.
