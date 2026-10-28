module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Modules

/-!
# Inner stabilizer clauses of H.9.1

For the actual automorphism group acting through `CoordinateAction`, the
pairing-one stabilizer inside the inner subgroup is the genuine projective
linear group in one lower dimension. It equals its two-residual and the
simultaneous fixer of the two pure components. Its complementary modules are
the natural kernel and the dual annihilator, with exact fixed and commutator
spaces. A nonzero pure vector has no outer stabilizer.

This assembles those proved clauses. The pure parabolic family, the full
nonsingular outer extension, and their Sylow assertions remain separate
branches of H.9.1; the coordinate action is the explicit shared input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(3–4),
printed pp.389–390, and the fixed-Sylow correction documented in
`.fleet/h09-source-repair-20261006/source-audit.md` of the driving workspace.
-/

public section

namespace CFSG.Quasithin.ChapterH.NaturalDual
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers

/-- The nonsingular inner stabilizer and module clauses of the corrected H.9.1(4).
The full outer extension and its Sylow involutions are separate obligations. -/
theorem nonsingular_inner_stabilizer_structure {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    componentStabilizer d x f = innerResidual d (x,f) ∧
    innerResidual d (x,f) = innerStabilizer d (x,f) ∧
    Nonempty (innerStabilizer d (x,f) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)) ∧
    IsCompl (Submodule.span (ZMod 2) {x}) f.ker ∧
    IsCompl (Submodule.span (ZMod 2) {f}) (annihilator x) ∧
    Representation.invariants (innerRepresentation d (x,f)) =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f}) ∧
    Representation.Coinvariants.ker (innerRepresentation d (x,f)) =
      f.ker.prod (annihilator x) :=
  ⟨componentStabilizer_eq_innerResidual hn d h,
    innerResidual_eq_innerStabilizer hn d h,
    ⟨innerStabilizerEquivProjective hn d h⟩,
    line_isCompl_kernel h, dual_line_isCompl_annihilator h,
    inner_invariants hn d h, inner_commutator hn d h⟩

/-- The equality of the full and inner pure-vector stabilizers in H.9.1(3). -/
theorem pure_stabilizer_is_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} (hx : x ≠ 0) :
    fullStabilizer d (x,0) = innerStabilizer d (x,0) :=
  pure_fullStabilizer_eq_innerStabilizer hn d hx

end CFSG.Quasithin.ChapterH.NaturalDual
