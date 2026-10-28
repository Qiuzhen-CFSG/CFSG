module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.VectorStabilizers.Pure
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.VectorStabilizers.Outer

/-!
# The vector-stabilizer families of H.9.1(3–4)

For the explicit coordinate action of Aut(GL_n(2)), n = 4 or 5, the imported
pure-vector family proves the elementary split extension, its intrinsic
two-core, both quotient actions, the commutator spaces and the original
Sylow marking. The nonsingular family below assembles the actual residual
and stabilizer identifications with the complementary natural/dual actions.
The full stabilizer is identified through its faithful conjugation action
on the kernel group, compatibly with the inner projective identification.
Every Sylow of that stabilizer contains a complementing outer involution.

All statements use the actual embedded two-residual O²(C_L(v)). Their only
action input is `CoordinateAction`; its construction and comparison with
the arbitrary source module belong to the H.9 assembly. The nonsingular
Sylow is chosen independently of the pure-vector marking. The adapted-pair
theorem needed by Chapter 12 has its own owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(3–4),
printed pp.389–390; the correction to the fixed-Sylow clause is recorded in
`docs/quasithin-proof-basis.md` and the driving workspace's
`.fleet/h09-source-repair-20261006/source-audit.md`.
-/

public section

namespace CFSG.Quasithin.ChapterH.NaturalDual
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers

/-- All nonsingular centralizers and residuals agree as embedded subgroups;
the complementary modules are the actual fixed and commutator spaces of L_v. -/
theorem nonsingular_stabilizer_structure {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    quadratic (x,f) = 1 ∧
    componentStabilizer d x f = innerResidual d (x,f) ∧
    (MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup n) ⊓
      componentStabilizer d x f) = innerResidual d (x,f) ∧
    innerStabilizer d (x,f) = innerResidual d (x,f) ∧
    (pResidual 2 (componentStabilizer d x f)).map (componentStabilizer d x f).subtype =
      innerResidual d (x,f) ∧
    (pResidual 2 (fullStabilizer d (x,f))).map (fullStabilizer d (x,f)).subtype =
      innerResidual d (x,f) ∧
    Nonempty (innerResidual d (x,f) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)) ∧
    Nonempty (fullStabilizer d (x,f) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2))) ∧
    IsCompl (Submodule.span (ZMod 2) {x}) f.ker ∧
    IsCompl (Submodule.span (ZMod 2) {f}) (annihilator x) ∧
    Representation.invariants (residualRepresentation d (x,f)) =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f}) ∧
    Representation.Coinvariants.ker (residualRepresentation d (x,f)) =
      f.ker.prod (annihilator x) := by
  have hr := innerResidual_eq_innerStabilizer hn d h
  refine ⟨h, componentStabilizer_eq_innerResidual hn d h, ?_, hr.symm,
    componentStabilizer_embedded_twoResidual hn d h, ?_,
    ⟨(MulEquiv.subgroupCongr hr).trans (innerStabilizerEquivProjective hn d h)⟩,
    ⟨fullStabilizerEquivAutProjective hn d h⟩,
    line_isCompl_kernel h, dual_line_isCompl_annihilator h,
    residual_invariants hn d h, residual_commutator hn d h⟩
  · rw [componentStabilizer_eq_innerStabilizer hn d (vector_ne_zero h), hr]
    exact inf_eq_right.mpr inf_le_left
  · rw [fullStabilizer_embedded_twoResidual hn d h, hr]

/-- The two complementary actions of the actual L_v are natural and dual
under one full linear-group equivalence and the restriction pairing. -/
theorem nonsingular_complement_actions {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Module.finrank (ZMod 2) f.ker = n - 1 ∧
    Module.finrank (ZMod 2) (annihilator x) = n - 1 ∧
    ∃ e : innerResidual d (x,f) ≃* BinaryLinear.GL f.ker,
      (∀ (a : innerResidual d (x,f)) (w : f.ker),
        d.representation a.val (w.val,0) = ((e a w).val,0)) ∧
      (∀ (a : innerResidual d (x,f)) (q : annihilator x),
        d.representation a.val (0,q.val) =
          (0,((annihilatorEquivKernelDual h).symm
            ((e a).symm.dualMap (annihilatorEquivKernelDual h q))).val)) := by
  refine ⟨(kernelCoordinates h).finrank_eq.trans ?_, Pure.annihilator_finrank
    (vector_ne_zero h), residualEquivKernel hn d h,
    residual_kernel_action hn d h, residual_dual_action hn d h⟩
  simp only [BinaryLinear.OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin]

/-- Recognition by actual conjugation preserves the given inner projective
identification, pointwise and on the whole embedded subgroup. -/
theorem nonsingular_automorphism_identification {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    ∃ e : fullStabilizer d (x,f) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)),
      (∀ a : innerStabilizer d (x,f),
        e ⟨a.val,a.property.2⟩ = MulAut.conj (innerStabilizerEquivProjective hn d h a)) ∧
      (innerInFull d (x,f)).map e.toMonoidHom =
        MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)) :=
  ⟨fullStabilizerEquivAutProjective hn d h,
    fullStabilizerEquivAutProjective_inner hn d h,
    fullStabilizerEquivAutProjective_map_inner hn d h⟩

/-- A separately chosen stabilizer Sylow contains an outer involution that
exchanges the marked components and gives the internal semidirect product. -/
theorem nonsingular_sylow_extension {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (P : Sylow 2 (fullStabilizer d (x,f))) :
    ∃ s : fullStabilizer d (x,f), s ∈ P ∧
      s.val ∉ MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup n) ∧
      s ^ 2 = 1 ∧ (innerInFull d (x,f)).IsComplement' (Subgroup.zpowers s) ∧
      d.representation s.val (x,0) = (0,f) ∧
      d.representation s.val (0,f) = (x,0) ∧
      Nonempty ((innerInFull d (x,f)) ⋊[(innerInFull d (x,f)).normalizerMonoidHom.comp
        (Subgroup.inclusion ((innerInFull d (x,f)).normalizer_eq_top ▸ le_top))]
          (Subgroup.zpowers s) ≃* fullStabilizer d (x,f)) := by
  obtain ⟨s,hs,hout,hsq,hcomp⟩ := sylow_exists_outer_involution hn d h P
  obtain ⟨hxf,hfx⟩ := outer_swaps_components hn d s hout
  exact ⟨s,hs,hout,hsq,hcomp,hxf,hfx,⟨outerSemidirectEquiv hn d h s hout hsq⟩⟩

/-- The centralizer orders consumed by the corrected adapted-pair construction. -/
theorem nonsingular_stabilizer_orders :
    (∀ (d : CoordinateAction 4) (x : BinaryLinear.OuterCyclic.Space 4)
      (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space 4)), f x = 1 →
      Nat.card (fullStabilizer d (x,f)) = 336) ∧
    (∀ (d : CoordinateAction 5) (x : BinaryLinear.OuterCyclic.Space 5)
      (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space 5)), f x = 1 →
      Nat.card (fullStabilizer d (x,f)) = 40320) :=
  ⟨fun d _ _ h => fullStabilizer_card_four d h,
    fun d _ _ h => fullStabilizer_card_five d h⟩

end CFSG.Quasithin.ChapterH.NaturalDual
