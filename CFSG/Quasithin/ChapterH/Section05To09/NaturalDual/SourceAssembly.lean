module
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourcePairedGeometry
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceAdaptedPair
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFiveActors
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors

/-!
# Source assembly of H.9.1–3

Every result takes the standing `SourceSetup` and the displayed vector,
Sylow or elementary-actor hypotheses. The full automorphism action and
marked whole-module comparison are constructed, not additional premises.

For H.9.1(1–2), `quadratic_invariant`, `quadratic_unique`,
`source_form_and_orbits`, `orbit_iff`, and `singularDiagonal_iff_sylow`
provide the form and three nonzero orbits, with the existential Sylow clause.
For (3), `pure_source_structure`, `pure_split_extension`,
`pureNativeQuotientEquiv_action`, `naturalSylow_fixed_finrank` and
`pure_sylow` retain the actual pure stabilizer and both commutator modules.

`lemma_H_9_1_4_adequate` proves the corrected nonsingular clause.
`pairedNaturalComplement_orthogonal`, `pairedDualComplement_orthogonal`
and `paired_complement_actions` give the literal polar complements and
their exact natural and dual actions. `nonsingularSemidirectEquiv` uses
the actual conjugation action; `innerInStabilizer_image` identifies its
normal factor with the embedded two-residual. `nonsingular_sylow_outer`
works for every independently chosen stabilizer Sylow. `adapted_pair`
and `adapted_vector` supply the original fixed-Sylow consumer marking.

`SourceFiveActors.sylow_family`, `high_rank_family`, `outer_diagonal`,
`outer_conjugate` and `outer_decomposition` supply all of H.9.2 on the
original module. `SourceFourActors` supplies H.9.3, including its complete
marked permutation catalogue, three fixed/core formulas, transvections,
and the mixed-space and quotient-action calculations on printed p.392.
Both families use the actual Chapter E generated core.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1–3,
printed pp.389–392, PDF pp.400–403. The fixed-Sylow clause in H.9.1(4)
uses the authorized correction of 6 October 2026. Chapter 12's ambient
kernel, quotient and local-group arguments remain with that chapter.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup n M V)

/-- H.9.1(2) uses the SAME unique form as the source stabilizer and actor families. -/
theorem orbit_iff {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    (∃ m : M, S.representation m v = w) ↔
      (MarkedGeometry.Pure S.natural S.dual v ∧ MarkedGeometry.Pure S.natural S.dual w) ∨
      (MarkedGeometry.SingularDiagonal S.natural S.dual S.quadratic v ∧
        MarkedGeometry.SingularDiagonal S.natural S.dual S.quadratic w) ∨
      (S.quadratic v = 1 ∧ S.quadratic w = 1) :=
  MarkedGeometry.orbit_iff (AutomorphismModel.coordinateAction S.degree) S.representation
    S.model.group S.model.coordinates S.model.equivariant
    (MarkedGeometry.mem_natural_iff_of_marking _ _ S.model.natural_marking)
    (MarkedGeometry.mem_dual_iff_of_marking _ _ S.model.dual_marking) S.degree hv hw

/-- The Sylow clause is existential for each singular diagonal vector. -/
theorem singularDiagonal_iff_sylow {v : V} (hv : v ≠ 0) :
    MarkedGeometry.SingularDiagonal S.natural S.dual S.quadratic v ↔
      ∃ T : Sylow 2 M, ∀ a ∈ T, S.representation a v = v :=
  MarkedGeometry.singularDiagonal_iff_exists_sylow_fixed
    (AutomorphismModel.coordinateAction S.degree) S.representation
    S.model.group S.model.coordinates S.model.equivariant
    (MarkedGeometry.mem_natural_iff_of_marking _ _ S.model.natural_marking)
    (MarkedGeometry.mem_dual_iff_of_marking _ _ S.model.dual_marking) S.degree hv

/-- The pure source quotient acts as the full linear group on its native dual hyperplane. -/
noncomputable def pureNativeQuotientEquiv (u : S.natural) (hu : (u : V) ≠ 0) :
    (S.stabilizer u ⧸ pCore 2 (S.stabilizer u)) ≃* BinaryLinear.GL (S.dualHyperplane u) :=
  (S.pureQuotientEquiv u hu).trans (Pure.linearGroupCongr (S.pairedDualEquiv u))

theorem pureNativeQuotientEquiv_action (u : S.natural) (hu : (u : V) ≠ 0)
    (a : S.stabilizer u) (f : S.dualHyperplane u) :
    (S.pureNativeQuotientEquiv u hu (QuotientGroup.mk' _ a) f : V) =
      S.representation a.val f := by
  obtain ⟨q,rfl⟩ := (S.pairedDualEquiv u).surjective f
  change (S.pairedDualEquiv u
    (S.pureQuotientEquiv u hu (QuotientGroup.mk' _ a)
      ((S.pairedDualEquiv u).symm (S.pairedDualEquiv u q))) : V) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (S.pureQuotientEquiv_action u hu a q).symm

/-- The internal normal factor is literally the embedded source residual. -/
theorem innerInStabilizer_image {v : V} (hv : S.quadratic v = 1) :
    (S.innerInStabilizer v).map (S.stabilizer v).subtype = S.residual v := by
  rw [S.residual_eq_innerStabilizer hv]
  ext a
  constructor
  · rintro ⟨g,hg,rfl⟩; exact ⟨hg,g.property⟩
  · rintro ⟨ha,hv⟩; exact ⟨⟨a,hv⟩,ha,rfl⟩

/-- H.9.1(3): the pure-vector structure and both literal commutator modules.
The quotient's exact natural action is `pureNativeQuotientEquiv_action`,
its splitting is `pure_split_extension`, and its supplied Sylow is `pure_sylow`. -/
theorem pure_source_structure (u : S.natural) (hu : (u : V) ≠ 0) :
    S.stabilizer u = S.innerStabilizer u ∧ S.stabilizer u = S.residual u ∧
    IsElementaryAbelian 2 (pCore 2 (S.stabilizer u)) ∧
    Nat.card (pCore 2 (S.stabilizer u)) = 2 ^ (n - 1) ∧
    Nonempty ((S.stabilizer u ⧸ pCore 2 (S.stabilizer u)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)) ∧
    Representation.BinaryOffender.subspaceCommutator S.representation S.natural (S.residual u) = S.natural ∧
    Representation.BinaryOffender.subspaceCommutator S.representation S.dual (S.residual u) = S.dualHyperplane u ∧
    Module.finrank (ZMod 2) (S.dualHyperplane u) = n - 1 := by
  obtain ⟨hs,hl⟩ := S.pure_stabilizer_eq_residual u hu
  exact ⟨(inf_eq_right.mpr hl).symm,hs,(S.pure_twoCore u hu).1,
    (S.pure_twoCore u hu).2,S.pure_quotient_projective u hu,
    (S.pure_commutators u hu).1,(S.pure_commutators u hu).2,S.dualHyperplane_finrank u hu⟩

/-- Adequate H.9.1(4), with arbitrary paired nonsingular components.
The outer involution is chosen in their stabilizer. The original fixed Sylow
is treated by `adapted_pair`, with every supplied two-subgroup retained. -/
theorem lemma_H_9_1_4_adequate (u : S.natural) (w : S.dual)
    (h : S.quadratic ((u : V) + w) = 1) :
    let v := (u : V) + w
    S.residual v = S.innerStabilizer v ∧
    S.stabilizer u ⊓ S.stabilizer w = S.residual v ∧
    (pResidual 2 (S.stabilizer v)).map (S.stabilizer v).subtype = S.residual v ∧
    Nonempty (S.residual v ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)) ∧
    Nonempty (S.stabilizer v ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2))) ∧
    (∃ s : S.stabilizer v, s.val ∉ componentLayer M ∧ s ^ 2 = 1 ∧
      (S.innerInStabilizer v).IsComplement' (Subgroup.zpowers s) ∧
      S.representation s.val u = w ∧ S.representation s.val w = u) ∧
    S.fixed (S.residual v) = Submodule.span (ZMod 2) {(u : V),(w : V)} ∧
    S.moving v = S.pairedNaturalComplement w ⊔ S.dualHyperplane u ∧
    Submodule.span (ZMod 2) {(u : V)} ⊔ S.pairedNaturalComplement w = S.natural ∧
    Disjoint (Submodule.span (ZMod 2) {(u : V)}) (S.pairedNaturalComplement w) ∧
    Submodule.span (ZMod 2) {(w : V)} ⊔ S.dualHyperplane u = S.dual ∧
    Disjoint (Submodule.span (ZMod 2) {(w : V)}) (S.dualHyperplane u) ∧
    Disjoint (S.pairedNaturalComplement w) (S.dualHyperplane u) := by
  dsimp only
  obtain ⟨hr,he,hM,_,_⟩ := S.nonsingular_structure h
  obtain ⟨hf,hm⟩ := S.paired_fixed_moving u w h
  refine ⟨hr,S.paired_stabilizer u w h,S.nonsingular_full_residual h,he,hM,?_,hf,hm,
    S.paired_decompositions u w h⟩
  let := S.finite_group
  let P : Sylow 2 (S.stabilizer ((u : V) + w)) := Classical.choice inferInstance
  obtain ⟨s,_,ho,hs,hc⟩ := S.nonsingular_sylow_outer h P
  exact ⟨s,ho,hs,hc,S.paired_outer_swaps u w s ho⟩
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
