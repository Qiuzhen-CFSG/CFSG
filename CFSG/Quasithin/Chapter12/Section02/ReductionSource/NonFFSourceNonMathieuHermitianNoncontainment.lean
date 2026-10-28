module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianQuadratic

import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The actual Hermitian orbit escapes every outside parabolic two-core

If the original orbit lay in O₂(H), the genuine reduced-join qrc theorem
would bound its quadratic ratio by two. The dual-FF alternative has the
same bound by the proved B.5.13 theorem. The conjugation image and the
existing orbit representation share the original local-join covering map;
faithfulness and the literal subgroup coordinates transport the bound.
Hermitian descent gives the contradictory strict lower bound.

This proves the Hermitian case of 8.2.2(1), including half-degree one,
without additional numerical, centralizer, or weak-closure assumptions.
The multiple-overgroup hypothesis also supplies an actual HStar witness.
The canonical offender and subsequent 8.2.3–13 arguments remain with
qt-d-1222-nonmathieu-hermitian-exclusion.
The private implementation import checks only the orbit projection's
pointwise conjugation formula; the public action boundaries are unchanged.

Source: Aschbacher–Smith 3.1.8(2) and 8.2.2(1), printed pp.576 and714–715,
using 3.2.9(4) and H.4.4 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule

private theorem quadraticRatio_le_of_common_cover
    {J A B U W : Type*} [Group J] [Group A] [Group B]
    [AddCommGroup U] [AddCommGroup W] [Module (ZMod 2) U] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A U) (σ : Representation (ZMod 2) B W)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (q : J →* A) (hq : Function.Surjective q) (r : J →* B)
    (e : W ≃ₗ[ZMod 2] U)
    (he : ∀ g w, e (σ (r g) w) = ρ (q g) (e w)) :
    quadraticRatio σ ≤ quadraticRatio ρ := by
  have hk : q.ker ≤ r.ker := by
    intro g hg
    apply hσ
    ext w
    apply e.injective
    rw [he, MonoidHom.mem_ker.mp hg, map_one, map_one]
    rfl
  let f := q.liftOfSurjective hq ⟨r, hk⟩
  have hf (g : J) : f (q g) = r g := q.liftOfRightInverse_comp_apply _ _ _ g
  have he' (a : A) (v : U) : e.symm (ρ a v) = σ (f a) (e.symm v) := by
    obtain ⟨g, rfl⟩ := hq a
    apply e.injective
    rw [e.apply_symm_apply, hf, he, e.apply_symm_apply]
  have hfi : Function.Injective f := by
    intro a b hab
    apply hρ
    ext v
    apply e.symm.injective
    rw [he', he', hab]
  exact quadraticRatio_le_of_injective_equivariant ρ σ f hfi e.symm he'

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem orbitHom_conjugation
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (D.sourceOrbit : Set G))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G)) (w : D.orbitSpace) :
    D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitHom g) w) =
      ChapterD.UniqueFactor.imageRepresentation (L ⊔ (T : Subgroup G)) D.sourceOrbit hn
        ((ChapterD.UniqueFactor.actionHom (L ⊔ (T : Subgroup G)) D.sourceOrbit hn).rangeRestrict g)
        (D.sourceOrbitCoordinates w) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (D.sourceOrbitCoordinates_apply (D.orbitRepresentation (D.orbitHom g) w)).trans
    (congrArg (fun x : G => (g : G) * x * (g : G)⁻¹)
      (D.sourceOrbitCoordinates_apply w).symm)

/-- The original Hermitian orbit cannot lie in the two-core of any actual
HStar member. This is the Hermitian branch of 8.2.2(1). -/
theorem sourceOrbit_hermitian_not_le_HStar_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ D.sourceOrbit ≤ H.pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let M := normalizer (L : Set G)
  let Q := ReducedNormal.intrinsicSubspace J D.orbitSpace
  have hW : (⊤ : Subgroup J) ≤ subspaceStabilizer (ReducedNormal.representation J)
      D.orbitSpace := orbitSpan_invariant _ ⊤ D.space
  have hr : IsPReduced 2 Q := by
    change IsPReduced 2 (ReducedNormal.intrinsicSubspace J D.orbitSpace)
    rw [ReducedNormal.intrinsicSubspace_eq]
    exact ReducedNormal.subspaceImage_isPReduced_of_action_core J D.orbitSpace hW
      (D.orbit_twoCore_eq_bot h.toHypothesis1221)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hj : J ≤ M := sup_le L.le_normalizer D.sylow_normalizes_component
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → J ≤ N → N = M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_unique
  have hn : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hq := Chapter3.qrcHypotheses_of_reduced_join T M L H
    h.maximal_faithful.2.1.2.1 L.le_normalizer hn hj hH Q hr
    (D.orbit_intrinsic_centralizer h.toHypothesis1221)
  change Chapter3.QrcHypotheses T M J H D.sourceOrbit at hq
  intro hcore
  have hbound : quadraticRatio
      (ChapterD.UniqueFactor.imageRepresentation J D.sourceOrbit hq.module_normalized) ≤ 2 := by
    rcases hq.quadraticRatio_le_two_or_dualFF h.simpleQTKE hm huniq
      D.sourceOrbit_weakClosure_setup.nontrivial hcore with hb | hd
    · exact hb
    · exact hq.quadraticRatio_le_two_of_dualFF h.simpleQTKE hm hd
  have htransport := quadraticRatio_le_of_common_cover
    (ChapterD.UniqueFactor.imageRepresentation J D.sourceOrbit hq.module_normalized)
    D.orbitRepresentation
    (ChapterD.UniqueFactor.imageRepresentation_injective J D.sourceOrbit hq.module_normalized)
    (subspaceImageRepresentation_injective _ _)
    (ChapterD.UniqueFactor.actionHom J D.sourceOrbit hq.module_normalized).rangeRestrict
    (ChapterD.UniqueFactor.actionHom J D.sourceOrbit hq.module_normalized).rangeRestrict_surjective
    D.orbitHom D.sourceOrbitCoordinates (D.orbitHom_conjugation hq.module_normalized)
  exact (not_le_of_gt (Chapter7.NormalizedSource.NonMathieuHermitian.quadraticRatio_gt_two
    hs hrow)) (htransport.trans hbound)

/-- The original multiple-overgroup premise supplies a parabolic for which
the literal orbit escapes the two-core. No replacement of T or of the action
is involved in the selection. -/
theorem sourceOrbit_hermitian_exists_HStar_outside_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs) :
    ∃ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        ¬ D.sourceOrbit ≤ H.pCoreIn 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany _ hm D.sylow_normalizes_component)
  exact ⟨H, hH, D.sourceOrbit_hermitian_not_le_HStar_core h hs hrow hH⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
