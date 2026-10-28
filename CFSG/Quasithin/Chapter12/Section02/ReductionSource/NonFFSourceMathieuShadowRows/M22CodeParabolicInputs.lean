module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.Automizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.M22CodeParameters
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.Offender
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Parabolic
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair

/-!
# Original qrc inputs for the exceptional M22 code parabolic

The original reduced orbit and maximal-local uniqueness construct the qrc
configuration with M₀ = LT. The actual full-automizer code marking supplies
quadratic ratio at least two and excludes the dual FF case. Under the temporary
inside-core assumption, 3.1.8 supplies the reverse ratio bound; 3.1.9 then gives
exactly two noncentral chief factors on the same H-span of the original orbit.

These are the original 3.1.9 hypotheses used in 8.2.2(1). They do not yet
identify H/O₂(H) or exclude the inside-core branch.
Source: Aschbacher--Smith, printed pp.576--578,714--715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuShadowRows MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD ChapterD.UniqueFactor NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem original_qrc
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G)) (L ⊔ (T : Subgroup G)) H
      D.sourceOrbit := by
  let J := L ⊔ (T : Subgroup G)
  let Q := ReducedNormal.intrinsicSubspace J D.orbitSpace
  have hW : (⊤ : Subgroup J) ≤ subspaceStabilizer (ReducedNormal.representation J)
      D.orbitSpace := orbitSpan_invariant _ ⊤ D.space
  have hr : IsPReduced 2 Q := by
    change IsPReduced 2 (ReducedNormal.intrinsicSubspace J D.orbitSpace)
    rw [ReducedNormal.intrinsicSubspace_eq]
    exact ReducedNormal.subspaceImage_isPReduced_of_action_core J D.orbitSpace hW
      (D.orbit_twoCore_eq_bot h.toHypothesis1221)
  exact Chapter3.qrcHypotheses_of_reduced_join T (normalizer (L : Set G)) L H
    h.maximal_faithful.2.1.2.1 L.le_normalizer
    (normal_subgroupOf_of_le_normalizer le_rfl)
    (sup_le L.le_normalizer D.sylow_normalizes_component) hH Q hr
    (D.orbit_intrinsic_centralizer h.toHypothesis1221)

include D in
private theorem original_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
        N = normalizer (L : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  simpa only [D.localOrbit_eq] using And.intro hu.normalizer_maximal hu.normalizer_unique

/-- The actual conjugation image of every original normalizing subgroup has
code ratio at least two, and its dual is not FF. -/
theorem sourceOrbit_m22_code_local_parameters
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (X : Subgroup G) (hX : X ≤ normalizer (D.sourceOrbit : Set G)) :
    2 ≤ quadraticRatio (ChapterD.UniqueFactor.imageRepresentation X D.sourceOrbit hX) ∧
      ¬ IsFFModule (ChapterD.UniqueFactor.imageRepresentation X D.sourceOrbit hX).dual := by
  obtain ⟨a,ha,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h d
  let j : internalActionImage X D.sourceOrbit hX →* Automizer D.sourceOrbit :=
    inclusion (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hX x,rfl⟩)
  exact marked_m22_code_parameters _ (a.comp j) (ha.comp (inclusion_injective _))
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
    (fun b v => hE (j b) v)

/-- The temporary inside-core branch has all numerical and dual hypotheses
of original 3.1.9, on LT's literal action image. -/
theorem sourceOrbit_m22_code_inside_core_inputs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    ∃ c : Chapter3.QrcHypotheses T (normalizer (L : Set G)) (L ⊔ (T : Subgroup G)) H
      D.sourceOrbit,
      H ⊓ normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G) ∧
      quadraticRatio (ChapterD.UniqueFactor.imageRepresentation (L ⊔ (T : Subgroup G))
        D.sourceOrbit c.module_normalized) = 2 ∧
      ¬ IsFFModule (ChapterD.UniqueFactor.imageRepresentation (L ⊔ (T : Subgroup G))
        D.sourceOrbit c.module_normalized).dual := by
  let c := D.original_qrc h hH
  obtain ⟨hM,hu⟩ := D.original_uniqueness h
  obtain ⟨hl,hd⟩ := D.sourceOrbit_m22_code_local_parameters h.toHypothesis1221 d _ c.module_normalized
  have hb : quadraticRatio (ChapterD.UniqueFactor.imageRepresentation (L ⊔ (T : Subgroup G))
      D.sourceOrbit c.module_normalized) ≤ 2 := by
    rcases c.quadraticRatio_le_two_or_dualFF h.simpleQTKE hM hu
      D.sourceOrbit_weakClosure_setup.nontrivial hcore with hb | hd'
    · exact hb
    · exact (hd hd').elim
  exact ⟨c,D.m24_hstar_normalizes h hmany hV hnon hH,le_antisymm hb hl,hd⟩

/-- Original 3.1.9(1) in the exceptional code branch: every chief series of
the same H-span has exactly two noncentral factors. -/
theorem sourceOrbit_m22_code_inside_core_two_chiefs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    ∀ s : SeriesOn ((conjugateSpan H D.sourceOrbit).subgroupOf H), s.noncentralCount = 2 := by
  obtain ⟨c,_,hq,hd⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  obtain ⟨hM,hu⟩ := D.original_uniqueness h
  exact c.sqtk_noncentral_count_two h.simpleQTKE hM hu
    (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
    D.sourceOrbit_weakClosure_setup.nontrivial hcore hd hq

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
