module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeEssentialSeed
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialCartanCover
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeParabolicInputs

/-!
# Cartans on the original nonsolvable M22-code essential action

The existing source construction supplies the essential quotient and the same
sharp actor on every chief factor. The natural-action alternatives now give
an actual split Cartan in the image of H ∩ N_G(L), whose nonidentity elements
move the image of the original seed. Its full original preimage projects
onto that Cartan with exactly the original action kernel. The whole-span
image of that preimage covers the same Cartan with kernel precisely its
intersection with the whole-action two-core, a proved two-group kernel.

For a cubic subgroup of the original overlap whose chief image is nontrivial
and lies in this Cartan, the centralizing alternative is impossible. Thus the
original M22 code and its dual have exactly three noncentral factors under
that same cubic. Existence of a cubic with these image properties, the field
bound and two-factor contradiction, and the symmetric-five exclusions remain
part of the original 3.1.9(6) sieve; none is assumed by the selection endpoint.

Source: Aschbacher--Smith, proof of 3.1.9(6), printed pp.577--578,
applied in 8.2.2(1), printed p.715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement
open Chapter8.MathieuShadowRows
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
open Chapter8.Section02.Offenders.Parabolic.Exclusion.CodeParabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option backward.isDefEq.respectTransparency false in
/-- On the same original essential action, the nonsolvable branch has a
small natural marking or a constructed split Cartan moving its source seed,
with its full original covering map. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_cartan
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) (hns : ¬ Group.IsSolvable H) :
    let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U,
      let := hU
      ∃ a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
          (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)),
        ∃ A ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
          ¬ A ≤ pCore 2 H ∧ IsQuadratic (normalRepresentation U) A ∧
          (∀ B ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
            ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
          EssentialChiefActor a A ∧
          OriginalCartanAlternatives (M := normalizer (L : Set G))
            D.sourceOrbit a.projection a.imageRepresentation a.vector := by
  obtain ⟨hU,a,A,hA,hAR,hquad,hmin,ha⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_seed h hmany hV hnon d hH hcore hns
  let := hU
  let c := D.original_qrc h hH
  have hD := Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1
  refine ⟨hU,a,A,hA,hAR,hquad,hmin,ha,?_⟩
  exact essential_original_cartan_alternatives c hD hns a ⟨_,ha.offender⟩

set_option backward.isDefEq.respectTransparency false in
/-- A cubic with nontrivial image in the constructed Cartan moves the
original orbit, so its code and dual chief counts are both three. -/
theorem sourceOrbit_m22_code_cartan_cubic_chiefs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    [IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H)]
    (a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
      (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)))
    (c : SeedCartan (M := normalizer (L : Set G)) a.projection a.imageRepresentation a.vector)
    (X : Subgroup H) (hX : X ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hcard : Nat.card X = 3) (himage : X.map a.projection ≤ c.embedding.range)
    (hne : X.map a.projection ≠ ⊥) :
    ∃ hXN : X.map H.subtype ≤ normalizer (D.sourceOrbit : Set G),
      HasCount (sourceRepresentation (X.map H.subtype) D.sourceOrbit hXN) 3 ∧
      HasCount (sourceRepresentation (X.map H.subtype) D.sourceOrbit hXN).dual 3 := by
  obtain ⟨_,hNM,_,_⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  have hXN : X.map H.subtype ≤ normalizer (D.sourceOrbit : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    exact hNM (hX hx)
  have hcard' : Nat.card (X.map H.subtype) = 3 :=
    (Nat.card_congr (X.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm.trans hcard
  rcases D.sourceOrbit_m22_code_cubic_chiefs_or_centralizes h.toHypothesis1221 d
    (X.map H.subtype) hXN hcard' with hC | hc
  · exact (hne (c.image_eq_bot_of_centralizes a.vector_centralizer_fixed X himage hC)).elim
  · exact ⟨hXN,hc⟩

set_option backward.isDefEq.respectTransparency false in
/-- On the literal Cartan preimage, the faithful whole-span action covers
the same torus with its actual two-core as kernel. This supplies the
coprime kernel needed for subsequent odd-element lifting. -/
theorem sourceOrbit_m22_code_cartan_span_cover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    [IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H)]
    (a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
      (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)))
    (A : Subgroup H) (ha : EssentialChiefActor a A)
    (c : SeedCartan (M := normalizer (L : Set G)) a.projection a.imageRepresentation a.vector) :
    c.HasSpanCover (normalRepresentation ((conjugateSpan H D.sourceOrbit).subgroupOf H)) := by
  obtain ⟨s⟩ := SeriesOn.exists_series ((conjugateSpan H D.sourceOrbit).subgroupOf H)
  have hex : ∃ i : Fin s.series.length, ¬ s.Central i := by
    by_contra! hz
    have hz' := s.noncentralCount_eq_zero_iff.mpr hz
    have ht := D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s
    omega
  obtain ⟨i,hi⟩ := hex
  exact essential_cartan_span_cover a A ha c s i hi

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
