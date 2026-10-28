module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeCartanFieldFour
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.NaturalChiefSelection
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Excluding the original M22-code larger natural chief rows

The original nonsolvable inside-core construction supplies the same minimum
sharp actor, essential seed action and Cartan alternative. The original
Thompson subgroup centralizes the unchanged orbit, contains that actor and
is invariant under the prescribed Sylow. The constructed field-four Cartan
has three noncentral factors on the original orbit, whereas its two original
chief intervals allow at most two. The proved matching natural coordinates
give this contradiction without any additional action or model premise.

Consequently the essential action and every original noncentral chief factor
have small natural markings. The symmetric-five exclusions, exceptional
inside-core centralizer argument and subsequent M22-code exclusion remain
separate source steps; this does not assert the final Mathieu selection.
Source: Aschbacher--Smith, 3.1.9(6), printed p.578, used in 8.2.2(1),
printed p.715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option backward.isDefEq.respectTransparency false in
/-- The original marked M22-code branch has small natural essential action,
with the same minimum sharp actor and no Cartan or coordinate premise. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_small_natural
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
          EssentialChiefActor a A ∧ ChapterB.ChiefSmallNaturalAlternatives a.imageRepresentation := by
  obtain ⟨hU,a,A,hA,hAR,hquad,hmin,ha,hc⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_cartan h hmany hV hnon d hH hcore hns
  let := hU
  refine ⟨hU,a,A,hA,hAR,hquad,hmin,ha,?_⟩
  rcases hc with hs | ⟨c,_⟩
  · exact hs
  let S := T.subtype hH.1.1.2
  let J := elementaryAbelianMaxJ (S : Subgroup H)
  have hAJ : A ≤ J := le_sSup hA
  have hJ : (S : Subgroup H) ≤ normalizer (J : Set H) :=
    (S : Subgroup H).le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  have hJT : J.map H.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      show (S : Subgroup H).map H.subtype = (T : Subgroup G) from
        map_subgroupOf_eq_of_le hH.1.1.2]
  have hJC : J.map H.subtype ≤ centralizer (D.sourceOrbit : Set G) :=
    hJT ▸ D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon
  have hfour := D.sourceOrbit_m22_code_cartan_field_four_chiefs h hmany hV hnon d hH hcore a A ha c
  exact essential_small_of_cubic_chiefs a ha
    (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1) J hJ hAJ hJC c hfour.1 hfour.2.2
    (fun s => D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s)

set_option backward.isDefEq.respectTransparency false in
/-- The original chief series now has only small natural rows. The literal
common actor still offends sharply on every noncentral factor. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_chief_small
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
      ∃ A ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
        ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
          ChapterB.ChiefSmallNaturalAlternatives
            (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)) ∧
          IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
            (actionSubgroup (s.factorRepresentation i) A) ∧
          rank (actionSubgroup (s.factorRepresentation i) A) =
            fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
              (actionSubgroup (s.factorRepresentation i) A) := by
  obtain ⟨hU,a,A,hA,_,_,_,ha,hs⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_small_natural h hmany hV hnon d hH hcore hns
  let := hU
  refine ⟨hU,A,hA,?_⟩
  intro s i hi
  exact ⟨(ha.small_iff s i hi).mp hs,(ha.chief s i hi).1,ha.chief_sharp s i hi⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
