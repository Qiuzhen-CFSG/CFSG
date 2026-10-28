module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeCartanFieldFour
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.OriginalChiefMovement

/-!
# Cubic movement on the original Thompson-fixed chief sections

The original Thompson subgroup centralizes the chosen orbit. The filtration
of that orbit by the two noncentral chief factors therefore injects into
their Thompson-fixed spaces. The actual field-four Cartan cubic moves six
binary dimensions on the orbit, so its movement on at least one of these
fixed spaces has dimension at least three. Both the original cubic lift
and all original covering maps are retained.

This formulation preserves passive coordinates in a paired natural action;
the source upper bound concerns movement by the chosen component cubic,
not the dimension of the entire Thompson-fixed space. The natural upper
bound and the symmetric-five exclusions still need to be established.
Source: Aschbacher--Smith, 3.1.9(6), printed p.578, used in8.2.2(1), p.715,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement Chapter8.MathieuShadowRows Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option backward.isDefEq.respectTransparency false in
/-- The original Cartan cubic moves at least three dimensions in an actual
chief fixed space of the original Thompson subgroup. -/
theorem sourceOrbit_m22_code_cartan_thompson_movement
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
    CubicFixedMovement H D.sourceOrbit
      ((Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H)
      c.originalPreimage a.projection := by
  have hfour :=
    D.sourceOrbit_m22_code_cartan_field_four_chiefs h hmany hV hnon d hH hcore a A ha c
  have hJ : ((Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H).map H.subtype ≤
      centralizer (D.sourceOrbit : Set G) := by
    rw [subgroupOf_map_subtype]
    exact inf_le_left.trans (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  exact cubic_large_fixed_movement H D.sourceOrbit
    (hcore.trans (ChapterD.UniqueFactor.twoCore_le H))
    ((Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H) hJ
    c.originalPreimage a.projection hfour.2.2
    (fun s => D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s)

set_option backward.isDefEq.respectTransparency false in
/-- The original nonsolvable inside-core branch constructs either its small
natural action or a Cartan whose cubic has large movement on an actual
Thompson-fixed chief space. The original sharp actor and full covers remain. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_movement_alternatives
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
          (ChapterB.ChiefSmallNaturalAlternatives a.imageRepresentation ∨
            ∃ c : SeedCartan (M := normalizer (L : Set G))
                a.projection a.imageRepresentation a.vector,
              CubicFixedMovement H D.sourceOrbit
                ((Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H)
                c.originalPreimage a.projection) := by
  obtain ⟨hU,a,A,hA,hAR,hquad,hmin,ha,hc⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_cartan h hmany hV hnon d hH hcore hns
  let := hU
  refine ⟨hU,a,A,hA,hAR,hquad,hmin,ha,?_⟩
  rcases hc with hs | ⟨c,_⟩
  · exact Or.inl hs
  · exact Or.inr ⟨c,D.sourceOrbit_m22_code_cartan_thompson_movement
      h hmany hV hnon d hH hcore a A ha c⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
