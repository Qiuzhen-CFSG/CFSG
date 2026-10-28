module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeCubicMovement
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.NaturalChiefMovement

/-!
# The natural-coordinate obstruction for the original M22-code cubic

The constructed original field-four Cartan supplies a cubic moving six
binary dimensions on the unchanged orbit. In each original chief series,
its induced filtration therefore has a section moving at least three.
The original sharp actor forces that section's actual chief factor to have
dimension at least five. The native component-movement calculation rules
out a single or paired field-four marking on that same factor, with the
original Thompson fixed actor and original cubic in one component.

The final theorem constructs this obstruction from the original inside-core
nonsolvable branch, retaining the full original covering maps and the same
minimum sharp actor. No model-coordinate premise is added. To eliminate the
Cartan branch, the source B.6.9 markings must still be matched to this same
component and Thompson actor on every noncentral chief factor. The small
symmetric-five alternatives and subsequent M22-code exclusion also remain.

Source: Aschbacher--Smith, 3.1.9(6), printed p.578, used in8.2.2(1),
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
private theorem original_cartan_natural_obstruction
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
    CubicNaturalObstruction (V := D.sourceOrbit) (F := c.field.Carrier)
      ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H)
      c.originalPreimage a.projection := by
  have hfour :=
    D.sourceOrbit_m22_code_cartan_field_four_chiefs h hmany hV hnon d hH hcore a A ha c
  have hJ : ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H).map H.subtype ≤
      centralizer (D.sourceOrbit : Set G) := by
    rw [subgroupOf_map_subtype]
    exact inf_le_left.trans (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  exact cubic_natural_obstruction a ha _ hJ c.originalPreimage a.projection hfour.2.2
    (fun s => D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s) hfour.1

set_option backward.isDefEq.respectTransparency false in
/-- Under the original temporary inside-core branch, either the essential
module is small natural or an original cubic forces a chief factor of
dimension at least five and excludes its matching field-four coordinates.
No coordinate, movement or fixed-space estimate is assumed. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_natural_obstruction
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
              CubicNaturalObstruction (V := D.sourceOrbit) (F := c.field.Carrier)
                ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H)
                c.originalPreimage a.projection) := by
  obtain ⟨hU,a,A,hA,hAR,hquad,hmin,ha,hc⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_cartan h hmany hV hnon d hH hcore hns
  let := hU
  refine ⟨hU,a,A,hA,hAR,hquad,hmin,ha,?_⟩
  rcases hc with hs | ⟨c,_⟩
  · exact Or.inl hs
  · exact Or.inr ⟨c,D.original_cartan_natural_obstruction
      h hmany hV hnon d hH hcore a A ha c⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
