module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeCartanFieldFour
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.OriginalChiefFixedSpaces

/-!
# A large actual chief fixed space in the original M22-code Cartan branch

The constructed field-four Cartan supplies a cubic with three noncentral
constituents on the unchanged original orbit. Intersecting the two-factor
chief series of the conjugate span with that orbit gives an induced section
of cubic codimension at least three. Its canonical injection into the
corresponding actual chief factor lies in the fixed space of the original
sharp actor, so that fixed space has dimension at least three as well.
All covering maps, the original H-star choice, and the temporary inside-core
branch hypothesis are retained.

Source: Aschbacher--Smith, 3.1.9(6), printed p.578, used in8.2.2(1),
printed p.715, refs/quasithin.pdf. Natural fixed-space upper bounds and the
remaining symmetric-five exclusions are subsequent source steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option backward.isDefEq.respectTransparency false in
/-- The original Cartan cubic forces a large induced orbit section and a
large fixed space for the same original sharp actor on an actual chief factor. -/
theorem sourceOrbit_m22_code_cartan_large_chief_fixedSpace
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
    ∃ b : c.originalPreimage,
      orderOf (actionHom (normalRepresentation
        ((conjugateSpan H D.sourceOrbit).subgroupOf H)) (b : H)) = 3 ∧
      orderOf (a.projection (b : H)) = 3 ∧
      ∃ hn : ((b : H) : G) ∈ normalizer (D.sourceOrbit : Set G),
        orderOf (D.sourceOrbit.normalizerMonoidHom.rangeRestrict ⟨((b : H) : G),hn⟩) = 3 ∧
        ∀ s : SeriesOn ((conjugateSpan H D.sourceOrbit).subgroupOf H),
          ∃ i : Fin s.series.length, ¬ s.Central i ∧
            3 ≤ fixedCodim (originalSeedFactor H D.sourceOrbit s i) (zpowers ⟨(b : H),hn⟩) ∧
            3 ≤ Module.finrank (ZMod 2) (fixedSpace (s.factorRepresentation i) A) := by
  have hfour :=
    D.sourceOrbit_m22_code_cartan_field_four_chiefs h hmany hV hnon d hH hcore a A ha c
  exact cubic_large_fixedSpace H D.sourceOrbit
    (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)) A ha.centralizes
    c.originalPreimage a.projection hfour.2.2
    (fun s => D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
