module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeCartan
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CartanCubicCounts
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair

/-!
# Constructed cubic actions in the original M22-code Cartan branch

Use the canonical essential source action and the same minimum sharp actor.
The already proved whole-span cover has a two-group kernel; its Cartan
therefore supplies a genuine cubic on that span. Restriction is a nontrivial
cubic in the full automizer of the unchanged original orbit. The original
M22 marking proves chief count three on its code and dual. We keep the
original representative in the full preimage, without asserting it has
order three upstairs. The full span-to-orbit restriction is also constructed.

Under the three-group Cartan condition, the field is F₄ and the Cartan
has order three, so the divisibility premise of this construction follows.
That three-group condition remains to be proved by the original3.1.9(6)
centralization argument. The two-factor upper count, symmetric-five sieve,
inside-core exclusion and final same-orbit selection remain subsequent
source obligations. These statements do not assert the selection theorem.

Source: Aschbacher--Smith, original3.1.9(6), printed p.578, applied in8.2.2(1),
printed p.715, refs/quasithin.pdf. The private import reuses only the already
proved original H-star normalization, with its public boundary unchanged.
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
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option backward.isDefEq.respectTransparency false in
/-- Construct the cubic on the original span and orbit, and derive the
original code and dual chief counts from their actual full markings. -/
theorem sourceOrbit_m22_code_cartan_constructed_cubic_chiefs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    [hU : IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H)]
    (a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
      (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)))
    (A : Subgroup H) (ha : EssentialChiefActor a A)
    (c : SeedCartan (M := normalizer (L : Set G)) a.projection a.imageRepresentation a.vector)
    (hthree : 3 ∣ Nat.card c.field.Carrierˣ) :
    CubicOrbitChiefs (V := D.sourceOrbit) c.originalPreimage a.projection := by
  have hN := D.m24_hstar_normalizes h hmany hV hnon hH
  have hc := D.sourceOrbit_m22_code_cartan_span_cover h hmany hV hnon d hH hcore a A ha c
  obtain ⟨f,hf,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  exact marked_cartan_cubic_chiefs c (hcore.trans (ChapterD.UniqueFactor.twoCore_le H))
    a.vector_centralizer_fixed hN hc hthree f hf
    (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) hE

set_option backward.isDefEq.respectTransparency false in
/-- Under the original three-group Cartan premise, its field is four and
its constructed cubic has three chief factors on the same code and dual. -/
theorem sourceOrbit_m22_code_three_group_cartan_chiefs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    [hU : IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H)]
    (a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
      (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)))
    (A : Subgroup H) (ha : EssentialChiefActor a A)
    (c : SeedCartan (M := normalizer (L : Set G)) a.projection a.imageRepresentation a.vector)
    (hthree : IsPGroup 3 c.field.Carrierˣ) :
    Nat.card c.field.Carrier = 4 ∧ Nat.card c.field.Carrierˣ = 3 ∧
      CubicOrbitChiefs (V := D.sourceOrbit) c.originalPreimage a.projection := by
  have hfour := NormalizedShadowRows.binary_field_card_four_of_units_three_group
    c.field.Carrier c.large hthree
  have hcard : Nat.card c.field.Carrierˣ = 3 := by rw [Nat.card_units,hfour]
  exact ⟨hfour,hcard,D.sourceOrbit_m22_code_cartan_constructed_cubic_chiefs
    h hmany hV hnon d hH hcore a A ha c (by rw [hcard])⟩

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the full original span-image cover to the full automizer of
the same original orbit, retaining every original conjugation map. -/
theorem sourceOrbit_m22_code_cartan_orbit_restriction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    [hU : IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H)]
    (a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
      (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)))
    (c : SeedCartan (M := normalizer (L : Set G)) a.projection a.imageRepresentation a.vector)
    : SpanOrbitRestriction (V := D.sourceOrbit) c.originalPreimage := by
  have hN := D.m24_hstar_normalizes h hmany hV hnon hH
  apply span_orbit_restriction (hcore.trans (ChapterD.UniqueFactor.twoCore_le H))
  rintro _ ⟨y,hy,rfl⟩
  exact hN hy.1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
