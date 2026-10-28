module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.RankOneModels.FiniteExclusions
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M12.ValueBoundParabolics.Supplement
public import Theory.Mathieu.M12.TwoCentralInvolutions.CentralizerOrder
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.Mathieu.M23.Properties.OuterRestriction
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoCentral
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InvolutionCentralizerOdd
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.CubicOrder
public import Theory.SpecificGroups.Held.ComponentFacts
public import Theory.SpecificGroups.Held.OrdinaryLocal
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# The nine non-J₄ sporadic centralizer bounds

The literal Mathieu, J₂, HS, Held and Rudvalis models have two-central
involution centralizers of order indivisible by nine. The Held argument
retains the Sylow-center marking to select the correct involution class;
HS uses the actual proper full-Sylow overgroup bound. The model outer
groups are two-groups, with simplicity inherited where the intrinsic
Rudvalis theorem requires it.

These are exactly the model facts consumed by the original 15.2.15
ordinary-component argument. J₄ is retained for its different residual
section argument. Every imported model calculation retains its ATLAS
attribution and actual carrier; no new finite computation is introduced.
Source: Aschbacher--Smith, printed p.1118, refs/quasithin.pdf;
GLS3 involution-centralizer tables cited by the imported model modules.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents.SporadicBounds
open ClassificationModels Sporadic.Mathieu

private theorem card_centralizer_of_isConj {D : Type*} [Group D] {x y : D}
    (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set D)) = Nat.card (centralizer ({y} : Set D)) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  have he : (MulAut.conj g) x = y := hg
  have hh := Nat.card_congr (MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj x)).toEquiv
  rw [MulAut.congr_conj,he,MulAut.fixedSubgroup_conj,MulAut.fixedSubgroup_conj] at hh
  exact hh

private theorem m11_not_nine (t : M11) (ht : orderOf t = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set M11)) := by
  rw [card_centralizer_of_isConj (m11_involution_isConj_generatorA t ht)]
  change ¬9 ∣ Nat.card m11InvolutionCentralizer
  rw [m11_involutionCentralizer_card]
  decide

private theorem j2_not_nine (t : Sporadic.LeechRelated.J2.Carrier) (ht : orderOf t = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set Sporadic.LeechRelated.J2.Carrier)) := by
  rcases Sporadic.LeechRelated.J2.InnerInvolutionCores.involution_fusion t ht with h | h
  · rw [←card_centralizer_of_isConj h,
      Nat.card_congr Sporadic.LeechRelated.J2.InnerInvolutionCores.a_centralizer_equiv.toEquiv,
      Nat.card_prod,nat_card_alternatingGroup,Nat.card_fin]
    norm_num [Sporadic.LeechRelated.J2.InnerInvolutionCores.E4,
      Sporadic.LeechRelated.J2.InnerInvolutionCores.C2,Nat.card_fun,Nat.factorial]
  · rw [←card_centralizer_of_isConj h]
    change ¬9 ∣ Nat.card Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁]
    decide

private theorem held_not_nine (t : Held.He) (ht : orderOf t = 2) (hc : TwoCentral t) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set Held.He)) := by
  let z : Held.He := Held.TwoLocalCandidates.max5First ^ 4
  obtain ⟨R,hR⟩ := Held.RankOneLocalPair.exists_sylow_le_max5
  have hzC : z ∈ centralizer (R : Set Held.He) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp
      (Held.TwoLocalCandidates.CentralInvolutionBounds.max5_le_centralizer (hR hx))
  have hzR : z ∈ R := by
    have hh := centralizer_le_normalizer (R : Set Held.He) hzC
    rwa [Held.LocalPairs.SylowGeometry.Calculations.inner_self_normalizing R] at hh
  have hz : TwoCentral z := ⟨R,hzR,mem_center_iff.mpr (fun x => Subtype.ext (hzC x x.property))⟩
  have ho : orderOf z = 2 := Held.TwoLocalCandidates.CentralInvolutionBounds.orderOf_centralInvolution
  have he := hc.isConj_of_center_card_two hz
    (by intro he; rw [he,orderOf_one] at ht; omega)
    (by intro he; rw [he,orderOf_one] at ho; omega)
    Held.LocalPairs.SylowGeometry.Calculations.inner_center_card
  rw [card_centralizer_of_isConj he]
  change ¬9 ∣ Nat.card (centralizer ({Held.TwoLocalCandidates.max5First ^ 4} : Set Held.He))
  rw [Held.InvolutionFixedData.TwoB.centralizer_eq_max5,Held.InvolutionFixedData.TwoB.max5_card]
  decide

/-- The nine actual outer groups are two-groups. -/
theorem outer_two (name : SporadicName) (hn : name ≠ .j3) (hj : name ≠ .j4)
    [IsSimpleGroup name.Carrier] : IsPGroup 2 (MulAut.Outer name.Carrier) := by
  cases name with
  | m11 => exact m11_outer_isPGroup_two
  | m12 => exact M12SmallPair.ValueBoundParabolics.outer_isPGroup_two
  | m22 =>
    exact IsPGroup.of_card_dvd_pow (G := MulAut.Outer M22) (n := 1)
      (by simpa only [pow_one] using M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)
  | m23 => exact m23_outer_isTwoGroup
  | m24 => exact M24OuterRestriction.outer_isPGroup_two
  | j2 => exact Sporadic.LeechRelated.J2.outer_isTwoGroup
  | j3 => exact (hn rfl).elim
  | j4 => exact (hj rfl).elim
  | hs =>
    exact IsPGroup.of_card_dvd_pow (G := MulAut.Outer Sporadic.LeechRelated.HS.Carrier) (n := 1)
      (by simpa only [pow_one] using Sporadic.LeechRelated.HS.outer_card_dvd_two)
  | he => exact Held.outer_isPGroup_two
  | ru =>
    let : IsSimpleGroup Rudvalis.Model := ‹IsSimpleGroup SporadicName.ru.Carrier›
    exact Rudvalis.outer_isPGroup_two

private theorem m12_not_nine (t : M12) (ht : orderOf t = 2) (hc : TwoCentral t) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set M12)) := by
  rw [M12Involutions.card_centralizer_of_twoCentral t ht hc]
  decide

private theorem m22_not_nine (t : M22) (ht : orderOf t = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set M22)) := by
  rw [M22FourNormalizers.involution_centralizer_card t ht]
  decide

private theorem m23_not_nine (t : M23) (ht : orderOf t = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set M23)) := by
  obtain ⟨e⟩ := M23Geometry.InvolutionCentralizer.centralizer_equiv_representative ht
  rw [Nat.card_congr e.toEquiv,M23Geometry.involutionRepresentative_centralizer_card]
  decide

private theorem m24_not_nine (t : M24) (ht : orderOf t = 2) (hc : TwoCentral t) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set M24)) := by
  rw [M24InvolutionCentralizers.card_centralizer_of_twoCentral t ht hc]
  decide

private theorem hs_not_nine (t : Sporadic.LeechRelated.HS.Carrier)
    (ht : orderOf t = 2) (hc : TwoCentral t) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set Sporadic.LeechRelated.HS.Carrier)) := by
  obtain ⟨R,hR,hRc⟩ := hc
  apply Sporadic.LeechRelated.HS.SylowOvergroups.proper_overgroup_not_nine_dvd R
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hRc ⟨x,hx⟩))
  · intro he
    have htz : t ∈ center Sporadic.LeechRelated.HS.Carrier := by
      rw [mem_center_iff]
      intro x
      exact mem_centralizer_singleton_iff.mp (he ▸ mem_top x)
    rw [Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot,mem_bot] at htz
    rw [htz,orderOf_one] at ht
    omega

/-- The original two-central marking excludes an elementary nine in the centralizer. -/
theorem centralizer_not_nine (name : SporadicName) (hn : name ≠ .j3) (hj : name ≠ .j4)
    (t : name.Carrier) (ht : orderOf t = 2) (hc : TwoCentral t) :
    ¬ 9 ∣ Nat.card (centralizer ({t} : Set name.Carrier)) := by
  cases name with
  | m11 => exact m11_not_nine t ht
  | m12 => exact m12_not_nine t ht hc
  | m22 => exact m22_not_nine t ht
  | m23 => exact m23_not_nine t ht
  | m24 => exact m24_not_nine t ht hc
  | j2 => exact j2_not_nine t ht
  | j3 => exact (hn rfl).elim
  | j4 => exact (hj rfl).elim
  | hs => exact hs_not_nine t ht hc
  | he => exact held_not_nine t ht hc
  | ru => exact Rudvalis.InvolutionCentralizers.centralizer_not_nine t ht
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents.SporadicBounds
