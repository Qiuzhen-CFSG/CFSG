module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFiniteModels
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.SpecificGroups.Alternating.EightComponent
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.Mathieu.M23.Properties.OuterRestriction
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import Theory.SpecificGroups.Held.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.ComponentFacts

/-!
# Cubic support in the original finite containing component

Each remaining finite carrier has a two-group of outer automorphisms.
The original smaller normalizer rank bound makes the centralizer of the
normal containing component have order prime to three. The outer
conjugation map therefore makes that containing component have index
prime to three in the same point quotient. Every three-subgroup of that
quotient, including its original elementary nine, lies in the component.

This locates the original cubic actors without assuming that the whole
ambient point quotient is simple or that its other components vanish.
It does not exclude the remaining proper finite embeddings.
Source: Aschbacher--Smith A.3.18 and15.3.23, pp.51--52 and1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

/-- All finite remaining carriers have two-group outer automorphism group.
The Rudvalis case uses simplicity inherited from the actual containing K. -/
theorem binary_three_finite_carrier_outer_two
    {A : Type*} [Group A] [Finite A] [IsSimpleGroup A]
    (hm : BinaryThreeFiniteSimpleCarrier A) : IsPGroup 2 (MulAut.Outer A) := by
  rcases hm with ⟨n,hn,⟨e⟩⟩ | ⟨n,hn,hm⟩ | ⟨name,hn,⟨e⟩⟩
  · rcases hn with rfl | rfl
    · exact alternatingGroup.SevenComponent.outer_two.of_equiv (MulAut.outerCongr e).symm
    · exact alternatingGroup.EightComponent.outer_two.of_equiv (MulAut.outerCongr e).symm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF
    let a := (e.trans (Atlas.fieldEquivPSL n (FiniteField.ringEquivOfCardEq hc))).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n))
    exact (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup hn).of_equiv
      (MulAut.outerCongr a).symm
  · rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Sporadic.Mathieu.m23_outer_isTwoGroup.of_equiv (MulAut.outerCongr e).symm
    · exact Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two.of_equiv
        (MulAut.outerCongr e).symm
    · exact Janko4.AdequateLocal.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm
    · have ho := Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map
        Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow
      exact ho.of_equiv (MulAut.outerCongr e).symm
    · exact Held.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm
    · let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
      exact Rudvalis.outer_isPGroup_two.of_equiv (MulAut.outerCongr e).symm

variable {X : Type*} [Group X] [Finite X]

private theorem binary_three_containing_centralizer_coprime
    {B K : Subgroup X} (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hr : primeRank 3 (normalizer (B : Set X)) ≤ 1) :
    Nat.Coprime 3 (Nat.card (centralizer (K : Set X))) := by
  let A := centralizer (K : Set X)
  have hc : A ≤ centralizer (B : Set X) := centralizer_le hBK
  have hn : A ≤ normalizer (B : Set X) := hc.trans (Subgroup.centralizer_le_normalizer _)
  let eSL := eB.trans Matrix.PSL3Two.equiv.symm
  have hz : Nat.Coprime 3 (Nat.card (center (B ⧸ pCore 2 B))) := by
    rw [Nat.card_congr (centerCongr eSL).toEquiv,Matrix.PSL3Two.center_eq_bot,card_bot]
    decide
  have hcomm : ⁅(pResidual 2 A).map A.subtype,B⁆ ≤ B.pCoreIn 2 := by
    have hb : ⁅A,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hc
    exact (commutator_mono (map_subtype_le _) le_rfl).trans (hb ▸ bot_le)
  have hsum := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) A B hn hcomm hz
  have hB : 1 ≤ primeRank 3 B := by
    have hq : 1 ≤ primeRank 3 (B ⧸ pCore 2 B) := by
      apply Theory.Quasithin.one_le_primeRank_of_dvd_card
      rw [Nat.card_congr eSL.toEquiv,Matrix.PSL3Two.card_SL]
      decide
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup] at hq
    exact hq
  have hu := (primeRank_mono 3 (sup_le hn B.le_normalizer)).trans hr
  have hA : primeRank 3 A = 0 := by omega
  exact Nat.prime_three.coprime_iff_not_dvd.mpr (PrimeRank.eq_zero_iff_not_dvd_card.mp hA)

/-- The original normal containing component has index prime to three;
the entire point quotient need not equal that component. -/
theorem binary_three_finite_containing_index_coprime_three
    {B K : Subgroup X} [K.Normal] [IsSimpleGroup K] (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hr : primeRank 3 (normalizer (B : Set X)) ≤ 1)
    (hm : BinaryThreeFiniteSimpleCarrier K) : Nat.Coprime 3 K.index := by
  have hC := binary_three_containing_centralizer_coprime hBK eB hr
  have hO : Nat.Coprime 3 (Nat.card (MulAut.Outer K)) := by
    obtain ⟨n,hn⟩ := (binary_three_finite_carrier_outer_two hm).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  let f : X →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp MulAut.conjNormal
  have hk : f.ker = K ⊔ centralizer (K : Set X) := by
    change ((QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      (MulAut.conjNormal : X →* MulAut K)).ker = _
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk',MulAut.conjNormal_comap_innerSubgroup]
  have hf : Nat.Coprime 3 f.ker.index := by
    rw [index_ker]
    exact hO.coprime_dvd_right f.range.card_subgroup_dvd_card
  rw [hk] at hf
  rw [←relIndex_mul_index (show K ≤ K ⊔ centralizer (K : Set X) from le_sup_left)]
  apply Nat.Coprime.mul_right _ hf
  rw [relIndex_sup_left]
  exact hC.coprime_dvd_right (relIndex_dvd_card _ _)

/-- Every actual three-subgroup of the point quotient lies in its same
normal containing component, including the original elementary nine. -/
theorem binary_three_three_subgroup_le_finite_containing
    {B K E : Subgroup X} [K.Normal] [IsSimpleGroup K] (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hr : primeRank 3 (normalizer (B : Set X)) ≤ 1)
    (hm : BinaryThreeFiniteSimpleCarrier K) (hE : IsPGroup 3 E) : E ≤ K := by
  have hi := binary_three_finite_containing_index_coprime_three hBK eB hr hm
  intro x hx
  obtain ⟨n,hn⟩ := hE ⟨x,hx⟩
  exact primeToResidual_le K hi (mem_primeToResidual_of_pow (congrArg E.subtype hn))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
