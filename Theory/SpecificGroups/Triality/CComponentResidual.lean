module
public import Theory.SpecificGroups.Triality.CubicComponentAction
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.GroupTheory.CComponent.CentralizerMovement
public import Theory.GroupTheory.PResidual.PrimeToQuotientLift

/-!
# Cubic residuals of C-components with binary triality quotient

The literal two-core image of the C-component is an ordinary component.
The triality fixed-nine theorem excludes outer cubic actors in the actual
rank-two ambient action and identifies this image with O^{3′}. Normality
and residual equality lift through O₂, whose order is prime to three.
This covers the genuine triality quotient even though its outer group has
an element of order three. The final result applies this identity in the
normalizer of a subgroup moved by a cubic residual.

Source: Aschbacher--Smith A.3.18 and 15.1.25(1),(3), printed pp.51--53,1102.
-/

public section
open Subgroup Theory.GroupTheory
namespace Triality.Standard
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

/-- The genuine triality outer group cannot satisfy an outer-two catalogue interface. -/
theorem binaryCarrier_outer_not_two (n : ℕ) (hn : 0 < n) :
    ¬ IsPGroup 2 (MulAut.Outer (BinaryCarrier n hn)) := by
  intro ho
  have hc := ho.orderOf_coprime (by decide : Nat.Coprime 2 3)
    (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn))
      (OddGraph.automorphism (binaryParameters n hn)))
  rw [OddGraph.automorphism_outer_order] at hc
  norm_num at hc

/-- The original C-component is the cubic residual, with no outer-two premise. -/
theorem cComponent_eq_primeToResidual_three
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hrG : primeRank 3 G ≤ 2)
    (n : ℕ) (hn : 0 < n) (e : (K ⧸ pCore 2 K) ≃* BinaryCarrier n hn) :
    K = primeToResidual 3 G := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let a : (K ⧸ pCore 2 K) ≃* B := cComponentTwoCoreQuotientEquiv hK
  let b : B ≃* BinaryCarrier n hn := a.symm.trans e
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv a
  have hB : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨(hK.map_quotient (pCore 2 G)).subnormal, inferInstance⟩
  have hzB : center B = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact b.map_eq_one_iff.mp
      ((binaryCarrier_center_eq_bot n hn).le ((centerCongr b) ⟨x,hx⟩).property)
  let j : (B ⧸ center B) ≃* BinaryCarrier n hn :=
    ((QuotientGroup.quotientMulEquivOfEq hzB).trans QuotientGroup.quotientBot).trans b
  have hrQ : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrG
  have he : B = primeToResidual 3 (G ⧸ pCore 2 G) :=
    (CubicComponentAction.component_eq_primeClosure_and_residual hrQ hB
      (by rw [hzB,card_bot]; decide) n hn j).2
  let : B.Normal := he.symm ▸ inferInstance
  let : K.Normal := cComponent_normal_of_quotient_normal hK (pCore 2 G) inferInstance
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact e.map_eq_one_iff.mp
      ((binaryCarrier_center_eq_bot n hn).le ((centerCongr e) ⟨x,hx⟩).property)
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 e]
    let E := ElementaryNine.subgroup (binaryParameters n hn) rfl
    let : IsElementaryAbelian 3 E := ElementaryNine.subgroup_elementary _ _
    exact IsElementaryAbelian.primeRank_ge_of_card E (ElementaryNine.card_subgroup _ _)
  apply eq_primeToResidual_of_coprime_quotient_image 3 (pCore 2 G) K _
    (hK.le_primeToResidual_three hz hr) he
  obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  rw [hm]
  exact (by decide : Nat.Coprime 3 2).pow_right m

/-- A cubic residual moving W excludes centralization by the triality C-component. -/
theorem cComponent_not_centralizes_of_cubic_movement
    {L H W A : Subgroup G} (hL : (L.subgroupOf H).IsCComponent)
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hCH : centralizer (W : Set G) ≤ H)
    (n : ℕ) (hn : 0 < n) (e : (L ⧸ pCore 2 L) ≃* BinaryCarrier n hn)
    (hN : primeRank 3 (normalizer (W : Set G)) ≤ 2)
    (hA : A ≤ normalizer (W : Set G))
    (hres : (primeToResidual 3 A).map A.subtype = A)
    (hmove : ⁅W,A⁆ ≠ ⊥) : ¬ L ≤ centralizer (W : Set G) := by
  intro hLC
  let N := normalizer (W : Set G)
  have hLN : L ≤ N := hLC.trans (Subgroup.centralizer_le_normalizer _)
  let B := L.subgroupOf N
  let a : B ≃* L := subgroupOfEquivOfLe hLN
  let b : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv b.symm
  have hB : B.IsCComponent := hL.in_normalizer_of_centralizes hLC hCH
  have he := cComponent_eq_primeToResidual_three hB hN n hn (b.trans e)
  have hAL : A ≤ L := by
    have hh := embedded_primeToResidual_mono 3 hA
    rw [hres,←he,map_subgroupOf_eq_of_le hLN] at hh
    exact hh
  apply hmove
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hAL.trans hLC)

end Triality.Standard
