module

public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.GroupAction.CoprimeFixedCardinality
public import Theory.Frattini.PGroup
public import Theory.GroupAction.ThreeFiveBinaryFixed

/-!
# A three-by-five action forces eight five-fixed points

Let H have a three-subgroup B and a complement A of order five, and let
H act on a finite two-group K. The action is coprime, and a faithful
elementary abelian B-action stays faithful on K/Φ(K).

When B is nontrivial elementary abelian and A acts fixed-point-freely on B,
the binary fixed-point theorem gives
4 |C_{K/Φ(K)}(H)| ≤ |C_{K/Φ(K)}(A)|. The reduction below lifts this ratio
to K by multiplying the fixed quotient and fixed kernel orders. An
H-fixed involution then contributes the factor two, regardless of whether
it lies in Φ(K). The reduction itself does not require that A act freely
on B; that hypothesis belongs to the binary representation inequality.

Source motivation: Thompson VI, printed p.630, final four-group
contradiction. All actions and fixed subgroups below are actual group
actions; no character data are substituted for them.
-/

namespace ThreeFiveAction

/-- Complementary three- and five-subgroups have order coprime to a two-group. -/
public theorem coprime_card
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (hK : IsPGroup 2 K) (B A : Subgroup H)
    (hB : IsPGroup 3 B) (hA : Nat.card A = 5) (hBA : B.IsComplement' A) :
    Nat.Coprime (Nat.card H) (Nat.card K) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  obtain ⟨k, hk⟩ := hK.exists_card_eq
  rw [← hBA.card_mul_card, hb, hA, hk]
  exact ((by decide : Nat.Coprime 3 2).pow_left b |>.mul_left
    (by decide : Nat.Coprime 5 2)).pow_right k

/-- Faithfulness of the three-subgroup survives on the actual Frattini quotient. -/
public theorem faithful_frattini
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    [MulDistribMulAction H K]
    (hK : IsPGroup 2 K) (B : Subgroup H) [IsElementaryAbelian 3 B]
    [FaithfulSMul B K] :
    letI : MulDistribMulAction H (K ⧸ frattini K) :=
      quotientMulDistribMulAction (frattini K) (isInvariant_of_characteristic (frattini K))
    FaithfulSMul B (K ⧸ frattini K) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 3 B).exists_card_eq
  exact MonoidHom.faithfulSMul_frattini_of_coprime hK
    (by rw [hb]; exact (by decide : Nat.Coprime 3 2).pow_left b)

/-- The binary Frattini fixed-point ratio implies at least eight five-fixed points. -/
public theorem eight_le_card_fixed_of_frattini_ratio
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    [MulDistribMulAction H K]
    (hK : IsPGroup 2 K) (B A : Subgroup H)
    (hB : IsPGroup 3 B) (hA : Nat.card A = 5) (hBA : B.IsComplement' A)
    (y : K) (hy : orderOf y = 2) (hfix : ∀ h : H, h • y = y) :
    letI : MulDistribMulAction H (K ⧸ frattini K) :=
      quotientMulDistribMulAction (frattini K) (isInvariant_of_characteristic (frattini K))
    4 * Nat.card (FixedPoints.subgroup H (K ⧸ frattini K)) ≤
        Nat.card (FixedPoints.subgroup A (K ⧸ frattini K)) →
      8 ≤ Nat.card (FixedPoints.subgroup A K) := by
  let : Group.IsNilpotent K := hK.isNilpotent
  have hyne : y ≠ 1 := by intro heq; simp [heq] at hy
  exact FixedPoints.two_mul_le_card_of_quotient_ratio inferInstance
    (coprime_card hK B A hB hA hBA) A (frattini K)
    (isInvariant_of_characteristic (frattini K)) 4 y hyne hfix

/-- Let H = B ⋊ A act on a finite two-group K, where B is a nontrivial
elementary abelian three-group acting faithfully on K and A has order five
and acts fixed-point-freely on B. An H-fixed involution in K forces A to
fix at least eight elements of K. -/
public theorem eight_le_card_fixed
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    [MulDistribMulAction H K]
    (hK : IsPGroup 2 K) (B A : Subgroup H)
    [B.Normal] [IsElementaryAbelian 3 B] [FaithfulSMul B K]
    (hB : B ≠ ⊥) (hA : Nat.card A = 5) (hBA : B.IsComplement' A)
    (hfree : B ⊓ Subgroup.centralizer (A : Set H) = ⊥)
    (y : K) (hy : orderOf y = 2) (hfix : ∀ h : H, h • y = y) :
    8 ≤ Nat.card (FixedPoints.subgroup A K) := by
  let : Fact (IsPGroup 2 K) := ⟨hK⟩
  let V := K ⧸ frattini K
  let : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  let : MulDistribMulAction H V :=
    quotientMulDistribMulAction (frattini K) (isInvariant_of_characteristic (frattini K))
  let : FaithfulSMul B V := faithful_frattini hK B
  apply eight_le_card_fixed_of_frattini_ratio hK B A
    (IsElementaryAbelian.isPGroup 3 B) hA hBA y hy hfix
  exact four_mul_card_fixed_le B A hB hA hBA hfree

end ThreeFiveAction
