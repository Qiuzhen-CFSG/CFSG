module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import Theory.GroupTheory.SubgroupProductCard
public import Mathlib.FieldTheory.Finiteness

/-!
# The degree of the literal vector quotient in 15.3.56

The two conjugate core intersections have the same order and meet in a
four-group. Their product is P, of order 2^(4s+4). Hence W has order
2^(2s+3). The index-four U-image gives |U|=2^(2s+5), and dividing by the
original central line Z gives binary degree 2(s+2).

Source: Aschbacher–Smith, 15.3.53–54 and 15.3.56(2), printed pp.1146–1147.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition
variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)

/-- Counting the actual product and its four-element overlap determines W. -/
theorem card_pairW (g : G) (s : ℕ)
    (hproduct : (pairP Z ZS g : Set G) = (pairW Z ZS g : Set G) *
      (rightConjugate (pairW Z ZS g) g : Set G))
    (hinter : Nat.card (pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g : Subgroup G) = 4)
    (hcard : Nat.card (pairP Z ZS g) = 2 ^ (4 * s + 4)) :
    Nat.card (pairW Z ZS g) = 2 ^ (2 * s + 3) := by
  have hh := card_set_mul_mul_card_inf (pairW Z ZS g) (rightConjugate (pairW Z ZS g) g)
  have hg : Nat.card (rightConjugate (pairW Z ZS g) g) = Nat.card (pairW Z ZS g) := by
    exact card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [← hproduct, hinter, hg] at hh
  change Nat.card (pairP Z ZS g) * 4 = _ at hh
  rw [hcard] at hh
  have hexp : 2 ^ (4 * s + 4) * 4 = (2 ^ (2 * s + 3)) ^ 2 := by
    calc
      2 ^ (4 * s + 4) * 4 = 2 ^ (4 * s + 4) * 2 ^ 2 := rfl
      _ = 2 ^ ((4 * s + 4) + 2) := (pow_add 2 _ _).symm
      _ = (2 ^ (2 * s + 3)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
  rw [hexp, ← pow_two] at hh
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) hh.symm

/-- The rank in source 15.3.56(2), on precisely the recognition carrier U/Z. -/
theorem vector_dimension_of_pair (g : G) (s : ℕ)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (hZ : Z ≤ closureU Z ZS) (hZcard : Nat.card Z = 2)
    (hproduct : (pairP Z ZS g : Set G) = (pairW Z ZS g : Set G) *
      (rightConjugate (pairW Z ZS g) g : Set G))
    (hinter : Nat.card (pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g : Subgroup G) = 4)
    (hcard : Nat.card (pairP Z ZS g) = 2 ^ (4 * s + 4))
    (hindex : (pairW Z ZS g).relIndex (closureU Z ZS) = 4) :
    Module.finrank (ZMod 2) (Space Z ZS) = 2 * (s + 2) := by
  have hW := card_pairW Z ZS g s hproduct hinter hcard
  have hU := relIndex_mul_relIndex (⊥ : Subgroup G) (pairW Z ZS g)
    (closureU Z ZS) bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, hW, hindex] at hU
  have hcZ : Nat.card (Z.subgroupOf (closureU Z ZS)) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZ).toEquiv).trans hZcard
  have hQ := card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf (closureU Z ZS))
  rw [hcZ, ← hU] at hQ
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space Z ZS)
  have hc : Nat.card (VectorQuotient Z ZS) = 2 ^ Module.finrank (ZMod 2) (Space Z ZS) :=
    (Nat.card_congr (Additive.toMul : Space Z ZS ≃ VectorQuotient Z ZS)).symm.trans
      (by simpa only [Nat.card_zmod] using hd)
  rw [hc] at hQ
  have he : 2 ^ (2 * s + 3) * 4 = 2 ^ (2 * (s + 2)) * 2 := by
    rw [show 2 * (s + 2) = (2 * s + 3) + 1 by omega, pow_add]
    ring
  rw [he] at hQ
  exact Nat.pow_right_injective (by decide : 1 < 2)
    (Nat.mul_right_cancel (by decide : 0 < 2) hQ.symm)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
