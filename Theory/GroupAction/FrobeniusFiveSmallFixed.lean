module

public import FeitThompson.Wielandt

/-!
# A three-kernel acting on a two-group with few five-fixed points

Suppose a Frobenius group with three-group kernel and complement of order
five acts on a finite two-group. If the whole actor fixes at least two
elements and the complement fixes at most four, the kernel acts trivially.

Wielandt's fixed-point product formula says that the kernel fixed-subgroup
index is the fifth power of the complement/common fixed-subgroup index.
The latter index is at most two. The resulting index 32 is impossible by
three-group orbit counting modulo three; hence the index is one.

Source: Wielandt's fixed-point theorem (Huppert--Blackburn XI, 12.4),
formalized in `FeitThompson.Wielandt`; the numerical specialization supplies
the odd-local exclusion in Thompson VI, printed p.630.
-/

open Subgroup
universe u
namespace Wielandt

private theorem frobenius_fixed_card_identity
    {H V : Type u} [Group H] [Finite H] [Group V] [Finite V]
    [MulDistribMulAction H V] (K A : Subgroup H)
    (hfrob : IsFrobeniusGroupWithKernelComplement K A)
    (hcop : Nat.Coprime (Nat.card V) (Nat.card H))
    (hsolv : Group.IsSolvable V) :
    let _ : MulDistribMulAction K V := MulDistribMulAction.compHom V K.subtype
    let _ : MulDistribMulAction A V := MulDistribMulAction.compHom V A.subtype
    Nat.card V * Nat.card (fixedPointSubgroup H V) ^ Nat.card A =
      Nat.card (fixedPointSubgroup K V) *
        Nat.card (fixedPointSubgroup A V) ^ Nat.card A := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let c : Subgroup H → ℕ := fun B =>
    let _ : MulDistribMulAction B V := MulDistribMulAction.compHom V B.subtype
    Nat.card (fixedPointSubgroup B V)
  have hprod := fixedPointSubgroup_product_card_eq_of_coeff_sum_eq
    (G := H) (V := V) (ι := FrobeniusProductIndex K) hcop hsolv
    (frobeniusProductSubgroup K A)
    (frobeniusProductLeftCoeff K) (frobeniusProductRightCoeff K)
    (frobeniusProduct_coeff_sum_eq K A hfrob)
  have hTopC : c ⊤ = Nat.card (fixedPointSubgroup H V) := by
    dsimp [c]
    rw [fixedPointSubgroup_top_subgroup_eq]
  have hBotC : c ⊥ = Nat.card V := by
    dsimp [c]
    rw [fixedPointSubgroup_bot_subgroup_eq_top, card_top]
  have hConjC : ∀ k : K, c (A.conjBy (k : H)) = c A := by
    intro k
    exact (Nat.card_congr (fixedPointSubgroup_conjByEquiv A (k : H))).symm
  change (∏ i : FrobeniusProductIndex K,
      c (frobeniusProductSubgroup K A i) ^
        (frobeniusProductLeftCoeff K i * Nat.card (frobeniusProductSubgroup K A i))) =
    (∏ i : FrobeniusProductIndex K,
      c (frobeniusProductSubgroup K A i) ^
        (frobeniusProductRightCoeff K i * Nat.card (frobeniusProductSubgroup K A i))) at hprod
  have hprod' : c ⊤ ^ Nat.card H * Nat.card V ^ Nat.card K =
      (c A ^ Nat.card A) ^ Nat.card K * c K ^ Nat.card K := by
    simpa [Fintype.prod_sum_type, Fin.prod_univ_three,
      frobeniusProductSubgroup, frobeniusProductLeftCoeff, frobeniusProductRightCoeff,
      hBotC, hConjC, natCard_conjBy_eq, ← Nat.card_eq_fintype_card, mul_comm] using hprod
  have hc := hfrob.isComplement'.card_mul_card
  rw [← hc, mul_comm (Nat.card K), pow_mul, ← mul_pow, ← mul_pow] at hprod'
  have he := pow_left_injective Nat.card_pos.ne' hprod'
  rw [hTopC] at he
  simpa only [c, mul_comm] using he
end Wielandt

namespace Wielandt
private theorem card_eq_of_fifth_power_relation {v k a h : ℕ}
    (hv : 0 < v) (h2 : ¬ 3 ∣ k) (hmod : v % 3 = k % 3)
    (ha : a ≤ 4) (hh : 2 ≤ h) (hha : h ∣ a)
    (hid : v * h ^ 5 = k * a ^ 5) : v = k := by
  obtain ⟨d, hd⟩ := hha
  have hap : 0 < a := by
    by_contra! hz
    have hz0 : a = 0 := by omega
    rw [hz0] at hid
    have : 0 < v * h ^ 5 := Nat.mul_pos hv (pow_pos (by omega) _)
    simp at hid
    omega
  have hdpos : 0 < d := by nlinarith
  have hdle : d ≤ 2 := by nlinarith
  have heq : v = k * d ^ 5 := by
    rw [hd, mul_pow, ← mul_assoc, mul_right_comm k] at hid
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by omega) 5) hid
  interval_cases d
  · simpa using heq
  · have hbad : 3 ∣ k := by
      rw [heq, Nat.mul_mod] at hmod
      norm_num at hmod
      exact Nat.dvd_of_mod_eq_zero (by omega)
    exact (h2 hbad).elim

/-- A Frobenius three-kernel fixes the whole two-group when five-fixed
points have order at most four and common fixed points are nontrivial. -/
public theorem three_kernel_fixes_two_group_of_small_five_fixed
    {H V : Type u} [Group H] [Finite H] [Group V] [Finite V]
    [MulDistribMulAction H V] (K A : Subgroup H)
    (hfrob : IsFrobeniusGroupWithKernelComplement K A)
    (hK : IsPGroup 3 K) (hA : Nat.card A = 5) (hV : IsPGroup 2 V)
    (hcommon : 2 ≤ Nat.card (fixedPointSubgroup H V))
    (hsmall :
      let _ : MulDistribMulAction A V := MulDistribMulAction.compHom V A.subtype
      Nat.card (fixedPointSubgroup A V) ≤ 4) :
    let _ : MulDistribMulAction K V := MulDistribMulAction.compHom V K.subtype
    fixedPointSubgroup K V = ⊤ := by
  let _ : MulDistribMulAction A V := MulDistribMulAction.compHom V A.subtype
  let _ : MulDistribMulAction K V := MulDistribMulAction.compHom V K.subtype
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Group.IsNilpotent V := hV.isNilpotent
  have hcop : Nat.Coprime (Nat.card V) (Nat.card H) := by
    rw [← hfrob.isComplement'.card_mul_card, hA]
    apply Nat.Coprime.mul_right
    · obtain ⟨n, hn⟩ := hV.exists_card_eq
      obtain ⟨m, hm⟩ := hK.exists_card_eq
      rw [hn, hm]
      exact (by decide : Nat.Coprime 2 3).pow n m
    · obtain ⟨n, hn⟩ := hV.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 2 5).pow_left n
  have hid := frobenius_fixed_card_identity K A hfrob hcop inferInstance
  rw [hA] at hid
  have hle : fixedPointSubgroup H V ≤ fixedPointSubgroup A V := by
    intro v hv a
    exact hv (a : H)
  have hha := card_dvd_of_le hle
  have h2 : ¬ 3 ∣ Nat.card (fixedPointSubgroup K V) := by
    obtain ⟨n, hn⟩ := (hV.to_subgroup (fixedPointSubgroup K V)).exists_card_eq
    rw [hn]
    exact fun h => (by decide : ¬ 3 ∣ 2)
      ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3)) h)
  have hmod := hK.card_modEq_card_fixedPoints V
  change Nat.card V % 3 = Nat.card (fixedPointSubgroup K V) % 3 at hmod
  exact (fixedPointSubgroup K V).eq_top_of_card_eq
    (card_eq_of_fifth_power_relation Nat.card_pos h2 hmod hsmall hcommon hha hid).symm
end Wielandt
