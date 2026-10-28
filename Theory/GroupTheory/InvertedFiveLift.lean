module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.XCensus.Five
public import Mathlib.GroupTheory.PGroup

/-!
# Inverted five-subgroups above the actual alternating group A₅

A nontrivial involution in an A₅ quotient inverts an element of order five.
Lifting that element provides a conjugate of the original involution whose
product has image of order five. A power of this product has order five
and is inverted by the unchanged original involution. The entire cyclic
subgroup is inverted. No condition on the quotient kernel is needed.

Source application: Aschbacher–Smith J.2.7(5), printed p.436.
-/

namespace Subgroup
/-- A nontrivial involution image in A₅ supplies an inverted subgroup of order five. -/
public theorem exists_inverted_five_of_surjective_alternating_five
    {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (w : G) (hw : w ^ 2 = 1) (hfw : f w ≠ 1) :
    ∃ Q : Subgroup G, Nat.card Q = 5 ∧
      w ∈ Subgroup.normalizer (Q : Set G) ∧
      ∀ q ∈ Q, w * q * w⁻¹ = q⁻¹ := by
  have hfo : orderOf (f w) = 2 := orderOf_eq_prime
    (by rw [← map_pow, hw, map_one]) hfw
  obtain ⟨b,hb,hab⟩ :=
    Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.XCensus.a5_involution_inverts_five (f w) hfo
  obtain ⟨g,hg⟩ := hf b
  let x := w * (g * w * g⁻¹)
  have hwf : (f w)⁻¹ = f w := by rw [← map_inv]; congr 1; exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)
  have hfx : orderOf (f x) = 5 := by
    have he : f x = (b ^ 2)⁻¹ := by
      calc
        f x = (f w * b * (f w)⁻¹) * b⁻¹ := by
          simp only [x,map_mul,map_inv,hg,hwf,mul_assoc]
        _ = b⁻¹ * b⁻¹ := by rw [hab]
        _ = (b ^ 2)⁻¹ := by simp only [pow_two,mul_inv_rev]
    rw [he,orderOf_inv,(show (orderOf b).Coprime 2 by rw [hb]; decide).orderOf_pow,hb]
  have hfive : 5 ∣ orderOf x := hfx ▸ orderOf_map_dvd f x
  let y := x ^ (orderOf x / 5)
  have hy : orderOf y = 5 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' hfive
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)
  have hxinv : w * x * w⁻¹ = x⁻¹ := by
    calc
      w * x * w⁻¹ = w ^ 2 * (g * w * g⁻¹) * w⁻¹ := by simp only [x, pow_two, mul_assoc]
      _ = (g * w * g⁻¹) * w⁻¹ := by rw [hw, one_mul]
      _ = x⁻¹ := by simp only [x, mul_inv_rev, inv_inv, hwinv, mul_assoc]
  have hyinv : w * y * w⁻¹ = y⁻¹ := by
    change MulAut.conj w (x ^ (orderOf x / 5)) = y⁻¹
    rw [map_pow]
    change (w * x * w⁻¹) ^ (orderOf x / 5) = y⁻¹
    rw [hxinv, inv_pow]
  let Q := Subgroup.zpowers y
  have hinv : ∀ q ∈ Q, w * q * w⁻¹ = q⁻¹ := by
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    change MulAut.conj w (y ^ n) = (y ^ n)⁻¹
    rw [map_zpow]
    change (w * y * w⁻¹) ^ n = (y ^ n)⁻¹
    rw [hyinv, inv_zpow]
  refine ⟨Q, ?_, ?_, hinv⟩
  · exact (Nat.card_zpowers y).trans hy
  · apply Subgroup.mem_normalizer_iff.mpr
    intro q
    constructor
    · intro hq
      rw [hinv q hq]
      exact Q.inv_mem hq
    · intro hq
      have hconj : w * (w * q * w⁻¹) * w⁻¹ ∈ Q := by
        rw [hinv _ hq]
        exact Q.inv_mem hq
      have hww : w * (w * q * w⁻¹) * w⁻¹ = q := by
        calc
          w * (w * q * w⁻¹) * w⁻¹ = w ^ 2 * q * (w ^ 2)⁻¹ := by
            simp only [pow_two, mul_inv_rev, mul_assoc]
          _ = q := by rw [hw]; simp
      exact hww ▸ hconj

end Subgroup
