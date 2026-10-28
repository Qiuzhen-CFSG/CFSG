module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.IntervalCases

/-!
# Restricting involution commutators to an odd containing subgroup

If H ≤ D has odd order and contains [D,t] for an involution t, then
[D,t] = [H,t]. Each generator [d,t] is inverted by t, and its square
is therefore a commutator with first entry in H. Odd order recovers
the generator from that square.

This justifies K = [D,t] in the opening of GLS, volume 4, Chapter 2,
Section 16, after Proposition 3.5 supplies containment in O₂′(D).
It does not identify the commutator with the entire odd core.
-/

open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Restricting to an odd subgroup containing all involution commutators
does not change the commutator subgroup. -/
public theorem commutator_involution_eq_of_le_odd (D H : Subgroup G) (hHD : H ≤ D)
    (hodd : Odd (Nat.card H)) (t : G) (ht : orderOf t = 2)
    (hcomm : ⁅D, zpowers t⁆ ≤ H) : ⁅D, zpowers t⁆ = ⁅H, zpowers t⁆ := by
  classical
  apply le_antisymm ?_ (commutator_mono hHD le_rfl)
  rw [commutator_le]
  intro d hd s hs
  rw [mem_zpowers_iff_mem_range_orderOf, ht] at hs
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
  have hnlt := Finset.mem_range.mp hn
  interval_cases n
  · simp
  · simp only [pow_one]
    let x := ⁅d,t⁆
    have hx : x ∈ H := hcomm (commutator_mem_commutator hd (mem_zpowers t))
    have htt : t * t = 1 := by simpa [pow_two, ht] using pow_orderOf_eq_one t
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    have hinv : t * x * t⁻¹ = x⁻¹ := by
      dsimp only [x]
      simp only [commutatorElement_def, mul_inv_rev, inv_inv, hti,
        mul_assoc, htt, mul_one]
    have hsq : x ^ 2 ∈ ⁅H, zpowers t⁆ := by
      have he : ⁅x,t⁆ = x ^ 2 := by
        calc
          ⁅x,t⁆ = x * (t * x * t⁻¹)⁻¹ := by
            simp [commutatorElement_def, mul_assoc]
          _ = x ^ 2 := by rw [hinv, inv_inv, pow_two]
      rw [← he]
      exact commutator_mem_commutator hx (mem_zpowers t)
    have hxo : Odd (orderOf x) := hodd.of_dvd_nat (H.orderOf_dvd_natCard hx)
    obtain ⟨n, hn⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one x) hxo 1
    rw [pow_one, pow_mul] at hn
    change x ∈ _
    rw [hn]
    exact pow_mem hsq n
end Subgroup
