module
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Odd actors normalized by a cubic in a solvable M₂₂ Sylow overgroup

The native solvable-overgroup theorem forces order 384. The join of an
odd subgroup D and a cubic E normalizing it has odd order dividing 384,
so it equals E. This controls the actual D and E without selecting a
new conjugate parabolic.

Source application: Aschbacher--Smith 5.1.13, printed p.637,
refs/quasithin.pdf, after projecting the first J₄ involution centralizer.
-/

public section
open Subgroup
namespace Sporadic.Mathieu.M22SolvableSylow

/-- The original odd actor lies in the normalizing cubic. -/
theorem odd_actor_le_cubic (S : Sylow 2 M22) (K D E : Subgroup M22)
    (hs : Group.IsSolvable K) (hSK : (S : Subgroup M22) ≤ K)
    (hDK : D ≤ K) (hEK : E ≤ K) (hD : Odd (Nat.card D))
    (hE : Nat.card E = 3) (hED : E ≤ normalizer (D : Set M22)) : D ≤ E := by
  have hn : (K.subgroupOf K).Normal := by rw [subgroupOf_self]; infer_instance
  have hthree : 3 ∣ Nat.card K := hE ▸ card_dvd_of_le hEK
  have hK := card_eq_384_of_solvable_normal_three K K le_rfl hn hs hthree ⟨S,hSK⟩
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D E hED
  have hodd : Odd (Nat.card (D ⊔ E : Subgroup M22)) := by
    have hh : Odd (Nat.card (D ⊓ E : Subgroup M22) * Nat.card (D ⊔ E : Subgroup M22)) := by
      rw [←hprod,hE]
      exact hD.mul (by decide)
    exact (Nat.odd_mul.mp hh).2
  have hd : Nat.card (D ⊔ E : Subgroup M22) ∣ 3 * 128 := by
    simpa only [hK] using card_dvd_of_le (sup_le hDK hEK)
  have hc : Nat.Coprime (Nat.card (D ⊔ E : Subgroup M22)) 128 :=
    hodd.coprime_two_right.pow_right 7
  have hcard : Nat.card (D ⊔ E : Subgroup M22) ≤ 3 :=
    Nat.le_of_dvd (by decide) (hc.dvd_of_dvd_mul_right hd)
  have he : E = D ⊔ E := eq_of_le_of_card_ge le_sup_right (hE ▸ hcard)
  exact he ▸ le_sup_left
end Sporadic.Mathieu.M22SolvableSylow
