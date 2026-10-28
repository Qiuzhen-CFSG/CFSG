module

public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence

/-!
# The small odd PSL₂ models have no element of order twelve

The involution in a putative cyclic group of order twelve centralizes that
whole group. Its actual PSL₂ centralizer has order q−1 or q+1, both incompatible
with twelve when q is seven or nine. This supplies the original-local check
needed after the Chapter 15 offender action has restricted the field.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
theorem orderOf_ne_twelve_of_card_seven_or_nine {F : Type*} [Field F] [Finite F]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (hc : Nat.card F = 7 ∨ Nat.card F = 9) (x : PSL(2,F)) : orderOf x ≠ 12 := by
  intro hx
  let t := x ^ 6
  have ht : orderOf t = 2 := by
    have hh := orderOf_pow_orderOf_div (x := x) (n := 2) (by omega) (by omega)
    simpa [hx,t] using hh
  have hinv : IsInvolution t := (orderOf_eq_prime_iff.mp ht).symm
  have hxC : x ∈ centralizer ({t} : Set PSL(2,F)) := by
    apply mem_centralizer_singleton_iff.mpr
    exact (Commute.self_pow x 6).eq
  have hd : 12 ∣ Nat.card (centralizer ({t} : Set PSL(2,F))) :=
    hx ▸ Subgroup.orderOf_dvd_natCard _ hxC
  have h := Theory.PSL2.involution_centralizer_card_cases hF t hinv
  rcases hc with hc | hc <;> rcases h with h | h <;> rw [h,hc] at hd <;> norm_num at hd


end Theory.PSL2
