module

public import Theory.SpecificGroups.PSL3.CartanActions.ThreeAlignment
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Three-prime Borels in PSL₃ of odd binary degree

The projective diagonal torus has order dividing `(q-1)^2`, while its
index in the actual upper Borel divides `q^3`. If q = 2^n with n odd,
both are prime to three. This retains the projective scalar quotient
and needs no order or simplicity theorem for the whole group.

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955.
-/

public section

open scoped MatrixGroups
open Subgroup
namespace Matrix.PSL3.CartanActions.OddDegree
open LinearThree
variable (F : Type*) [Field F] [Finite F]

omit [Finite F] in
theorem card_torus_dvd : Nat.card (torus F) ∣ (Nat.card F - 1) ^ 2 := by
  simpa only [torus, Nat.card_prod, Nat.card_units, pow_two] using
    (Subgroup.card_range_dvd (torusMap F))

theorem borel_threePrime {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Odd n) :
    Nat.Coprime 3 (Nat.card (borel F)) := by
  have htorus : Nat.Coprime 3 (Nat.card (torus F)) := by
    apply Nat.Coprime.of_dvd_right (card_torus_dvd F)
    rw [hF]
    exact (Nat.BinaryTorusParity.coprime_three_sub_one hn).pow_right 2
  have hindex : Nat.Coprime 3 ((torus F).subgroupOf (borel F)).index := by
    apply Nat.Coprime.of_dvd_right (ThreeAlignment.torus_index_dvd F)
    rw [hF]
    exact ((by decide : Nat.Coprime 3 2).pow_right n).pow_right 3
  rw [← ((torus F).subgroupOf (borel F)).card_mul_index]
  apply Nat.Coprime.mul_right _ hindex
  rwa [Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv]

end Matrix.PSL3.CartanActions.OddDegree
