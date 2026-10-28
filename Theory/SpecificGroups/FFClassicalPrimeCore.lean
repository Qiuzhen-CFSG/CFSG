module

public import Theory.SpecificGroups.FFLinearPrimeCore
public import Theory.SpecificGroups.PermutationThreePrimeCore
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# Further classical models with trivial three-prime core

Simplicity and three-divisibility handle the alternating groups. A cyclic
center of order three handles the exceptional triple cover, reusing its
quasisimplicity. The scalar-center and order formulas give the binary
linear groups of degrees four and five. For Sp₄ in characteristic two,
we reuse the quasisimplicity supplied by the source, its proved trivial
center and its order formula. No independent simplicity certification is
needed for this last family.

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
B.5.6(1), printed p.105. The imported order and simplicity constructions
retain their ATLAS attribution and license.
-/

public section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups
theorem alternating_threePrimeCore (n : ℕ) (hn : 5 ≤ n) : pPrimeCore 3 (alternatingGroup (Fin n)) = ⊥ := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  apply pPrimeCore_eq_bot_of_simple
  rw [nat_card_alternatingGroup]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact Nat.dvd_div_of_mul_dvd (show 2 * 3 ∣ n.factorial from
    (by decide : 2 * 3 = (3 : ℕ).factorial) ▸ Nat.factorial_dvd_factorial (by omega))
theorem quasisimple_center_three_threePrimeCore {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (e : center L ≃* Multiplicative (ZMod 3)) : pPrimeCore 3 L = ⊥ := by
  have hc : Nat.card (center L) = 3 := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_zmod 3
  apply IsQuasisimple.pPrimeCore_eq_bot
  · exact IsPGroup.of_card (n := 1) (by simpa using hc)
  · simpa only [hc] using (center L).card_subgroup_dvd_card
theorem binary_linear_threePrimeCore (n : ℕ) (hn : n = 4 ∨ n = 5) :
    pPrimeCore 3 SL(n,ZMod 2) = ⊥ := by
  have hpos : 0 < n := by omega
  let : NeZero n := ⟨by omega⟩
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hpos
  have hc : center SL(n,ZMod 2) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Atlas.ExceptionalSupport.card_sl_center]
    simp
  let : IsQuasisimple SL(n,ZMod 2) :=
    { toIsPerfect := Atlas.sl_perfect n (by omega)
      simple := Atlas.psl_simple_high_rank n (by omega) }
  apply IsQuasisimple.pPrimeCore_eq_bot
  · rw [hc]
    exact IsPGroup.of_subsingleton 3 _
  · have he := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) n
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(n,ZMod 2))
    have hcenter : Nat.card (center SL(n,ZMod 2)) = 1 := by rw [hc, Subgroup.card_bot]
    rw [hcenter, mul_one] at hcard
    change Nat.card SL(n,ZMod 2) = Nat.card PSL(n,ZMod 2) at hcard
    rw [← hcard] at he
    rcases hn with rfl | rfl <;>
      norm_num only [Nat.card_zmod, Nat.gcd_one_right, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, Fin.prod_univ_zero, Nat.reduceSub, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, mul_one] at he <;>
      rw [he] <;> norm_num
theorem three_dvd_even_square_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h : (2 ^ n) ^ 2 % 3 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    have := (show Nat.ModEq 3 4 1 from by decide).pow n
    simpa [Nat.ModEq] using this
  omega
theorem symplectic_four_threePrimeCore (F : Type*) [Field F] [Finite F] [CharP F 2]
    [IsQuasisimple (Matrix.symplecticGroup (Fin 2) F)] (n : ℕ) (hc : Nat.card F = 2 ^ n) :
    pPrimeCore 3 (Matrix.symplecticGroup (Fin 2) F) = ⊥ := by
  apply IsQuasisimple.pPrimeCore_eq_bot
  · rw [SymplecticFour.EvenProjective.center_eq_bot]
    exact IsPGroup.of_subsingleton 3 _
  · rw [SymplecticFour.card_sp, hc]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (three_dvd_even_square_sub_one n) _) _
end Theory.SpecificGroups
