module
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Data.ZMod.Basic

/-!
# Seven does not divide Fermat-field PSL₄

A field order of the form `2^(2^k)+1` is three or five modulo seven.
None of its first four powers is one modulo seven. The literal product
formula for the general linear order, including the scalar and determinant
factors, therefore excludes seven from the projective special linear order.

This is the order calculation used for the Fermat PSL₄ row in
Aschbacher--Smith 4.4.3, printed p.622.
-/

public section
open scoped MatrixGroups
namespace Theory.SpecificGroups.PSL4
private theorem fermat_mod_seven (k : ℕ) :
    ((2 : ZMod 7) ^ (2 ^ k) + 1 = 3) ∨ ((2 : ZMod 7) ^ (2 ^ k) + 1 = 5) := by
  have h : (2 : ZMod 7) ^ (2 ^ k) = 2 ∨ (2 : ZMod 7) ^ (2 ^ k) = 4 := by
    induction k with
    | zero => norm_num
    | succ k hk =>
      rw [pow_succ,pow_mul]
      rcases hk with h | h <;> rw [h] <;> decide
  rcases h with h | h <;> rw [h] <;> decide

/-- Seven does not divide the order of PSL₄ over a field of Fermat order. -/
theorem fermat_seven_not_dvd
    {F : Type*} [Field F] [Finite F] {r : ℕ}
    (hf : ∃ k : ℕ, r = 2 ^ (2 ^ k) + 1) (hF : Nat.card F = r) :
    ¬ 7 ∣ Nat.card PSL(4,F) := by
  obtain ⟨k,rfl⟩ := hf
  let r := 2 ^ (2 ^ k) + 1
  change Nat.card F = r at hF
  intro hd
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  have hdiv : 7 ∣ ∏ i : Fin 4, (r^4-r^(i:ℕ)) := by
    rw [←hF,←hc]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
  have hz : ((∏ i : Fin 4, (r^4-r^(i:ℕ)) : ℕ) : ZMod 7) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have he (i : Fin 4) : ((r^4-r^(i:ℕ) : ℕ) : ZMod 7) =
      (r : ZMod 7)^4-(r : ZMod 7)^(i:ℕ) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by dsimp [r]; positivity) (by omega)),
      Nat.cast_pow,Nat.cast_pow]
  rw [Nat.cast_prod] at hz
  simp_rw [he] at hz
  have hr : (r : ZMod 7) = 3 ∨ (r : ZMod 7) = 5 := by
    simpa only [r,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using fermat_mod_seven k
  rcases hr with hr | hr
  · rw [hr] at hz
    exact (by decide : (∏ i : Fin 4, ((3 : ZMod 7)^4-3^(i:ℕ))) ≠ 0) hz
  · rw [hr] at hz
    exact (by decide : (∏ i : Fin 4, ((5 : ZMod 7)^4-5^(i:ℕ))) ≠ 0) hz

end Theory.SpecificGroups.PSL4
