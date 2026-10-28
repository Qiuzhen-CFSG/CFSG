module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.Recurrence
/-!
# Split rank-two order formulas and odd opposition

The two reduced alternating expressions of the longest element calculate
|U| as the alternating product of the same two actual simple-root orders.
For m = 2k the result is (q₀q₁)^k; for odd m the endpoint orders agree
and |U| = q₀^m. These formulas require no prescribed value of m.
In odd length, the marked dihedral coordinates prove s₀w₀ = w₀s₁.
Conjugating the literal intersection X₀ by any lift of s₀w₀ then gives X₁,
so the equality of parameters also has an explicit conjugacy in the same N.

Source: Carter 2.5.10–2.5.17,
`refs/KGroup/GLS3/Chapter2Ca2.tex`. The proof uses only finite split BN
axioms; it does not assert commutator laws or a Lie-model realization.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (d : MarkedQuotient P) (split : SplitData d.tits)

/-- The alternating product of the two actual simple-root orders. -/
@[expose] def alternatingOrder : Bool → ℕ → ℕ
  | _, 0 => 1
  | b, n+1 => Nat.card (simpleRoot d split (if b then 1 else 0)) * alternatingOrder (!b) n

/-- The finite root recurrence along either reduced alternating expression. -/
theorem rootIntersection_card_alternating (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder d) :
    Nat.card (rootIntersection split (longest d) (alternatingWord d b n)⁻¹) =
      alternatingOrder d split b n := by
  induction n generalizing b with
  | zero => simp [alternatingWord, rootIntersection_one, alternatingOrder]
  | succ n ih =>
    let i : Fin 2 := if b then 1 else 0
    have hi : (d.simple i)⁻¹ = d.simple i := inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2)
    have hstep : d.tits.wordLength ((alternatingWord d (!b) n)⁻¹*d.simple i) =
        d.tits.wordLength ((alternatingWord d (!b) n)⁻¹)+1 := by
      rw [← hi, ← mul_inv_rev]
      change d.tits.wordLength (alternatingWord d b (n+1))⁻¹ = _
      rw [wordLength_inv, wordLength_inv, wordLength_alternatingWord d b hn,
        wordLength_alternatingWord d (!b) (by omega)]
    rw [alternatingWord, mul_inv_rev, hi,
      rootIntersection_card_ascent d split _ i hstep, ih (!b) (by omega)]
    rfl

/-- Two successive alternating factors give one factor of q₀q₁. -/
theorem alternatingOrder_even (b : Bool) (k : ℕ) :
    alternatingOrder d split b (2*k) =
      (Nat.card (simpleRoot d split 0)*Nat.card (simpleRoot d split 1))^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have he : 2*(k+1) = (2*k+1)+1 := by omega
    rw [he, alternatingOrder, alternatingOrder, Bool.not_not, ih, pow_succ]
    cases b <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false, mul_assoc, mul_comm, mul_left_comm]

theorem alternatingOrder_odd (b : Bool) (k : ℕ) :
    alternatingOrder d split b (2*k+1) = Nat.card (simpleRoot d split (if b then 1 else 0)) *
      (Nat.card (simpleRoot d split 0)*Nat.card (simpleRoot d split 1))^k := by
  rw [alternatingOrder, alternatingOrder_even]

/-- The longest word counts the entire specified unipotent subgroup. -/
theorem unipotent_card_alternating (b : Bool) :
    Nat.card split.U = alternatingOrder d split b (rotationOrder d) := by
  have h := rootIntersection_card_alternating d split b (rotationOrder d) le_rfl
  rwa [alternatingWord_longest, longest_inv, rootIntersection_longest] at h

/-- The general even-parameter formula, including the reducible m=2 case. -/
theorem unipotent_card_even (k : ℕ) (hm : rotationOrder d = 2*k) :
    Nat.card split.U =
      (Nat.card (simpleRoot d split 0)*Nat.card (simpleRoot d split 1))^k := by
  rw [unipotent_card_alternating d split false, hm, alternatingOrder_even]

/-- The general odd-parameter formula before identifying the two endpoint orders. -/
theorem unipotent_card_odd (k : ℕ) (hm : rotationOrder d = 2*k+1) (b : Bool) :
    Nat.card split.U = Nat.card (simpleRoot d split (if b then 1 else 0)) *
      (Nat.card (simpleRoot d split 0)*Nat.card (simpleRoot d split 1))^k := by
  rw [unipotent_card_alternating d split b, hm, alternatingOrder_odd]

private theorem map_alternating_even_odd (k : ℕ) :
    weylEquiv d (alternatingWord d false (2*k)) = DihedralGroup.r k ∧
    weylEquiv d (alternatingWord d true (2*k)) = DihedralGroup.r (-(k : ZMod (rotationOrder d))) ∧
    weylEquiv d (alternatingWord d false (2*k+1)) = DihedralGroup.sr (-(k : ZMod (rotationOrder d))) ∧
    weylEquiv d (alternatingWord d true (2*k+1)) = DihedralGroup.sr (k+1) := by
  induction k with
  | zero => simp [alternatingWord, weylEquiv_simple_zero, weylEquiv_simple_one]
  | succ k ih =>
    have he : 2*(k+1) = (2*k+1)+1 := by omega
    simp only [he, alternatingWord, Bool.false_eq_true, ite_false, ite_true,
      Bool.not_false, Bool.not_true, map_mul, weylEquiv_simple_zero, weylEquiv_simple_one,
      ih, DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_r,
      sub_zero, zero_add, Nat.cast_add, Nat.cast_one]
    simp only [neg_add_rev, sub_eq_add_neg, add_comm, and_self]

/-- The odd-dihedral opposition interchanges the original two endpoints. -/
theorem simple_zero_mul_longest_of_odd (hm : Odd (rotationOrder d)) :
    d.simple 0*longest d = longest d*d.simple 1 := by
  obtain ⟨k,hk⟩ := hm.exists_bit1
  have hw : weylEquiv d (longest d) = DihedralGroup.sr (-(k : ZMod (rotationOrder d))) := by
    exact (congrArg (fun n => weylEquiv d (alternatingWord d false n)) hk).trans
      (map_alternating_even_odd d k).2.2.1
  have hc : (k : ZMod (rotationOrder d)) + k + 1 = 0 := by
    have hh : ((2*k+1 : ℕ) : ZMod (rotationOrder d)) = 0 := by
      rw [← hk, ZMod.natCast_self]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, two_mul] using hh
  apply (weylEquiv d).injective
  rw [map_mul, map_mul, weylEquiv_simple_zero, weylEquiv_simple_one, hw]
  simp only [DihedralGroup.sr_mul_sr, sub_zero, sub_neg_eq_add]
  congr 1
  apply neg_eq_iff_add_eq_zero.mpr
  simpa only [add_assoc, add_left_comm, add_comm] using hc

/-- For odd m, the two actual simple roots are conjugate by a lift in the same N. -/
theorem simpleRoot_conjugate_of_odd (hm : Odd (rotationOrder d)) (ni : d.tits.N)
    (hni : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) ni =
      d.simple 0*longest d) :
    rightConjugate (simpleRoot d split 0) (ni : X ⧸ d.D) = simpleRoot d split 1 := by
  have hs : d.simple 0*d.simple 0 = 1 := by
    simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem 0)).2
  have he : (longest d*d.simple 0)*(d.simple 0*longest d) = 1 := by
    rw [mul_assoc, ← mul_assoc (d.simple 0), hs, one_mul, longest_mul_self]
  change rightConjugate (split.U ⊓ unipotentConjugate split (longest d*d.simple 0))
    (ni:X ⧸ d.D) = split.U ⊓ unipotentConjugate split (longest d*d.simple 1)
  rw [rightConjugate_inf, ← unipotentConjugate_eq split _ ni hni,
    unipotentConjugate_right split _ _ ni hni, he, unipotentConjugate_one,
    simple_zero_mul_longest_of_odd d hm, inf_comm]

/-- Odd dihedral length forces equality of the same two simple-root orders. -/
theorem simpleRoot_card_eq_of_odd (hm : Odd (rotationOrder d)) :
    Nat.card (simpleRoot d split 0) = Nat.card (simpleRoot d split 1) := by
  obtain ⟨k,hk⟩ := hm.exists_bit1
  have h0 := unipotent_card_odd d split k hk false
  have h1 := unipotent_card_odd d split k hk true
  have he : Nat.card (simpleRoot d split 0)*
      (Nat.card (simpleRoot d split 0)*Nat.card (simpleRoot d split 1))^k =
      Nat.card (simpleRoot d split 1)*
      (Nat.card (simpleRoot d split 0)*Nat.card (simpleRoot d split 1))^k := h0.symm.trans h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) _) he

/-- Equal endpoint orders yield the uniform q^n formula at every reduced length. -/
theorem alternatingOrder_eq_pow (hq : Nat.card (simpleRoot d split 0) = Nat.card (simpleRoot d split 1))
    (b : Bool) (n : ℕ) : alternatingOrder d split b n = Nat.card (simpleRoot d split 0)^n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [alternatingOrder, ih, pow_succ]
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, ← hq, mul_comm]

/-- In odd dihedral rank the unipotent order is q^m. -/
theorem unipotent_card_odd_pow (hm : Odd (rotationOrder d)) :
    Nat.card split.U = Nat.card (simpleRoot d split 0)^rotationOrder d := by
  rw [unipotent_card_alternating d split false,
    alternatingOrder_eq_pow d split (simpleRoot_card_eq_of_odd d split hm)]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
