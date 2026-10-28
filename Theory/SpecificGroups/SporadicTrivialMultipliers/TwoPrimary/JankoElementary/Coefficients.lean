module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoElementary.Collection
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Tables
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Tactic.LinearCombination

/-!
# Vanishing of quadratic polynomials invariant under the max1 action

The eleven linear and fifty-five strictly upper triangular quadratic
coefficients are constrained by invariance on basis vectors and their pairwise
sums. Below are explicit row operations reducing sixty-six of these equations
to zero coefficients. Each operation is proved in the Boolean ring; the action
masks are the original certified ATLAS right-conjugation tables.

The expansion lemma prevents repeated recursive unfolding in row reduction.
No externally computed rank or unchecked certificate is assumed.
-/

@[expose] public section
namespace Janko4.TwoPrimary.JankoElementary
open Cardinality.KernelCount
attribute [local irreducible] bne
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency true

/-- The binary vector represented by a mask. -/
def mask (m : ℕ) : Fin 11 → Bool := fun i => m.testBit i.val
/-- A coordinate vector. -/
def single (i : Fin 11) : Fin 11 → Bool := fun j => decide (j = i)
/-- Addition in binary coordinates. -/
def add (v w : Fin 11 → Bool) : Fin 11 → Bool := fun i => v i ^^ w i

/-- Invariance on basis vectors and their pairwise sums. -/
def TableInvariant (Q : (Fin 11 → Bool) → Bool) (a : Fin 11 → ℕ) : Prop :=
  (∀ i, Q (mask (a i)) = Q (single i)) ∧
  (∀ i j, Q (add (mask (a i)) (mask (a j))) = Q (add (single i) (single j)))

private lemma xor_cancel (a b : Bool) : (a ^^ (a ^^ b)) = b := by
  rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
private lemma xor_zero {a b : Bool} (ha : a = false) (hb : b = false) :
    (a ^^ b) = false := by rw [ha, hb, Bool.false_xor]
private lemma xor_of_eq {a b : Bool} (h : a = b) : (a ^^ b) = false := by
  rw [h, Bool.xor_self]

private theorem quadratic_expand (s : Fin 11 → Bool) (b : Fin 11 → Fin 11 → Bool)
    (v : Fin 11 → Bool) : quadratic s b v =
    ((v 0 && s 0) ^^ (((v 1 && s 1) ^^ (((v 2 && s 2) ^^ (((v 3 && s 3) ^^ (((v 4 && s 4) ^^ (((v 5 && s 5) ^^ (((v 6 && s 6) ^^ (((v 7 && s 7) ^^ (((v 8 && s 8) ^^ (((v 9 && s 9) ^^ (((v 10 && s 10) ^^ (false ^^ (v 10 && false))) ^^ (v 9 && ((v 10 && b 9 10) ^^ false)))) ^^ (v 8 && ((v 9 && b 8 9) ^^ ((v 10 && b 8 10) ^^ false))))) ^^ (v 7 && ((v 8 && b 7 8) ^^ ((v 9 && b 7 9) ^^ ((v 10 && b 7 10) ^^ false)))))) ^^ (v 6 && ((v 7 && b 6 7) ^^ ((v 8 && b 6 8) ^^ ((v 9 && b 6 9) ^^ ((v 10 && b 6 10) ^^ false))))))) ^^ (v 5 && ((v 6 && b 5 6) ^^ ((v 7 && b 5 7) ^^ ((v 8 && b 5 8) ^^ ((v 9 && b 5 9) ^^ ((v 10 && b 5 10) ^^ false)))))))) ^^ (v 4 && ((v 5 && b 4 5) ^^ ((v 6 && b 4 6) ^^ ((v 7 && b 4 7) ^^ ((v 8 && b 4 8) ^^ ((v 9 && b 4 9) ^^ ((v 10 && b 4 10) ^^ false))))))))) ^^ (v 3 && ((v 4 && b 3 4) ^^ ((v 5 && b 3 5) ^^ ((v 6 && b 3 6) ^^ ((v 7 && b 3 7) ^^ ((v 8 && b 3 8) ^^ ((v 9 && b 3 9) ^^ ((v 10 && b 3 10) ^^ false)))))))))) ^^ (v 2 && ((v 3 && b 2 3) ^^ ((v 4 && b 2 4) ^^ ((v 5 && b 2 5) ^^ ((v 6 && b 2 6) ^^ ((v 7 && b 2 7) ^^ ((v 8 && b 2 8) ^^ ((v 9 && b 2 9) ^^ ((v 10 && b 2 10) ^^ false))))))))))) ^^ (v 1 && ((v 2 && b 1 2) ^^ ((v 3 && b 1 3) ^^ ((v 4 && b 1 4) ^^ ((v 5 && b 1 5) ^^ ((v 6 && b 1 6) ^^ ((v 7 && b 1 7) ^^ ((v 8 && b 1 8) ^^ ((v 9 && b 1 9) ^^ ((v 10 && b 1 10) ^^ false)))))))))))) ^^ (v 0 && ((v 1 && b 0 1) ^^ ((v 2 && b 0 2) ^^ ((v 3 && b 0 3) ^^ ((v 4 && b 0 4) ^^ ((v 5 && b 0 5) ^^ ((v 6 && b 0 6) ^^ ((v 7 && b 0 7) ^^ ((v 8 && b 0 8) ^^ ((v 9 && b 0 9) ^^ ((v 10 && b 0 10) ^^ false))))))))))))) := by rfl
@[local simp] private lemma even1 : (2 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even2 : (4 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even3 : (6 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even4 : (8 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even5 : (10 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even6 : (12 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even7 : (14 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even8 : (16 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even9 : (18 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even10 : (20 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even11 : (22 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even12 : (24 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even13 : (26 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even14 : (28 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even15 : (30 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even16 : (32 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even17 : (34 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even18 : (36 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even19 : (38 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even20 : (40 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even21 : (42 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even22 : (44 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even23 : (46 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even24 : (48 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even25 : (50 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even26 : (52 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even27 : (54 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even28 : (56 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even29 : (58 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even30 : (60 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even31 : (62 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even32 : (64 : Bool) = 0 := by decide +kernel
@[local simp] private lemma even33 : (66 : Bool) = 0 := by decide +kernel

section
variable (s : Fin 11 → Bool) (b : Fin 11 → Fin 11 → Bool)
variable (h : TableInvariant (quadratic s b) xMasks ∧ TableInvariant (quadratic s b) yMasks)
include h

private lemma e0 : ((s 0) ^^ (s 1)) = false := by
  have hh : quadratic s b (![false, true, false, false, false, false, false, false, false, false, false]) = quadratic s b (![true, false, false, false, false, false, false, false, false, false, false]) := by
    convert h.1.1 0 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r0 : ((s 0) ^^ (s 1)) = false := by
  exact e0 s b h

private lemma e2 : ((s 2) ^^ (s 3)) = false := by
  have hh : quadratic s b (![false, false, false, true, false, false, false, false, false, false, false]) = quadratic s b (![false, false, true, false, false, false, false, false, false, false, false]) := by
    convert h.1.1 2 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r2 : ((s 2) ^^ (s 3)) = false := by
  exact e2 s b h

private lemma e5 : ((s 5) ^^ (s 6)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, false, true, false, false, false, false]) = quadratic s b (![false, false, false, false, false, true, false, false, false, false, false]) := by
    convert h.1.1 5 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r5 : ((s 5) ^^ (s 6)) = false := by
  exact e5 s b h

private lemma e7 : ((s 5) ^^ (s 6) ^^ (b 5 6) ^^ (b 5 7) ^^ (b 6 7)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, true, true, false, false, false]) = quadratic s b (![false, false, false, false, false, false, false, true, false, false, false]) := by
    convert h.1.1 7 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination hh

private lemma r7 : ((b 5 6) ^^ (b 5 7) ^^ (b 6 7)) = false := by
  have hh := (xor_zero (e7 s b h) (r5 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e8 : ((s 8) ^^ (s 9)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, false, false, false, false, true, false]) = quadratic s b (![false, false, false, false, false, false, false, false, true, false, false]) := by
    convert h.1.1 8 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r8 : ((s 8) ^^ (s 9)) = false := by
  exact e8 s b h

private lemma e10 : ((s 5) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, false, true, true, true, true]) = quadratic s b (![false, false, false, false, false, false, false, false, false, false, true]) := by
    convert h.1.1 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination hh

private lemma r10 : ((s 6) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (e10 s b h) (r5 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e12 : ((s 0) ^^ (s 1) ^^ (s 2) ^^ (s 3) ^^ (b 0 2) ^^ (b 1 3)) = false := by
  have hh : quadratic s b (![false, true, false, true, false, false, false, false, false, false, false]) = quadratic s b (![true, false, true, false, false, false, false, false, false, false, false]) := by
    convert h.1.2 0 2 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r12 : ((b 0 2) ^^ (b 1 3)) = false := by
  have hh := (xor_zero (xor_zero (e12 s b h) (r0 s b h)) (r2 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e13 : ((s 0) ^^ (s 1) ^^ (s 2) ^^ (s 3) ^^ (b 0 3) ^^ (b 1 2)) = false := by
  have hh : quadratic s b (![false, true, true, false, false, false, false, false, false, false, false]) = quadratic s b (![true, false, false, true, false, false, false, false, false, false, false]) := by
    convert h.1.2 0 3 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r13 : ((b 0 3) ^^ (b 1 2)) = false := by
  have hh := (xor_zero (xor_zero (e13 s b h) (r0 s b h)) (r2 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e14 : ((s 0) ^^ (s 1) ^^ (b 0 4) ^^ (b 1 4)) = false := by
  have hh : quadratic s b (![false, true, false, false, true, false, false, false, false, false, false]) = quadratic s b (![true, false, false, false, true, false, false, false, false, false, false]) := by
    convert h.1.2 0 4 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r14 : ((b 0 4) ^^ (b 1 4)) = false := by
  have hh := (xor_zero (e14 s b h) (r0 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e15 : ((s 0) ^^ (s 1) ^^ (s 5) ^^ (s 6) ^^ (b 0 5) ^^ (b 1 6)) = false := by
  have hh : quadratic s b (![false, true, false, false, false, false, true, false, false, false, false]) = quadratic s b (![true, false, false, false, false, true, false, false, false, false, false]) := by
    convert h.1.2 0 5 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r15 : ((b 0 5) ^^ (b 1 6)) = false := by
  have hh := (xor_zero (xor_zero (e15 s b h) (r0 s b h)) (r5 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e16 : ((s 0) ^^ (s 1) ^^ (s 5) ^^ (s 6) ^^ (b 0 6) ^^ (b 1 5)) = false := by
  have hh : quadratic s b (![false, true, false, false, false, true, false, false, false, false, false]) = quadratic s b (![true, false, false, false, false, false, true, false, false, false, false]) := by
    convert h.1.2 0 6 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r16 : ((b 0 6) ^^ (b 1 5)) = false := by
  have hh := (xor_zero (xor_zero (e16 s b h) (r0 s b h)) (r5 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e17 : ((s 0) ^^ (s 1) ^^ (s 5) ^^ (s 6) ^^ (b 0 7) ^^ (b 1 5) ^^ (b 1 6) ^^ (b 1 7) ^^ (b 5 6) ^^ (b 5 7) ^^ (b 6 7)) = false := by
  have hh : quadratic s b (![false, true, false, false, false, true, true, true, false, false, false]) = quadratic s b (![true, false, false, false, false, false, false, true, false, false, false]) := by
    convert h.1.2 0 7 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r17 : ((b 0 7) ^^ (b 1 5) ^^ (b 1 6) ^^ (b 1 7) ^^ (b 5 6) ^^ (b 5 7) ^^ (b 6 7)) = false := by
  have hh := (xor_zero (xor_zero (e17 s b h) (r0 s b h)) (r5 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e18 : ((s 0) ^^ (s 1) ^^ (s 8) ^^ (s 9) ^^ (b 0 8) ^^ (b 1 9)) = false := by
  have hh : quadratic s b (![false, true, false, false, false, false, false, false, false, true, false]) = quadratic s b (![true, false, false, false, false, false, false, false, true, false, false]) := by
    convert h.1.2 0 8 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r18 : ((b 0 8) ^^ (b 1 9)) = false := by
  have hh := (xor_zero (xor_zero (e18 s b h) (r0 s b h)) (r8 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e19 : ((s 0) ^^ (s 1) ^^ (s 8) ^^ (s 9) ^^ (b 0 9) ^^ (b 1 8)) = false := by
  have hh : quadratic s b (![false, true, false, false, false, false, false, false, true, false, false]) = quadratic s b (![true, false, false, false, false, false, false, false, false, true, false]) := by
    convert h.1.2 0 9 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r19 : ((b 0 9) ^^ (b 1 8)) = false := by
  have hh := (xor_zero (xor_zero (e19 s b h) (r0 s b h)) (r8 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e20 : ((s 0) ^^ (s 1) ^^ (s 5) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 0 10) ^^ (b 1 5) ^^ (b 1 7) ^^ (b 1 8) ^^ (b 1 9) ^^ (b 1 10) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![false, true, false, false, false, true, false, true, true, true, true]) = quadratic s b (![true, false, false, false, false, false, false, false, false, false, true]) := by
    convert h.1.2 0 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r20 : ((b 0 10) ^^ (b 1 5) ^^ (b 1 7) ^^ (b 1 8) ^^ (b 1 9) ^^ (b 1 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (e20 s b h) (r0 s b h)) (r5 s b h)) (r10 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e31 : ((s 2) ^^ (s 3) ^^ (b 2 4) ^^ (b 3 4)) = false := by
  have hh : quadratic s b (![false, false, false, true, true, false, false, false, false, false, false]) = quadratic s b (![false, false, true, false, true, false, false, false, false, false, false]) := by
    convert h.1.2 2 4 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r31 : ((b 2 4) ^^ (b 3 4)) = false := by
  have hh := (xor_zero (e31 s b h) (r2 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e32 : ((s 2) ^^ (s 3) ^^ (s 5) ^^ (s 6) ^^ (b 2 5) ^^ (b 3 6)) = false := by
  have hh : quadratic s b (![false, false, false, true, false, false, true, false, false, false, false]) = quadratic s b (![false, false, true, false, false, true, false, false, false, false, false]) := by
    convert h.1.2 2 5 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r32 : ((b 2 5) ^^ (b 3 6)) = false := by
  have hh := (xor_zero (xor_zero (e32 s b h) (r2 s b h)) (r5 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e33 : ((s 2) ^^ (s 3) ^^ (s 5) ^^ (s 6) ^^ (b 2 6) ^^ (b 3 5)) = false := by
  have hh : quadratic s b (![false, false, false, true, false, true, false, false, false, false, false]) = quadratic s b (![false, false, true, false, false, false, true, false, false, false, false]) := by
    convert h.1.2 2 6 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r33 : ((b 2 6) ^^ (b 3 5)) = false := by
  have hh := (xor_zero (xor_zero (e33 s b h) (r2 s b h)) (r5 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e34 : ((s 2) ^^ (s 3) ^^ (s 5) ^^ (s 6) ^^ (b 2 7) ^^ (b 3 5) ^^ (b 3 6) ^^ (b 3 7) ^^ (b 5 6) ^^ (b 5 7) ^^ (b 6 7)) = false := by
  have hh : quadratic s b (![false, false, false, true, false, true, true, true, false, false, false]) = quadratic s b (![false, false, true, false, false, false, false, true, false, false, false]) := by
    convert h.1.2 2 7 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r34 : ((b 2 7) ^^ (b 3 5) ^^ (b 3 6) ^^ (b 3 7) ^^ (b 5 6) ^^ (b 5 7) ^^ (b 6 7)) = false := by
  have hh := (xor_zero (xor_zero (e34 s b h) (r2 s b h)) (r5 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e35 : ((s 2) ^^ (s 3) ^^ (s 8) ^^ (s 9) ^^ (b 2 8) ^^ (b 3 9)) = false := by
  have hh : quadratic s b (![false, false, false, true, false, false, false, false, false, true, false]) = quadratic s b (![false, false, true, false, false, false, false, false, true, false, false]) := by
    convert h.1.2 2 8 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r35 : ((b 2 8) ^^ (b 3 9)) = false := by
  have hh := (xor_zero (xor_zero (e35 s b h) (r2 s b h)) (r8 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e36 : ((s 2) ^^ (s 3) ^^ (s 8) ^^ (s 9) ^^ (b 2 9) ^^ (b 3 8)) = false := by
  have hh : quadratic s b (![false, false, false, true, false, false, false, false, true, false, false]) = quadratic s b (![false, false, true, false, false, false, false, false, false, true, false]) := by
    convert h.1.2 2 9 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r36 : ((b 2 9) ^^ (b 3 8)) = false := by
  have hh := (xor_zero (xor_zero (e36 s b h) (r2 s b h)) (r8 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e37 : ((s 2) ^^ (s 3) ^^ (s 5) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 2 10) ^^ (b 3 5) ^^ (b 3 7) ^^ (b 3 8) ^^ (b 3 9) ^^ (b 3 10) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![false, false, false, true, false, true, false, true, true, true, true]) = quadratic s b (![false, false, true, false, false, false, false, false, false, false, true]) := by
    convert h.1.2 2 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r37 : ((b 2 10) ^^ (b 3 5) ^^ (b 3 7) ^^ (b 3 8) ^^ (b 3 9) ^^ (b 3 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (e37 s b h) (r2 s b h)) (r5 s b h)) (r10 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e45 : ((s 5) ^^ (s 6) ^^ (b 4 5) ^^ (b 4 6)) = false := by
  have hh : quadratic s b (![false, false, false, false, true, false, true, false, false, false, false]) = quadratic s b (![false, false, false, false, true, true, false, false, false, false, false]) := by
    convert h.1.2 4 5 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r45 : ((b 4 5) ^^ (b 4 6)) = false := by
  have hh := (xor_zero (e45 s b h) (r5 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e48 : ((s 8) ^^ (s 9) ^^ (b 4 8) ^^ (b 4 9)) = false := by
  have hh : quadratic s b (![false, false, false, false, true, false, false, false, false, true, false]) = quadratic s b (![false, false, false, false, true, false, false, false, true, false, false]) := by
    convert h.1.2 4 8 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r48 : ((b 4 8) ^^ (b 4 9)) = false := by
  have hh := (xor_zero (e48 s b h) (r8 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e50 : ((s 5) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 4 5) ^^ (b 4 7) ^^ (b 4 8) ^^ (b 4 9) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![false, false, false, false, true, true, false, true, true, true, true]) = quadratic s b (![false, false, false, false, true, false, false, false, false, false, true]) := by
    convert h.1.2 4 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination hh

private lemma r50 : ((b 4 6) ^^ (b 4 7) ^^ (b 4 8) ^^ (b 4 9)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (e50 s b h) (r5 s b h)) (r10 s b h)) (r45 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e53 : ((s 5) ^^ (s 6) ^^ (s 8) ^^ (s 9) ^^ (b 5 8) ^^ (b 6 9)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, false, true, false, false, true, false]) = quadratic s b (![false, false, false, false, false, true, false, false, true, false, false]) := by
    convert h.1.2 5 8 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r53 : ((b 5 8) ^^ (b 6 9)) = false := by
  have hh := (xor_zero (xor_zero (e53 s b h) (r5 s b h)) (r8 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e54 : ((s 5) ^^ (s 6) ^^ (s 8) ^^ (s 9) ^^ (b 5 9) ^^ (b 6 8)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, false, true, false, true, false, false]) = quadratic s b (![false, false, false, false, false, true, false, false, false, true, false]) := by
    convert h.1.2 5 9 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r54 : ((b 5 9) ^^ (b 6 8)) = false := by
  have hh := (xor_zero (xor_zero (e54 s b h) (r5 s b h)) (r8 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e55 : ((s 6) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 5 6) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 6 7) ^^ (b 6 8) ^^ (b 6 9) ^^ (b 6 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, true, true, true, true, true]) = quadratic s b (![false, false, false, false, false, true, false, false, false, false, true]) := by
    convert h.1.2 5 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination hh

private lemma r55 : ((b 5 7) ^^ (b 5 10) ^^ (b 6 8) ^^ (b 6 9) ^^ (b 6 10)) = false := by
  have hh := (xor_zero (xor_zero (e55 s b h) (r10 s b h)) (r7 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e60 : ((s 5) ^^ (s 6) ^^ (s 8) ^^ (s 9) ^^ (b 5 6) ^^ (b 5 7) ^^ (b 5 9) ^^ (b 6 7) ^^ (b 6 9) ^^ (b 7 8) ^^ (b 7 9)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, true, true, false, true, false]) = quadratic s b (![false, false, false, false, false, false, false, true, true, false, false]) := by
    convert h.1.2 7 8 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r60 : ((b 6 8) ^^ (b 6 9) ^^ (b 7 8) ^^ (b 7 9)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (e60 s b h) (r5 s b h)) (r8 s b h)) (r7 s b h)) (r54 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e64 : ((s 5) ^^ (s 7) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 10)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, false, true, true, false, true]) = quadratic s b (![false, false, false, false, false, false, false, false, true, false, true]) := by
    convert h.1.2 8 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination hh

private lemma r64 : ((b 6 9) ^^ (b 7 8) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e64 s b h) (r5 s b h)) (r10 s b h)) (r8 s b h)) (r54 s b h)) (r60 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e66 : ((s 0) ^^ (s 2)) = false := by
  have hh : quadratic s b (![false, false, true, false, false, false, false, false, false, false, false]) = quadratic s b (![true, false, false, false, false, false, false, false, false, false, false]) := by
    convert h.2.1 0 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r66 : ((s 1) ^^ (s 2)) = false := by
  have hh := (xor_zero (e66 s b h) (r0 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e69 : ((s 3) ^^ (s 4)) = false := by
  have hh : quadratic s b (![false, false, false, false, true, false, false, false, false, false, false]) = quadratic s b (![false, false, false, true, false, false, false, false, false, false, false]) := by
    convert h.2.1 3 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r69 : ((s 3) ^^ (s 4)) = false := by
  exact e69 s b h

private lemma e70 : ((s 4) ^^ (s 5)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, false, false, false, false, false]) = quadratic s b (![false, false, false, false, true, false, false, false, false, false, false]) := by
    convert h.2.1 4 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r70 : ((s 4) ^^ (s 5)) = false := by
  exact e70 s b h

private lemma e72 : ((s 6) ^^ (s 7)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, false, false, true, false, false, false]) = quadratic s b (![false, false, false, false, false, false, true, false, false, false, false]) := by
    convert h.2.1 6 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r72 : ((b 6 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e72 s b h) (r10 s b h)) (r8 s b h)) (r55 s b h)) (r53 s b h)) (r54 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e73 : ((s 7) ^^ (s 8)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, false, false, false, true, false, false]) = quadratic s b (![false, false, false, false, false, false, false, true, false, false, false]) := by
    convert h.2.1 7 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r73 : ((s 7) ^^ (s 8)) = false := by
  exact e73 s b h

private lemma e75 : ((s 9) ^^ (s 10)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, false, false, false, false, false, true]) = quadratic s b (![false, false, false, false, false, false, false, false, false, true, false]) := by
    convert h.2.1 9 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r75 : ((s 9) ^^ (s 10)) = false := by
  exact e75 s b h

private lemma e76 : ((s 0) ^^ (s 1) ^^ (s 2) ^^ (s 6) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 0 1) ^^ (b 0 2) ^^ (b 0 6) ^^ (b 0 7) ^^ (b 0 8) ^^ (b 0 9) ^^ (b 0 10) ^^ (b 1 2) ^^ (b 1 6) ^^ (b 1 7) ^^ (b 1 8) ^^ (b 1 9) ^^ (b 1 10) ^^ (b 2 6) ^^ (b 2 7) ^^ (b 2 8) ^^ (b 2 9) ^^ (b 2 10) ^^ (b 6 7) ^^ (b 6 8) ^^ (b 6 9) ^^ (b 6 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![true, true, true, false, false, false, true, true, true, true, true]) = quadratic s b (![false, false, false, false, false, false, false, false, false, false, true]) := by
    convert h.2.1 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination hh

private lemma r76 : ((s 10) ^^ (b 0 1) ^^ (b 0 2) ^^ (b 0 6) ^^ (b 0 7) ^^ (b 0 8) ^^ (b 0 9) ^^ (b 0 10) ^^ (b 1 2) ^^ (b 1 6) ^^ (b 1 7) ^^ (b 1 8) ^^ (b 1 9) ^^ (b 1 10) ^^ (b 2 6) ^^ (b 2 7) ^^ (b 2 8) ^^ (b 2 9) ^^ (b 2 10) ^^ (b 6 7) ^^ (b 6 8) ^^ (b 6 9) ^^ (b 6 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e76 s b h) (r0 s b h)) (r2 s b h)) (r69 s b h)) (r70 s b h)) (r5 s b h)) (r73 s b h)) (r75 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e77 : ((s 1) ^^ (s 2) ^^ (b 0 1) ^^ (b 0 2)) = false := by
  have hh : quadratic s b (![true, false, true, false, false, false, false, false, false, false, false]) = quadratic s b (![true, true, false, false, false, false, false, false, false, false, false]) := by
    convert h.2.2 0 1 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r77 : ((b 0 1) ^^ (b 0 2)) = false := by
  have hh := (xor_zero (e77 s b h) (r66 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e78 : ((s 0) ^^ (s 1) ^^ (b 0 2) ^^ (b 1 2)) = false := by
  have hh : quadratic s b (![false, true, true, false, false, false, false, false, false, false, false]) = quadratic s b (![true, false, true, false, false, false, false, false, false, false, false]) := by
    convert h.2.2 0 2 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r78 : ((b 1 2) ^^ (b 1 3)) = false := by
  have hh := (xor_zero (xor_zero (e78 s b h) (r0 s b h)) (r12 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e79 : ((s 0) ^^ (s 2) ^^ (s 3) ^^ (s 4) ^^ (b 0 3) ^^ (b 2 4)) = false := by
  have hh : quadratic s b (![false, false, true, false, true, false, false, false, false, false, false]) = quadratic s b (![true, false, false, true, false, false, false, false, false, false, false]) := by
    convert h.2.2 0 3 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r79 : ((b 1 3) ^^ (b 2 4)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e79 s b h) (r0 s b h)) (r66 s b h)) (r69 s b h)) (r13 s b h)) (r78 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e80 : ((s 0) ^^ (s 2) ^^ (s 4) ^^ (s 5) ^^ (b 0 4) ^^ (b 2 5)) = false := by
  have hh : quadratic s b (![false, false, true, false, false, true, false, false, false, false, false]) = quadratic s b (![true, false, false, false, true, false, false, false, false, false, false]) := by
    convert h.2.2 0 4 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r80 : ((b 1 4) ^^ (b 2 5)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (e80 s b h) (r0 s b h)) (r66 s b h)) (r70 s b h)) (r14 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e81 : ((s 0) ^^ (s 2) ^^ (s 3) ^^ (s 5) ^^ (b 0 5) ^^ (b 2 3)) = false := by
  have hh : quadratic s b (![false, false, true, true, false, false, false, false, false, false, false]) = quadratic s b (![true, false, false, false, false, true, false, false, false, false, false]) := by
    convert h.2.2 0 5 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r81 : ((b 1 6) ^^ (b 2 3)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e81 s b h) (r0 s b h)) (r66 s b h)) (r69 s b h)) (r70 s b h)) (r15 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e82 : ((s 0) ^^ (s 2) ^^ (s 6) ^^ (s 7) ^^ (b 0 6) ^^ (b 2 7)) = false := by
  have hh : quadratic s b (![false, false, true, false, false, false, false, true, false, false, false]) = quadratic s b (![true, false, false, false, false, false, true, false, false, false, false]) := by
    convert h.2.2 0 6 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r82 : ((b 1 5) ^^ (b 2 7) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e82 s b h) (r0 s b h)) (r66 s b h)) (r10 s b h)) (r8 s b h)) (r16 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e83 : ((s 0) ^^ (s 2) ^^ (s 7) ^^ (s 8) ^^ (b 0 7) ^^ (b 2 8)) = false := by
  have hh : quadratic s b (![false, false, true, false, false, false, false, false, true, false, false]) = quadratic s b (![true, false, false, false, false, false, false, true, false, false, false]) := by
    convert h.2.2 0 7 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r83 : ((b 1 7) ^^ (b 2 3) ^^ (b 2 7) ^^ (b 2 8) ^^ (b 5 6) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 6 7) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e83 s b h) (r0 s b h)) (r66 s b h)) (r73 s b h)) (r17 s b h)) (r82 s b h)) (r81 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e84 : ((s 0) ^^ (s 2) ^^ (s 6) ^^ (s 8) ^^ (b 0 8) ^^ (b 2 6)) = false := by
  have hh : quadratic s b (![false, false, true, false, false, false, true, false, false, false, false]) = quadratic s b (![true, false, false, false, false, false, false, false, true, false, false]) := by
    convert h.2.2 0 8 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r84 : ((b 1 9) ^^ (b 2 6) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e84 s b h) (r0 s b h)) (r66 s b h)) (r10 s b h)) (r73 s b h)) (r8 s b h)) (r18 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e85 : ((s 0) ^^ (s 2) ^^ (s 9) ^^ (s 10) ^^ (b 0 9) ^^ (b 2 10)) = false := by
  have hh : quadratic s b (![false, false, true, false, false, false, false, false, false, false, true]) = quadratic s b (![true, false, false, false, false, false, false, false, false, true, false]) := by
    convert h.2.2 0 9 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r85 : ((b 1 8) ^^ (b 2 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (e85 s b h) (r0 s b h)) (r66 s b h)) (r75 s b h)) (r19 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e86 : ((s 1) ^^ (s 6) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 0 1) ^^ (b 0 6) ^^ (b 0 7) ^^ (b 0 8) ^^ (b 0 9) ^^ (b 1 6) ^^ (b 1 7) ^^ (b 1 8) ^^ (b 1 9) ^^ (b 1 10) ^^ (b 6 7) ^^ (b 6 8) ^^ (b 6 9) ^^ (b 6 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![true, true, false, false, false, false, true, true, true, true, true]) = quadratic s b (![true, false, false, false, false, false, false, false, false, false, true]) := by
    convert h.2.2 0 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination hh

private lemma r86 : ((b 1 10) ^^ (b 2 3) ^^ (b 2 7) ^^ (b 2 9) ^^ (b 5 6) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 6 7) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e86 s b h) (r66 s b h)) (r2 s b h)) (r69 s b h)) (r70 s b h)) (r5 s b h)) (r73 s b h)) (r75 s b h)) (r76 s b h)) (r12 s b h)) (r20 s b h)) (r78 s b h)) (r82 s b h)) (r83 s b h)) (r85 s b h)) (r84 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e88 : ((s 0) ^^ (s 1) ^^ (s 3) ^^ (s 4) ^^ (b 0 4) ^^ (b 1 3)) = false := by
  have hh : quadratic s b (![true, false, false, false, true, false, false, false, false, false, false]) = quadratic s b (![false, true, false, true, false, false, false, false, false, false, false]) := by
    convert h.2.2 1 3 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r88 : ((b 3 4) ^^ (b 3 6)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e88 s b h) (r0 s b h)) (r69 s b h)) (r14 s b h)) (r79 s b h)) (r80 s b h)) (r31 s b h)) (r32 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e89 : ((s 0) ^^ (s 1) ^^ (s 4) ^^ (s 5) ^^ (b 0 5) ^^ (b 1 4)) = false := by
  have hh : quadratic s b (![true, false, false, false, false, true, false, false, false, false, false]) = quadratic s b (![false, true, false, false, true, false, false, false, false, false, false]) := by
    convert h.2.2 1 4 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r89 : ((b 2 3) ^^ (b 2 5)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e89 s b h) (r0 s b h)) (r70 s b h)) (r15 s b h)) (r80 s b h)) (r81 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e90 : ((s 0) ^^ (s 1) ^^ (s 3) ^^ (s 5) ^^ (b 0 3) ^^ (b 1 5)) = false := by
  have hh : quadratic s b (![true, false, false, true, false, false, false, false, false, false, false]) = quadratic s b (![false, true, false, false, false, true, false, false, false, false, false]) := by
    convert h.2.2 1 5 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r90 : ((b 3 5) ^^ (b 3 7) ^^ (b 5 6) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 6 7) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e90 s b h) (r0 s b h)) (r69 s b h)) (r70 s b h)) (r13 s b h)) (r78 s b h)) (r79 s b h)) (r82 s b h)) (r31 s b h)) (r34 s b h)) (r88 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e91 : ((s 0) ^^ (s 1) ^^ (s 6) ^^ (s 7) ^^ (b 0 7) ^^ (b 1 6)) = false := by
  have hh : quadratic s b (![true, false, false, false, false, false, false, true, false, false, false]) = quadratic s b (![false, true, false, false, false, false, true, false, false, false, false]) := by
    convert h.2.2 1 6 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r91 : ((b 3 6) ^^ (b 3 9) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e91 s b h) (r0 s b h)) (r10 s b h)) (r8 s b h)) (r17 s b h)) (r82 s b h)) (r83 s b h)) (r89 s b h)) (r32 s b h)) (r35 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e92 : ((s 0) ^^ (s 1) ^^ (s 7) ^^ (s 8) ^^ (b 0 8) ^^ (b 1 7)) = false := by
  have hh : quadratic s b (![true, false, false, false, false, false, false, false, true, false, false]) = quadratic s b (![false, true, false, false, false, false, false, true, false, false, false]) := by
    convert h.2.2 1 7 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r92 : ((b 3 7) ^^ (b 3 9)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e92 s b h) (r0 s b h)) (r73 s b h)) (r18 s b h)) (r83 s b h)) (r84 s b h)) (r89 s b h)) (r32 s b h)) (r33 s b h)) (r34 s b h)) (r35 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e93 : ((s 0) ^^ (s 1) ^^ (s 6) ^^ (s 8) ^^ (b 0 6) ^^ (b 1 8)) = false := by
  have hh : quadratic s b (![true, false, false, false, false, false, true, false, false, false, false]) = quadratic s b (![false, true, false, false, false, false, false, false, true, false, false]) := by
    convert h.2.2 1 8 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r93 : ((b 3 8) ^^ (b 3 10) ^^ (b 5 6) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 6 7) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e93 s b h) (r0 s b h)) (r10 s b h)) (r73 s b h)) (r8 s b h)) (r16 s b h)) (r82 s b h)) (r85 s b h)) (r34 s b h)) (r37 s b h)) (r91 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e94 : ((s 0) ^^ (s 1) ^^ (s 9) ^^ (s 10) ^^ (b 0 10) ^^ (b 1 9)) = false := by
  have hh : quadratic s b (![true, false, false, false, false, false, false, false, false, false, true]) = quadratic s b (![false, true, false, false, false, false, false, false, false, true, false]) := by
    convert h.2.2 1 9 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r94 : ((b 3 9) ^^ (b 3 10) ^^ (b 5 6) ^^ (b 5 7) ^^ (b 6 7)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e94 s b h) (r0 s b h)) (r75 s b h)) (r20 s b h)) (r82 s b h)) (r83 s b h)) (r85 s b h)) (r86 s b h)) (r34 s b h)) (r35 s b h)) (r36 s b h)) (r37 s b h)) (r91 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e104 : ((s 3) ^^ (s 5) ^^ (b 3 4) ^^ (b 4 5)) = false := by
  have hh : quadratic s b (![false, false, false, false, true, true, false, false, false, false, false]) = quadratic s b (![false, false, false, true, true, false, false, false, false, false, false]) := by
    convert h.2.2 3 4 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r104 : ((b 3 10) ^^ (b 4 5) ^^ (b 5 6) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 6 7) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e104 s b h) (r69 s b h)) (r70 s b h)) (r88 s b h)) (r91 s b h)) (r94 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e107 : ((s 3) ^^ (s 4) ^^ (s 7) ^^ (s 8) ^^ (b 3 7) ^^ (b 4 8)) = false := by
  have hh : quadratic s b (![false, false, false, false, true, false, false, false, true, false, false]) = quadratic s b (![false, false, false, true, false, false, false, true, false, false, false]) := by
    convert h.2.2 3 7 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r107 : ((b 4 7) ^^ (b 4 9) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e107 s b h) (r69 s b h)) (r73 s b h)) (r92 s b h)) (r94 s b h)) (r104 s b h)) (r45 s b h)) (r50 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e109 : ((s 3) ^^ (s 4) ^^ (s 9) ^^ (s 10) ^^ (b 3 9) ^^ (b 4 10)) = false := by
  have hh : quadratic s b (![false, false, false, false, true, false, false, false, false, false, true]) = quadratic s b (![false, false, false, true, false, false, false, false, false, true, false]) := by
    convert h.2.2 3 9 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r109 : ((b 4 9) ^^ (b 4 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e109 s b h) (r69 s b h)) (r75 s b h)) (r94 s b h)) (r104 s b h)) (r45 s b h)) (r50 s b h)) (r107 s b h)) (r48 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e110 : ((s 0) ^^ (s 1) ^^ (s 2) ^^ (s 3) ^^ (s 4) ^^ (s 6) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 0 1) ^^ (b 0 2) ^^ (b 0 4) ^^ (b 0 6) ^^ (b 0 7) ^^ (b 0 8) ^^ (b 0 9) ^^ (b 0 10) ^^ (b 1 2) ^^ (b 1 4) ^^ (b 1 6) ^^ (b 1 7) ^^ (b 1 8) ^^ (b 1 9) ^^ (b 1 10) ^^ (b 2 4) ^^ (b 2 6) ^^ (b 2 7) ^^ (b 2 8) ^^ (b 2 9) ^^ (b 2 10) ^^ (b 3 10) ^^ (b 4 6) ^^ (b 4 7) ^^ (b 4 8) ^^ (b 4 9) ^^ (b 4 10) ^^ (b 6 7) ^^ (b 6 8) ^^ (b 6 9) ^^ (b 6 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![true, true, true, false, true, false, true, true, true, true, true]) = quadratic s b (![false, false, false, true, false, false, false, false, false, false, true]) := by
    convert h.2.2 3 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r110 : ((b 4 10) ^^ (b 5 6) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 6 7) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e110 s b h) (r0 s b h)) (r2 s b h)) (r70 s b h)) (r5 s b h)) (r73 s b h)) (r75 s b h)) (r76 s b h)) (r14 s b h)) (r31 s b h)) (r88 s b h)) (r91 s b h)) (r94 s b h)) (r50 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e112 : ((s 4) ^^ (s 5) ^^ (s 6) ^^ (s 7) ^^ (b 4 6) ^^ (b 5 7)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, false, true, false, false, false]) = quadratic s b (![false, false, false, false, true, false, true, false, false, false, false]) := by
    convert h.2.2 4 6 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r112 : ((b 5 10) ^^ (b 6 8) ^^ (b 6 9) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e112 s b h) (r70 s b h)) (r10 s b h)) (r8 s b h)) (r50 s b h)) (r107 s b h)) (r48 s b h)) (r109 s b h)) (r110 s b h)) (r7 s b h)) (r53 s b h)) (r54 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e113 : ((s 4) ^^ (s 5) ^^ (s 7) ^^ (s 8) ^^ (b 4 7) ^^ (b 5 8)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, false, false, true, false, false]) = quadratic s b (![false, false, false, false, true, false, false, true, false, false, false]) := by
    convert h.2.2 4 7 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r113 : ((b 7 8) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e113 s b h) (r70 s b h)) (r73 s b h)) (r107 s b h)) (r109 s b h)) (r110 s b h)) (r7 s b h)) (r53 s b h)) (r64 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e114 : ((s 4) ^^ (s 5) ^^ (s 6) ^^ (s 8) ^^ (b 4 8) ^^ (b 5 6)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, true, false, false, false, false]) = quadratic s b (![false, false, false, false, true, false, false, false, true, false, false]) := by
    convert h.2.2 4 8 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r114 : ((b 6 7) ^^ (b 6 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e114 s b h) (r70 s b h)) (r10 s b h)) (r73 s b h)) (r8 s b h)) (r48 s b h)) (r109 s b h)) (r110 s b h)) (r55 s b h)) (r112 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e115 : ((s 4) ^^ (s 5) ^^ (s 9) ^^ (s 10) ^^ (b 4 9) ^^ (b 5 10)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, true, false, false, false, false, true]) = quadratic s b (![false, false, false, false, true, false, false, false, false, true, false]) := by
    convert h.2.2 4 9 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r115 : ((b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e115 s b h) (r70 s b h)) (r75 s b h)) (r109 s b h)) (r110 s b h)) (r7 s b h)) (r55 s b h)) (r53 s b h)) (r54 s b h)) (r112 s b h)) (r60 s b h)) (r72 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e116 : ((s 0) ^^ (s 1) ^^ (s 2) ^^ (s 4) ^^ (s 5) ^^ (s 6) ^^ (s 7) ^^ (s 8) ^^ (s 9) ^^ (b 0 1) ^^ (b 0 2) ^^ (b 0 5) ^^ (b 0 6) ^^ (b 0 7) ^^ (b 0 8) ^^ (b 0 9) ^^ (b 0 10) ^^ (b 1 2) ^^ (b 1 5) ^^ (b 1 6) ^^ (b 1 7) ^^ (b 1 8) ^^ (b 1 9) ^^ (b 1 10) ^^ (b 2 5) ^^ (b 2 6) ^^ (b 2 7) ^^ (b 2 8) ^^ (b 2 9) ^^ (b 2 10) ^^ (b 4 10) ^^ (b 5 6) ^^ (b 5 7) ^^ (b 5 8) ^^ (b 5 9) ^^ (b 5 10) ^^ (b 6 7) ^^ (b 6 8) ^^ (b 6 9) ^^ (b 6 10) ^^ (b 7 8) ^^ (b 7 9) ^^ (b 7 10) ^^ (b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![true, true, true, false, false, true, true, true, true, true, true]) = quadratic s b (![false, false, false, false, true, false, false, false, false, false, true]) := by
    convert h.2.2 4 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r116 : ((b 7 9) ^^ (b 7 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e116 s b h) (r0 s b h)) (r2 s b h)) (r69 s b h)) (r5 s b h)) (r73 s b h)) (r75 s b h)) (r76 s b h)) (r15 s b h)) (r82 s b h)) (r81 s b h)) (r89 s b h)) (r34 s b h)) (r90 s b h)) (r91 s b h)) (r94 s b h)) (r104 s b h)) (r45 s b h)) (r50 s b h)) (r107 s b h)) (r48 s b h)) (r109 s b h)) (r7 s b h)) (r55 s b h)) (r112 s b h)) (r114 s b h)) (r113 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e122 : ((s 6) ^^ (s 8) ^^ (b 6 7) ^^ (b 7 8)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, false, false, true, true, false, false]) = quadratic s b (![false, false, false, false, false, false, true, true, false, false, false]) := by
    convert h.2.2 6 7 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r122 : ((b 8 9) ^^ (b 8 10) ^^ (b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e122 s b h) (r10 s b h)) (r73 s b h)) (r8 s b h)) (r55 s b h)) (r53 s b h)) (r54 s b h)) (r114 s b h)) (r113 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e127 : ((s 7) ^^ (s 8) ^^ (s 9) ^^ (s 10) ^^ (b 7 9) ^^ (b 8 10)) = false := by
  have hh : quadratic s b (![false, false, false, false, false, false, false, false, true, false, true]) = quadratic s b (![false, false, false, false, false, false, false, true, false, true, false]) := by
    convert h.2.2 7 9 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma r127 : ((b 8 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e127 s b h) (r73 s b h)) (r75 s b h)) (r116 s b h)) (r115 s b h)) (r122 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma e128 : ((s 0) ^^ (s 1) ^^ (s 2) ^^ (s 6) ^^ (s 9) ^^ (b 0 1) ^^ (b 0 2) ^^ (b 0 6) ^^ (b 0 7) ^^ (b 0 9) ^^ (b 0 10) ^^ (b 1 2) ^^ (b 1 6) ^^ (b 1 7) ^^ (b 1 9) ^^ (b 1 10) ^^ (b 2 6) ^^ (b 2 7) ^^ (b 2 9) ^^ (b 2 10) ^^ (b 6 7) ^^ (b 6 9) ^^ (b 6 10) ^^ (b 7 9) ^^ (b 9 10)) = false := by
  have hh : quadratic s b (![true, true, true, false, false, false, true, true, false, true, true]) = quadratic s b (![false, false, false, false, false, false, false, true, false, false, true]) := by
    convert h.2.2 7 10 using 1 <;> congr 1 <;> decide +kernel
  simp [quadratic_expand] at hh
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination hh

private lemma r128 : ((b 9 10)) = false := by
  have hh := (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (xor_zero (e128 s b h) (r0 s b h)) (r2 s b h)) (r69 s b h)) (r70 s b h)) (r5 s b h)) (r75 s b h)) (r76 s b h)) (r18 s b h)) (r85 s b h)) (r84 s b h)) (r33 s b h)) (r35 s b h)) (r37 s b h)) (r92 s b h)) (r93 s b h)) (r94 s b h)) (r104 s b h)) (r45 s b h)) (r50 s b h)) (r107 s b h)) (r48 s b h)) (r109 s b h)) (r110 s b h)) (r55 s b h)) (r53 s b h)) (r54 s b h)) (r60 s b h)) (r64 s b h)) (r72 s b h)) (r113 s b h)) (r116 s b h)) (r122 s b h))
  simp only [← Bool.add_eq_xor, ← Bool.zero_eq_false] at hh ⊢
  linear_combination (norm := ring_nf) hh
  simp

private lemma c65 : b 9 10 = false := by
  exact r128 s b h

private lemma c64 : b 8 10 = false := by
  exact r127 s b h

private lemma c63 : b 8 9 = false := by
  simpa only [c64 s b h, c65 s b h, Bool.xor_false] using r122 s b h

private lemma c62 : b 7 10 = false := by
  simpa only [c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r115 s b h

private lemma c61 : b 7 9 = false := by
  simpa only [c62 s b h, Bool.xor_false] using r116 s b h

private lemma c60 : b 7 8 = false := by
  simpa only [c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r113 s b h

private lemma c59 : b 6 10 = false := by
  simpa only [c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r72 s b h

private lemma c58 : b 6 9 = false := by
  simpa only [c60 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r64 s b h

private lemma c57 : b 6 8 = false := by
  simpa only [c58 s b h, c60 s b h, c61 s b h, Bool.xor_false] using r60 s b h

private lemma c56 : b 6 7 = false := by
  simpa only [c59 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r114 s b h

private lemma c55 : b 5 10 = false := by
  simpa only [c57 s b h, c58 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r112 s b h

private lemma c54 : b 5 9 = false := by
  simpa only [c57 s b h, Bool.xor_false] using r54 s b h

private lemma c53 : b 5 8 = false := by
  simpa only [c58 s b h, Bool.xor_false] using r53 s b h

private lemma c52 : b 5 7 = false := by
  simpa only [c55 s b h, c57 s b h, c58 s b h, c59 s b h, Bool.xor_false] using r55 s b h

private lemma c51 : b 5 6 = false := by
  simpa only [c52 s b h, c56 s b h, Bool.xor_false] using r7 s b h

private lemma c50 : b 4 10 = false := by
  simpa only [c51 s b h, c53 s b h, c54 s b h, c55 s b h, c56 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r110 s b h

private lemma c49 : b 4 9 = false := by
  simpa only [c50 s b h, Bool.xor_false] using r109 s b h

private lemma c48 : b 4 8 = false := by
  simpa only [c49 s b h, Bool.xor_false] using r48 s b h

private lemma c47 : b 4 7 = false := by
  simpa only [c49 s b h, c52 s b h, c53 s b h, c54 s b h, c55 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r107 s b h

private lemma c46 : b 4 6 = false := by
  simpa only [c47 s b h, c48 s b h, c49 s b h, Bool.xor_false] using r50 s b h

private lemma c45 : b 4 5 = false := by
  simpa only [c46 s b h, Bool.xor_false] using r45 s b h

private lemma c44 : b 3 10 = false := by
  simpa only [c45 s b h, c51 s b h, c53 s b h, c54 s b h, c55 s b h, c56 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r104 s b h

private lemma c43 : b 3 9 = false := by
  simpa only [c44 s b h, c51 s b h, c52 s b h, c56 s b h, Bool.xor_false] using r94 s b h

private lemma c42 : b 3 8 = false := by
  simpa only [c44 s b h, c51 s b h, c53 s b h, c54 s b h, c55 s b h, c56 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r93 s b h

private lemma c41 : b 3 7 = false := by
  simpa only [c43 s b h, Bool.xor_false] using r92 s b h

private lemma c40 : b 3 6 = false := by
  simpa only [c43 s b h, c52 s b h, c53 s b h, c54 s b h, c55 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r91 s b h

private lemma c39 : b 3 5 = false := by
  simpa only [c41 s b h, c51 s b h, c53 s b h, c54 s b h, c55 s b h, c56 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r90 s b h

private lemma c38 : b 3 4 = false := by
  simpa only [c40 s b h, Bool.xor_false] using r88 s b h

private lemma c37 : b 2 10 = false := by
  simpa only [c39 s b h, c41 s b h, c42 s b h, c43 s b h, c44 s b h, Bool.xor_false] using r37 s b h

private lemma c36 : b 2 9 = false := by
  simpa only [c42 s b h, Bool.xor_false] using r36 s b h

private lemma c35 : b 2 8 = false := by
  simpa only [c43 s b h, Bool.xor_false] using r35 s b h

private lemma c34 : b 2 7 = false := by
  simpa only [c39 s b h, c40 s b h, c41 s b h, c51 s b h, c52 s b h, c56 s b h, Bool.xor_false] using r34 s b h

private lemma c33 : b 2 6 = false := by
  simpa only [c39 s b h, Bool.xor_false] using r33 s b h

private lemma c32 : b 2 5 = false := by
  simpa only [c40 s b h, Bool.xor_false] using r32 s b h

private lemma c31 : b 2 4 = false := by
  simpa only [c38 s b h, Bool.xor_false] using r31 s b h

private lemma c30 : b 2 3 = false := by
  simpa only [c32 s b h, Bool.xor_false] using r89 s b h

private lemma c29 : b 1 10 = false := by
  simpa only [c30 s b h, c34 s b h, c36 s b h, c51 s b h, c53 s b h, c54 s b h, c55 s b h, c56 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r86 s b h

private lemma c28 : b 1 9 = false := by
  simpa only [c33 s b h, c52 s b h, c53 s b h, c54 s b h, c55 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r84 s b h

private lemma c27 : b 1 8 = false := by
  simpa only [c37 s b h, Bool.xor_false] using r85 s b h

private lemma c26 : b 1 7 = false := by
  simpa only [c30 s b h, c34 s b h, c35 s b h, c51 s b h, c53 s b h, c54 s b h, c55 s b h, c56 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r83 s b h

private lemma c25 : b 1 6 = false := by
  simpa only [c30 s b h, Bool.xor_false] using r81 s b h

private lemma c24 : b 1 5 = false := by
  simpa only [c34 s b h, c52 s b h, c53 s b h, c54 s b h, c55 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r82 s b h

private lemma c23 : b 1 4 = false := by
  simpa only [c32 s b h, Bool.xor_false] using r80 s b h

private lemma c22 : b 1 3 = false := by
  simpa only [c31 s b h, Bool.xor_false] using r79 s b h

private lemma c21 : b 1 2 = false := by
  simpa only [c22 s b h, Bool.xor_false] using r78 s b h

private lemma c20 : b 0 10 = false := by
  simpa only [c24 s b h, c26 s b h, c27 s b h, c28 s b h, c29 s b h, Bool.xor_false] using r20 s b h

private lemma c19 : b 0 9 = false := by
  simpa only [c27 s b h, Bool.xor_false] using r19 s b h

private lemma c18 : b 0 8 = false := by
  simpa only [c28 s b h, Bool.xor_false] using r18 s b h

private lemma c17 : b 0 7 = false := by
  simpa only [c24 s b h, c25 s b h, c26 s b h, c51 s b h, c52 s b h, c56 s b h, Bool.xor_false] using r17 s b h

private lemma c16 : b 0 6 = false := by
  simpa only [c24 s b h, Bool.xor_false] using r16 s b h

private lemma c15 : b 0 5 = false := by
  simpa only [c25 s b h, Bool.xor_false] using r15 s b h

private lemma c14 : b 0 4 = false := by
  simpa only [c23 s b h, Bool.xor_false] using r14 s b h

private lemma c13 : b 0 3 = false := by
  simpa only [c21 s b h, Bool.xor_false] using r13 s b h

private lemma c12 : b 0 2 = false := by
  simpa only [c22 s b h, Bool.xor_false] using r12 s b h

private lemma c11 : b 0 1 = false := by
  simpa only [c12 s b h, Bool.xor_false] using r77 s b h

private lemma c10 : s 10 = false := by
  simpa only [c11 s b h, c12 s b h, c16 s b h, c17 s b h, c18 s b h, c19 s b h, c20 s b h, c21 s b h, c25 s b h, c26 s b h, c27 s b h, c28 s b h, c29 s b h, c33 s b h, c34 s b h, c35 s b h, c36 s b h, c37 s b h, c56 s b h, c57 s b h, c58 s b h, c59 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r76 s b h

private lemma c9 : s 9 = false := by
  simpa only [c10 s b h, Bool.xor_false] using r75 s b h

private lemma c8 : s 8 = false := by
  simpa only [c9 s b h, Bool.xor_false] using r8 s b h

private lemma c7 : s 7 = false := by
  simpa only [c8 s b h, Bool.xor_false] using r73 s b h

private lemma c6 : s 6 = false := by
  simpa only [c7 s b h, c8 s b h, c9 s b h, c52 s b h, c53 s b h, c54 s b h, c55 s b h, c60 s b h, c61 s b h, c62 s b h, c63 s b h, c64 s b h, c65 s b h, Bool.xor_false] using r10 s b h

private lemma c5 : s 5 = false := by
  simpa only [c6 s b h, Bool.xor_false] using r5 s b h

private lemma c4 : s 4 = false := by
  simpa only [c5 s b h, Bool.xor_false] using r70 s b h

private lemma c3 : s 3 = false := by
  simpa only [c4 s b h, Bool.xor_false] using r69 s b h

private lemma c2 : s 2 = false := by
  simpa only [c3 s b h, Bool.xor_false] using r2 s b h

private lemma c1 : s 1 = false := by
  simpa only [c2 s b h, Bool.xor_false] using r66 s b h

private lemma c0 : s 0 = false := by
  simpa only [c1 s b h, Bool.xor_false] using r0 s b h

/-- The explicit elimination annihilates all sixty-six coefficients. -/
theorem coefficients_vanish :
    (∀ i, s i = false) ∧ (∀ i j, i < j → b i j = false) := by
  have c0 := c0 s b h
  have c1 := c1 s b h
  have c2 := c2 s b h
  have c3 := c3 s b h
  have c4 := c4 s b h
  have c5 := c5 s b h
  have c6 := c6 s b h
  have c7 := c7 s b h
  have c8 := c8 s b h
  have c9 := c9 s b h
  have c10 := c10 s b h
  have c11 := c11 s b h
  have c12 := c12 s b h
  have c13 := c13 s b h
  have c14 := c14 s b h
  have c15 := c15 s b h
  have c16 := c16 s b h
  have c17 := c17 s b h
  have c18 := c18 s b h
  have c19 := c19 s b h
  have c20 := c20 s b h
  have c21 := c21 s b h
  have c22 := c22 s b h
  have c23 := c23 s b h
  have c24 := c24 s b h
  have c25 := c25 s b h
  have c26 := c26 s b h
  have c27 := c27 s b h
  have c28 := c28 s b h
  have c29 := c29 s b h
  have c30 := c30 s b h
  have c31 := c31 s b h
  have c32 := c32 s b h
  have c33 := c33 s b h
  have c34 := c34 s b h
  have c35 := c35 s b h
  have c36 := c36 s b h
  have c37 := c37 s b h
  have c38 := c38 s b h
  have c39 := c39 s b h
  have c40 := c40 s b h
  have c41 := c41 s b h
  have c42 := c42 s b h
  have c43 := c43 s b h
  have c44 := c44 s b h
  have c45 := c45 s b h
  have c46 := c46 s b h
  have c47 := c47 s b h
  have c48 := c48 s b h
  have c49 := c49 s b h
  have c50 := c50 s b h
  have c51 := c51 s b h
  have c52 := c52 s b h
  have c53 := c53 s b h
  have c54 := c54 s b h
  have c55 := c55 s b h
  have c56 := c56 s b h
  have c57 := c57 s b h
  have c58 := c58 s b h
  have c59 := c59 s b h
  have c60 := c60 s b h
  have c61 := c61 s b h
  have c62 := c62 s b h
  have c63 := c63 s b h
  have c64 := c64 s b h
  have c65 := c65 s b h
  constructor
  · intro i
    fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | assumption | contradiction
end

/-- The certified action fixes no nonzero binary quadratic polynomial. -/
theorem invariant_quadratic_zero (s : Fin 11 → Bool) (b : Fin 11 → Fin 11 → Bool)
    (hx : TableInvariant (quadratic s b) xMasks)
    (hy : TableInvariant (quadratic s b) yMasks)
    (v : Fin 11 → Bool) : quadratic s b v = false := by
  obtain ⟨hs, hb⟩ := coefficients_vanish s b ⟨hx, hy⟩
  exact quadratic_zero s b hs hb v
end Janko4.TwoPrimary.JankoElementary
