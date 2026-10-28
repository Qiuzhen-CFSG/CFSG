module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Seven-point Sylow and elementary coordinates

The swaps (01), (23), (02)(13), (45) give sixteen distinct words forming
 a Sylow two-subgroup of S₇. The triples (01),(23),(45) and
 (01)(23),(02)(13),(45) give its two elementary subgroups of order eight.
 Explicit coordinate products keep the kernel-checked calculations small.

The coordinates are adapted from the independent permutation calculations in
 Chapter 13, `Seven/LocalGeometry/PermutationOvergroups/Coordinates.lean` and
 `Sylow.lean`; this module has no dependency on the classification layer.
 Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.8,
 printed p.389/PDF p.400, and the coordinates of 13.8.24.
-/

@[expose] public section

open Equiv Subgroup
namespace Representation.AlternatingSevenConjugatePair.ElementaryGeometry
abbrev S7 := Perm (Fin 7)
abbrev Triple := Fin 2 × Fin 2 × Fin 2
abbrev Quadruple := Fin 2 × Fin 2 × Fin 2 × Fin 2
def swap01 : S7 := swap 0 1
def swap23 : S7 := swap 2 3
def crossSwap : S7 := swap 0 2 * swap 1 3
def swap45 : S7 := swap 4 5
def word (v : Quadruple) : S7 := swap01 ^ v.1.val * swap23 ^ v.2.1.val * crossSwap ^ v.2.2.1.val * swap45 ^ v.2.2.2.val
def firstWord (v : Triple) : S7 := word (v.1, v.2.1, 0, v.2.2)
def secondWord (v : Triple) : S7 := word (v.1, v.1, v.2.1, v.2.2)
def mulBits (v w : Quadruple) : Quadruple :=
  (v.1 + (if v.2.2.1 = 0 then w.1 else w.2.1),
   v.2.1 + (if v.2.2.1 = 0 then w.2.1 else w.1),
   v.2.2.1 + w.2.2.1, v.2.2.2 + w.2.2.2)
def invBits (v : Quadruple) : Quadruple :=
  (if v.2.2.1 = 0 then v.1 else v.2.1,
   if v.2.2.1 = 0 then v.2.1 else v.1, v.2.2.1, v.2.2.2)

theorem word_mul : ∀ v w, word (mulBits v w) = word v * word w := by decide +kernel
theorem word_inv : ∀ v, word (invBits v) = (word v)⁻¹ := by decide +kernel

def addBits (v w : Triple) : Triple := (v.1 + w.1, v.2.1 + w.2.1, v.2.2 + w.2.2)
theorem firstWord_mul : ∀ v w, firstWord (addBits v w) = firstWord v * firstWord w := by decide +kernel
theorem secondWord_mul : ∀ v w, secondWord (addBits v w) = secondWord v * secondWord w := by decide +kernel
theorem firstWord_inv : ∀ v, firstWord v = (firstWord v)⁻¹ := by decide +kernel
theorem secondWord_inv : ∀ v, secondWord v = (secondWord v)⁻¹ := by decide +kernel

def rangeSubgroup {I : Type*} (f : I → S7)
    (ho : ∃ i, f i = 1) (hm : ∀ i j, ∃ k, f k = f i * f j)
    (hi : ∀ i, ∃ j, f j = (f i)⁻¹) : Subgroup S7 where
  carrier := Set.range f
  one_mem' := ho
  mul_mem' := by rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact hm i j
  inv_mem' := by rintro _ ⟨i, rfl⟩; exact hi i

set_option maxRecDepth 4096 in
def sylowTwo : Subgroup S7 := rangeSubgroup word (by decide +kernel)
  (fun v w => ⟨mulBits v w, word_mul v w⟩) (fun v => ⟨invBits v, word_inv v⟩)

set_option maxRecDepth 4096 in
def pairElementary : Subgroup S7 := rangeSubgroup firstWord (by decide +kernel)
  (fun v w => ⟨addBits v w, firstWord_mul v w⟩) (fun v => ⟨v, firstWord_inv v⟩)

set_option maxRecDepth 4096 in
def fourTwoElementary : Subgroup S7 := rangeSubgroup secondWord (by decide +kernel)
  (fun v w => ⟨addBits v w, secondWord_mul v w⟩) (fun v => ⟨v, secondWord_inv v⟩)

theorem word_inj : Function.Injective word := by decide +kernel
theorem firstWord_inj : Function.Injective firstWord := by decide +kernel
theorem secondWord_inj : Function.Injective secondWord := by decide +kernel

theorem sylowTwo_card : Nat.card sylowTwo = 16 := by
  change Nat.card (Set.range word) = _
  rw [Nat.card_congr (Equiv.ofInjective word word_inj).symm]
  simp [Quadruple]

theorem pairElementary_card : Nat.card pairElementary = 8 := by
  change Nat.card (Set.range firstWord) = _
  rw [Nat.card_congr (Equiv.ofInjective firstWord firstWord_inj).symm]
  simp [Triple]

theorem fourTwoElementary_card : Nat.card fourTwoElementary = 8 := by
  change Nat.card (Set.range secondWord) = _
  rw [Nat.card_congr (Equiv.ofInjective secondWord secondWord_inj).symm]
  simp [Triple]

end Representation.AlternatingSevenConjugatePair.ElementaryGeometry
