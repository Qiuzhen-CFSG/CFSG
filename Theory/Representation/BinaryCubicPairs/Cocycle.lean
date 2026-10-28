module

public import Theory.Representation.BinaryCubicPairs.Certificate
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Interpreting the cubic-pair word certificates

The same word is evaluated in an arbitrary group and in the actual matrix
representation. Its two displacement coefficients follow from the cocycle
identity. This structural comparison is independent of the finite table,
and applies to every vector in an ambient module with trivial quotient by
the four-dimensional supporting space.

Source application: the cubic-pair reduction for Aschbacher--Smith E.6.24,
printed p.255. The finite matrix checks are consumed only through their
proved certificate interface.
-/

@[expose] public section
namespace BinaryCubicPairs
open Packed

def groupWord {G : Type*} [Monoid G] (c d : G) : List Bool → G
  | [] => 1
  | b :: w => (if b then d else c) * groupWord c d w

variable {G : Type*} [Group G] (μ : G →* CoordinateMatrix)
  (c d : G) (m : BitVec 16)
  (hc : μ c = toMat cubic) (hd : μ d = toMat m)
include hc hd

/-- Word evaluation commutes with the actual matrix homomorphism. -/
theorem matrix_groupWord (w : List Bool) :
    μ (groupWord c d w) = toMat (word m w) := by
  induction w with
  | nil => exact (map_one μ).trans toMat_one.symm
  | cons b w ih =>
    cases b <;> simp only [groupWord, word, Bool.false_eq_true, ↓reduceIte,
      map_mul, hc, hd, ih, toMat_mm]

/-- The checked displacement coefficients are the coefficients of every
one-cocycle for the given representation. -/
theorem cocycle_groupWord (δ : G → CoordinateVector)
    (hδ1 : δ 1 = 0)
    (hδ : ∀ g h : G, δ (g * h) = δ g + (μ g).mulVec (δ h))
    (w : List Bool) :
    δ (groupWord c d w) =
      (toMat (coefficients m w).1).mulVec (δ c) +
        (toMat (coefficients m w).2).mulVec (δ d) := by
  induction w with
  | nil => simp only [groupWord, coefficients, hδ1, toMat_zero, Matrix.zero_mulVec, add_zero]
  | cons b w ih =>
    cases b <;>
      simp only [groupWord, coefficients, Bool.false_eq_true, ↓reduceIte,
        hδ, hc, hd, ih, toMat_mm, toMat_xor, ident, toMat_one,
        Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec] <;>
      abel

/-- A nonidentity involution in the checked image lifts to a genuine
involution whenever restriction to the supporting space is faithful. -/
theorem orderOf_groupWord (hμ : Function.Injective μ) {k : Certificate}
    (hk : Valid m k) : orderOf (groupWord c d k.sequence) = 2 := by
  have hw := matrix_groupWord μ c d m hc hd k.sequence
  rw [hk.word_eq] at hw
  apply orderOf_eq_prime
  · apply hμ
    rw [map_pow, hw, pow_two, ← toMat_mm, hk.square, ident, toMat_one, map_one]
  · intro he
    apply hk.nontrivial
    apply toMat_injective
    rw [← hw, he, map_one, ident, toMat_one]

end BinaryCubicPairs
