/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/BinaryWalshSquare.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.BinaryWalshQuadratic

/-!
# Squared quadratic Walsh coefficients

Translate the double character sum and apply polar orthogonality.
The coefficient square is the space cardinality times the radical
cardinality precisely for compatible characters.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/BinaryWalshSquare.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Use `if_pos` and `if_neg` for the conditional reduction lemmas.
Definitions remain exposed for the source computational interfaces.
-/

@[expose] public section

namespace Atlas.Algebra

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

theorem binaryWalsh_polar_sum (q : QuadraticMap (ZMod 2) V (ZMod 2)) (t : V) :
    ∑ x, binaryWalshSign (q.polarBilin t x) =
      if t ∈ binaryWalshRadical q then (Fintype.card V : ℤ) else 0 := by
  have hh : (q.polarBilin t).toAddMonoidHom = 0 ↔ t ∈ binaryWalshRadical q := by
    change (q.polarBilin t).toAddMonoidHom = 0 ↔ q.polarBilin t = 0
    constructor
    · intro h
      ext x
      exact DFunLike.congr_fun h x
    · intro h
      rw [h]
      rfl
  have hs := binaryWalshChar_sum (q.polarBilin t).toAddMonoidHom
  change (∑ x, binaryWalshSign (q.polarBilin t x)) = _ at hs
  simpa only [hh] using hs

omit [Fintype V] in
theorem binaryWalsh_shift_product (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) (x t : V) :
    binaryWalshSign (q x + a x) * binaryWalshSign (q (x + t) + a (x + t)) =
      binaryWalshSign (q t + a t) * binaryWalshSign (q.polarBilin t x) := by
  rw [← binaryWalshSign_add, ← binaryWalshSign_add]
  congr 1
  rw [binaryWalsh_quadratic_add, map_add]
  have hb : q.polarBilin x t = q.polarBilin t x := QuadraticMap.polar_comm q x t
  rw [hb]
  calc
    _ = (q x + a x) + (q x + a x) + (q t + a t + q.polarBilin t x) := by ac_rfl
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- The exact squared Walsh coefficient before evaluating the radical character. -/
theorem binaryWalsh_sq_radical_sum (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) :
    binaryWalsh q a ^ 2 = (Fintype.card V : ℤ) *
      ∑ t : binaryWalshRadical q, binaryWalshRadicalChar q a t := by
  classical
  calc
    binaryWalsh q a ^ 2 = ∑ x, ∑ t,
        binaryWalshSign (q x + a x) * binaryWalshSign (q (x + t) + a (x + t)) := by
      rw [pow_two, binaryWalsh, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)).symm
    _ = ∑ t, binaryWalshSign (q t + a t) * ∑ x, binaryWalshSign (q.polarBilin t x) := by
      simp only [binaryWalsh_shift_product]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = (Fintype.card V : ℤ) *
        ∑ t, if t ∈ binaryWalshRadical q then binaryWalshSign (q t + a t) else 0 := by
      simp only [binaryWalsh_polar_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> ring
    _ = _ := by
      congr 1
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

/-- A normalized quadratic Walsh coefficient vanishes off the radical-compatible
characters; on that support its square is |V| times the cardinality of the radical. -/
theorem binaryWalsh_sq (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) :
    binaryWalsh q a ^ 2 = if BinaryWalshCompatible q a then
      (Fintype.card V : ℤ) * Fintype.card (binaryWalshRadical q) else 0 := by
  rw [binaryWalsh_sq_radical_sum, AddChar.sum_eq_ite]
  simp only [binaryWalshRadicalChar_eq_zero]
  split_ifs <;> simp

theorem binaryWalsh_eq_zero_of_not_compatible (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) (ha : ¬ BinaryWalshCompatible q a) : binaryWalsh q a = 0 := by
  have h := binaryWalsh_sq q a
  rw [if_neg ha] at h
  exact mul_self_eq_zero.mp (by simpa only [pow_two] using h)

theorem binaryWalsh_sq_of_compatible (q : QuadraticMap (ZMod 2) V (ZMod 2))
    (a : V →+ ZMod 2) (ha : BinaryWalshCompatible q a) :
    binaryWalsh q a ^ 2 = (Fintype.card V : ℤ) * Fintype.card (binaryWalshRadical q) := by
  rw [binaryWalsh_sq, if_pos ha]

end Atlas.Algebra
