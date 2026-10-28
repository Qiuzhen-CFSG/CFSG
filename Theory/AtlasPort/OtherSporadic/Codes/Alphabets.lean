/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

/-! The two quadratic alphabets share a binary vector space, not a quadratic form. -/
/-!
Binary quadratic alphabets and their common nondegenerate polar form.
Coordinate identities and the dimension formula for orthogonal complements give
the self-duality criterion used by the code constructions.

Source: `Atlas/Codes/Alphabets.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
abbrev Bit := ZMod 2
@[simp] theorem bit_two : (2 : Bit) = 0 := by decide
@[simp] theorem bit_four : (4 : Bit) = 0 := by decide
@[simp] theorem bit_five : (5 : Bit) = 1 := by decide
@[simp] theorem bit_square (x : Bit) : x ^ 2 = x := ZMod.pow_card x
@[simp] theorem bit_self_add (x : Bit) : x + x = 0 := by revert x; decide
abbrev Letter := Bit × Bit
abbrev L := Letter
abbrev K := Letter

def oneL : L := (1, 0)
def spin : L := (0, 1)
def cospin : L := (1, 1)
def a : K := (1, 0)
def b : K := (0, 1)
def c : K := (1, 1)
def qL (u : L) : Bit := u.1 + u.1 * u.2
def qK (u : K) : Bit := u.1 + u.2 + u.1 * u.2
def euclideanWeight (u : L) : ℕ := if u.2 = 1 then 2 else if u.1 = 1 then 1 else 0

def polar : LinearMap.BilinForm Bit Letter :=
  LinearMap.mk₂ Bit (fun u v => u.1 * v.2 + u.2 * v.1)
    (by intros; dsimp; ring) (by intros; dsimp; ring)
    (by intros; dsimp; ring) (by intros; dsimp; ring)

@[simp] theorem polar_apply (u v : Letter) : polar u v = u.1 * v.2 + u.2 * v.1 := rfl

theorem qL_homogeneous : ∀ (r : Bit) (u : L), qL (r • u) = r ^ 2 * qL u := by decide
theorem qK_homogeneous : ∀ (r : Bit) (u : K), qK (r • u) = r ^ 2 * qK u := by decide

theorem qL_polar : ∀ u v : L, qL (u + v) + qL u + qL v = polar u v := by decide
theorem qK_polar : ∀ u v : K, qK (u + v) + qK u + qK v = polar u v := by decide
theorem euclideanWeight_mod_two : ∀ u : L, (euclideanWeight u : Bit) = qL u := by decide
theorem qK_eq_indicator : ∀ u : K, qK u = if u = 0 then 0 else 1 := by decide

theorem polar_symmetric (u v : Letter) : polar u v = polar v u := by simp [mul_comm, add_comm]

theorem polar_nondegenerate : polar.Nondegenerate := by
  constructor
  · intro u hu
    apply Prod.ext
    · simpa [b] using hu b
    · simpa [a] using hu a
  · intro u hu
    apply Prod.ext
    · simpa [b] using hu b
    · simpa [a] using hu a

variable {ι : Type*} [Fintype ι]
def wordQ (q : Letter → Bit) (w : ι → Letter) : Bit := ∑ i, q (w i)
def wordPolar : LinearMap.BilinForm Bit (ι → Letter) :=
  LinearMap.mk₂ Bit (fun u v => ∑ i, polar (u i) (v i))
    (by intros; simp [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm])
    (by intros; simp [Finset.mul_sum])
    (by intros; simp [Finset.sum_add_distrib, mul_add, add_assoc, add_left_comm, add_comm])
    (by intros; simp [Finset.mul_sum])

@[simp] theorem wordPolar_apply (u v : ι → Letter) : wordPolar u v = ∑ i, polar (u i) (v i) := rfl

theorem wordPolar_symmetric (u v : ι → Letter) : wordPolar u v = wordPolar v u := by
  simp only [wordPolar_apply, polar_symmetric]

theorem wordPolar_nondegenerate : (wordPolar (ι := ι)).Nondegenerate := by
  classical
  have hleft : ∀ u : ι → Letter, (∀ v, wordPolar u v = 0) → u = 0 := by
    intro u hu
    funext i
    apply polar_nondegenerate.1
    intro v
    have he : wordPolar u (Pi.single i v) = polar (u i) v := by
      rw [wordPolar_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · simp
    rw [← he]
    exact hu _
  exact ⟨hleft, fun u hu => hleft u (fun v => by rw [wordPolar_symmetric]; exact hu v)⟩

def dual (C : Submodule Bit (ι → Letter)) : Submodule Bit (ι → Letter) :=
  wordPolar.orthogonal C

theorem wordQ_polar (q : Letter → Bit)
    (hq : ∀ u v, q (u + v) + q u + q v = polar u v) (u v : ι → Letter) :
    wordQ q (u + v) + wordQ q u + wordQ q v = wordPolar u v := by
  simp only [wordQ, wordPolar_apply, ← Finset.sum_add_distrib, Pi.add_apply, hq]

theorem wordQ_K_weight (u : ι → K) : wordQ qK u = (hammingNorm u : Bit) := by
  classical
  simp [wordQ, hammingNorm, qK_eq_indicator, Finset.card_filter, Nat.cast_sum]

/-- Half-dimensional self-orthogonality supplies self-duality over the binary field. -/
theorem selfDual_of_half_dimension {V : Type*} [AddCommGroup V] [Module Bit V]
    [FiniteDimensional Bit V] (B : LinearMap.BilinForm Bit V) (hB : B.Nondegenerate)
    (C : Submodule Bit V) (hC : C ≤ B.orthogonal C)
    (hd : 2 * Module.finrank Bit C = Module.finrank Bit V) : C = B.orthogonal C := by
  apply Submodule.eq_of_le_of_finrank_le hC
  rw [B.finrank_orthogonal hB]
  omega

/-- Every additive isometry is allowed; no four-element field structure is imposed. -/
structure AlphabetIsometry (q : Letter → Bit) where
  toLinearEquiv : Letter ≃ₗ[Bit] Letter
  map_q : ∀ u, q (toLinearEquiv u) = q u

end Atlas.Codes
