module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.Reduction
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# A small matrix calculation for natural SL₃(4) self-extensions

Write x = I + E₀₁, y = I + ω E₀₁, and p for the coordinate 3-cycle.
Six explicit equalities between words in x, y, p force nineteen linear
relations on the twenty-seven entries of their cross blocks. The displayed
`witness` matrix solves the coboundary equations on all three generators.
Short words recover every elementary transvection, so the identity holds
on the whole special linear group.

The word equalities are checked on the concrete 3 × 3 matrices by the
kernel. The scalar deductions are explicit linear combinations over F₄.
Only necessary relations are used; no abstract presentation or enumeration
of representations is assumed. Polynomial normalization precedes reduction
of coefficients and powers of ω to keep the checks small.

This supplies the intrinsic homogeneous extension calculation for James
(1973), Lemma 8.3, in the local catalogue associated with Aschbacher–Smith
H.12.1, printed pp.393–394. The binary-to-field passage and the actual
representation equivalence are supplied by the parent `Homogeneous` module.
-/

open Matrix
open Representation.SL3FourLocalCatalogue
open Representation
namespace Representation.SL3FourLocalCatalogue.HomogeneousCalculation
private abbrev Mat := Matrix (Fin 3) (Fin 3) F
private abbrev w : F := SL3FourNaturalDual.omega
-- The three concrete generators used throughout the calculation.
private def gen : Fin 3 → SL := ![
  ⟨!![1,1,0;0,1,0;0,0,1], by simp [Matrix.det_fin_three]⟩,
  ⟨!![1,w,0;0,1,0;0,0,1], by simp [Matrix.det_fin_three]⟩,
  ⟨!![0,0,1;1,0,0;0,1,0], by simp [Matrix.det_fin_three]⟩]
private def word (l : List (Fin 3)) : SL := (l.map gen).prod
private def matWord (l : List (Fin 3)) : Mat := (l.map (fun i => (gen i).val)).prod
private def cross (X : Fin 3 → Mat) : List (Fin 3) → Mat
| [] => 0
| i :: l => (gen i).val * cross X l + X i * matWord l
private lemma matWord_eq (l : List (Fin 3)) : matWord l = (word l).val := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [matWord, List.map_cons, List.prod_cons, word,
      Matrix.SpecialLinearGroup.coe_mul] at *
    rw [ih]
private lemma cross_eq (C : SL → Mat) (h1 : C 1 = 0)
    (hm : ∀ g h, C (g*h) = g.val * C h + C g * h.val) (l : List (Fin 3)) :
    cross (fun i => C (gen i)) l = C (word l) := by
  induction l with
  | nil => exact h1.symm
  | cons i l ih =>
    change (gen i).val * cross (fun i => C (gen i)) l + C (gen i) * matWord l = C (gen i * word l)
    rw [hm, ih, matWord_eq]
private lemma relation (C : SL → Mat) (h1 : C 1 = 0)
    (hm : ∀ g h, C (g*h) = g.val * C h + C g * h.val)
    (l r : List (Fin 3)) (h : word l = word r) :
    cross (fun i => C (gen i)) l = cross (fun i => C (gen i)) r := by
  rw [cross_eq C h1 hm, cross_eq C h1 hm, h]

private lemma wpow2 : w^2 = w + 1 := by decide +kernel
private lemma wpow3 : w^3 = 1 := by decide +kernel
private lemma wpow4 : w^4 = w := by decide +kernel
attribute [local simp] wpow2 wpow3 wpow4
local macro "four_ring" : tactic =>
  `(tactic| (ring_nf <;> simp [CharTwo.ofNat_eq_mod] <;>
    ring_nf <;> simp [CharTwo.ofNat_eq_mod]))

-- Coordinates of x² = 1.
private lemma constraint0 (X : Fin 3 → Mat)
    (h : cross X [0, 0] = cross X []) :
    X 0 1 0 = 0 := by
  have he := congrArg (fun M : Mat => M 0 0) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint1 (X : Fin 3 → Mat)
    (h : cross X [0, 0] = cross X []) :
    X 0 0 0 + X 0 1 1 = 0 := by
  have he := congrArg (fun M : Mat => M 0 1) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint2 (X : Fin 3 → Mat)
    (h : cross X [0, 0] = cross X []) :
    X 0 1 2 = 0 := by
  have he := congrArg (fun M : Mat => M 0 2) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint3 (X : Fin 3 → Mat)
    (h : cross X [0, 0] = cross X []) :
    X 0 2 0 = 0 := by
  have he := congrArg (fun M : Mat => M 2 1) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

-- Coordinates of yx = xy.
private lemma constraint4 (X : Fin 3 → Mat)
    (h : cross X [1, 0] = cross X [0, 1]) :
    w * X 0 1 0 + X 1 1 0 = 0 := by
  have he := congrArg (fun M : Mat => M 0 0) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint5 (X : Fin 3 → Mat)
    (h : cross X [1, 0] = cross X [0, 1]) :
    w * X 0 0 0 + w * X 0 1 1 + X 1 0 0 + X 1 1 1 = 0 := by
  have he := congrArg (fun M : Mat => M 0 1) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint6 (X : Fin 3 → Mat)
    (h : cross X [1, 0] = cross X [0, 1]) :
    w * X 0 1 2 + X 1 1 2 = 0 := by
  have he := congrArg (fun M : Mat => M 0 2) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint7 (X : Fin 3 → Mat)
    (h : cross X [1, 0] = cross X [0, 1]) :
    w * X 0 2 0 + X 1 2 0 = 0 := by
  have he := congrArg (fun M : Mat => M 2 1) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

-- Coordinates of p³ = 1.
private lemma constraint8 (X : Fin 3 → Mat)
    (h : cross X [2, 2, 2] = cross X []) :
    X 2 0 2 + X 2 1 0 + X 2 2 1 = 0 := by
  have he := congrArg (fun M : Mat => M 0 0) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint9 (X : Fin 3 → Mat)
    (h : cross X [2, 2, 2] = cross X []) :
    X 2 0 0 + X 2 1 1 + X 2 2 2 = 0 := by
  have he := congrArg (fun M : Mat => M 0 1) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint10 (X : Fin 3 → Mat)
    (h : cross X [2, 2, 2] = cross X []) :
    X 2 0 1 + X 2 1 2 + X 2 2 0 = 0 := by
  have he := congrArg (fun M : Mat => M 0 2) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

-- The first additional word relation.
private lemma constraint11 (X : Fin 3 → Mat)
    (h : cross X [1, 2, 0, 1, 2, 2, 0, 2] = cross X [0, 2, 1, 2, 2, 1, 2, 0]) :
    (w + 1) * X 0 0 0 + w * X 0 0 2 + w * X 0 1 0 + w * X 0 1 1 + X 0 2 1 + X 0 2 2 + w * X 1 0 0 +
      w * X 1 1 0 + X 1 1 1 + w * X 1 1 2 + w * X 1 2 1 + (w + 1) * X 1 2 2 + w * X 2 0 0 + (w + 1) * X 2 0 1 +
      w * X 2 1 1 + (w + 1) * X 2 1 2 + (w + 1) * X 2 2 0 = 0 := by
  have he := congrArg (fun M : Mat => M 0 0) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint12 (X : Fin 3 → Mat)
    (h : cross X [1, 2, 0, 1, 2, 2, 0, 2] = cross X [0, 2, 1, 2, 2, 1, 2, 0]) :
    X 0 0 0 + w * X 0 0 1 + w * X 0 1 1 + w * X 0 1 2 + w * X 0 2 0 + X 0 2 2 + X 1 0 0 + X 1 0 1 +
      w * X 1 0 2 + (w + 1) * X 1 1 1 + X 1 1 2 + X 1 2 0 + w * X 1 2 1 + X 2 0 0 + X 2 1 1 +
      w * X 2 2 2 = 0 := by
  have he := congrArg (fun M : Mat => M 0 1) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint13 (X : Fin 3 → Mat)
    (h : cross X [1, 2, 0, 1, 2, 2, 0, 2] = cross X [0, 2, 1, 2, 2, 1, 2, 0]) :
    X 0 0 2 + w * X 0 1 0 + w * X 0 1 2 + X 0 2 0 + (w + 1) * X 1 0 2 + X 1 1 0 + w * X 1 1 2 + w * X 1 2 0 +
      (w + 1) * X 2 0 0 + (w + 1) * X 2 0 1 + (w + 1) * X 2 1 1 + (w + 1) * X 2 1 2 + (w + 1) * X 2 2 0 + (w +
      1) * X 2 2 2 = 0 := by
  have he := congrArg (fun M : Mat => M 0 2) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint14 (X : Fin 3 → Mat)
    (h : cross X [1, 2, 0, 1, 2, 2, 0, 2] = cross X [0, 2, 1, 2, 2, 1, 2, 0]) :
    X 0 0 2 + (w + 1) * X 0 2 1 + (w + 1) * X 1 0 2 + X 1 1 2 + w * X 1 2 1 + w * X 2 0 1 + w * X 2 1 2 +
      w * X 2 2 0 = 0 := by
  have he := congrArg (fun M : Mat => M 1 0) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint15 (X : Fin 3 → Mat)
    (h : cross X [1, 2, 0, 1, 2, 2, 0, 2] = cross X [0, 2, 1, 2, 2, 1, 2, 0]) :
    w * X 0 0 0 + w * X 0 1 0 + X 0 1 1 + (w + 1) * X 0 2 2 + X 1 0 0 + w * X 1 0 2 + (w + 1) * X 1 1 1 +
      w * X 1 2 1 + w * X 1 2 2 + (w + 1) * X 2 0 0 + (w + 1) * X 2 1 1 = 0 := by
  have he := congrArg (fun M : Mat => M 1 1) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

-- The relation implied by (xp)⁷ = 1.
private lemma constraint16 (X : Fin 3 → Mat)
    (h : cross X [0, 2, 0, 2, 0, 2, 0, 2, 0] = cross X [2, 2, 0, 2, 2, 0, 2, 2]) :
    X 0 0 0 + X 0 0 2 + X 0 1 0 + X 0 1 1 + X 0 1 2 + X 0 2 0 + X 0 2 1 + X 0 2 2 + X 2 2 2 = 0 := by
  have he := congrArg (fun M : Mat => M 0 0) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

private lemma constraint17 (X : Fin 3 → Mat)
    (h : cross X [0, 2, 0, 2, 0, 2, 0, 2, 0] = cross X [2, 2, 0, 2, 2, 0, 2, 2]) :
    X 0 0 0 + X 0 0 1 + X 0 1 0 + X 0 1 1 + X 0 1 2 + X 0 2 0 + X 0 2 2 + X 2 0 2 + X 2 2 1 = 0 := by
  have he := congrArg (fun M : Mat => M 0 1) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

-- The remaining relation uses words of length twelve.
private lemma constraint18 (X : Fin 3 → Mat)
    (h : cross X [1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 2] = cross X [0, 2, 1, 2, 1, 2, 1, 2, 1, 2, 0, 1]) :
    (w + 1) * X 0 0 0 + X 0 0 1 + (w + 1) * X 0 1 1 + X 0 1 2 + X 0 2 0 + X 0 2 2 + w * X 1 0 0 + (w +
      1) * X 1 0 1 + w * X 1 0 2 + w * X 1 1 1 + w * X 1 2 1 + w * X 2 0 0 + w * X 2 0 1 + X 2 0 2 + X 2 1 0 +
      w * X 2 1 1 + w * X 2 1 2 + w * X 2 2 0 + X 2 2 1 + X 2 2 2 = 0 := by
  have he := congrArg (fun M : Mat => M 0 0) h
  simp [cross, matWord, gen, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at he
  linear_combination (norm := four_ring) he

-- Fix the scalar ambiguity by choosing the (0,0)-entry to be zero.
private def witness (X : Fin 3 → Mat) : Mat :=
  !![0, X 0 2 1 + X 2 0 0, X 0 0 0 + X 2 1 2;
    X 0 0 0, X 0 0 1, X 0 0 2;
    X 0 2 1, X 0 0 0 + X 2 0 1 + X 2 1 2, X 2 0 2]

private lemma generator0_coboundary (X : Fin 3 → Mat)
    (h0 : X 0 1 0 = 0)
    (h1 : X 0 0 0 + X 0 1 1 = 0)
    (h2 : X 0 1 2 = 0)
    (h3 : X 0 2 0 = 0)
    (h6 : w * X 0 1 2 + X 1 1 2 = 0)
    (h7 : w * X 0 2 0 + X 1 2 0 = 0)
    (h9 : X 2 0 0 + X 2 1 1 + X 2 2 2 = 0)
    (h10 : X 2 0 1 + X 2 1 2 + X 2 2 0 = 0)
    (h11 : (w + 1) * X 0 0 0 + w * X 0 0 2 + w * X 0 1 0 + w * X 0 1 1 + X 0 2 1 + X 0 2 2 + w * X 1 0 0 +
      w * X 1 1 0 + X 1 1 1 + w * X 1 1 2 + w * X 1 2 1 + (w + 1) * X 1 2 2 + w * X 2 0 0 + (w + 1) * X 2 0 1 +
      w * X 2 1 1 + (w + 1) * X 2 1 2 + (w + 1) * X 2 2 0 = 0)
    (h13 : X 0 0 2 + w * X 0 1 0 + w * X 0 1 2 + X 0 2 0 + (w + 1) * X 1 0 2 + X 1 1 0 + w * X 1 1 2 +
      w * X 1 2 0 + (w + 1) * X 2 0 0 + (w + 1) * X 2 0 1 + (w + 1) * X 2 1 1 + (w + 1) * X 2 1 2 + (w +
      1) * X 2 2 0 + (w + 1) * X 2 2 2 = 0)
    (h14 : X 0 0 2 + (w + 1) * X 0 2 1 + (w + 1) * X 1 0 2 + X 1 1 2 + w * X 1 2 1 + w * X 2 0 1 + w * X 2 1 2 +
      w * X 2 2 0 = 0)
    (h15 : w * X 0 0 0 + w * X 0 1 0 + X 0 1 1 + (w + 1) * X 0 2 2 + X 1 0 0 + w * X 1 0 2 + (w + 1) * X 1 1 1 +
      w * X 1 2 1 + w * X 1 2 2 + (w + 1) * X 2 0 0 + (w + 1) * X 2 1 1 = 0)
    (h16 : X 0 0 0 + X 0 0 2 + X 0 1 0 + X 0 1 1 + X 0 1 2 + X 0 2 0 + X 0 2 1 + X 0 2 2 + X 2 2 2 = 0)
    : X 0 + witness X * (gen 0).val = (gen 0).val * witness X := by
  funext i j
  fin_cases i <;> fin_cases j
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    four_ring
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    four_ring
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) h0
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) h1
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) h2
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) h3
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    four_ring
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) w * h0 + h1 + h2 + (w + 1) * h6 + h7 + (w + 1) * h9 + h10 + w * h11 +
      (w + 1) * h13 + h14 + (w + 1) * h15 + h16

private lemma generator1_coboundary (X : Fin 3 → Mat)
    (h0 : X 0 1 0 = 0)
    (h1 : X 0 0 0 + X 0 1 1 = 0)
    (h2 : X 0 1 2 = 0)
    (h3 : X 0 2 0 = 0)
    (h4 : w * X 0 1 0 + X 1 1 0 = 0)
    (h5 : w * X 0 0 0 + w * X 0 1 1 + X 1 0 0 + X 1 1 1 = 0)
    (h6 : w * X 0 1 2 + X 1 1 2 = 0)
    (h7 : w * X 0 2 0 + X 1 2 0 = 0)
    (h8 : X 2 0 2 + X 2 1 0 + X 2 2 1 = 0)
    (h9 : X 2 0 0 + X 2 1 1 + X 2 2 2 = 0)
    (h10 : X 2 0 1 + X 2 1 2 + X 2 2 0 = 0)
    (h11 : (w + 1) * X 0 0 0 + w * X 0 0 2 + w * X 0 1 0 + w * X 0 1 1 + X 0 2 1 + X 0 2 2 + w * X 1 0 0 +
      w * X 1 1 0 + X 1 1 1 + w * X 1 1 2 + w * X 1 2 1 + (w + 1) * X 1 2 2 + w * X 2 0 0 + (w + 1) * X 2 0 1 +
      w * X 2 1 1 + (w + 1) * X 2 1 2 + (w + 1) * X 2 2 0 = 0)
    (h12 : X 0 0 0 + w * X 0 0 1 + w * X 0 1 1 + w * X 0 1 2 + w * X 0 2 0 + X 0 2 2 + X 1 0 0 + X 1 0 1 +
      w * X 1 0 2 + (w + 1) * X 1 1 1 + X 1 1 2 + X 1 2 0 + w * X 1 2 1 + X 2 0 0 + X 2 1 1 + w * X 2 2 2 = 0)
    (h13 : X 0 0 2 + w * X 0 1 0 + w * X 0 1 2 + X 0 2 0 + (w + 1) * X 1 0 2 + X 1 1 0 + w * X 1 1 2 +
      w * X 1 2 0 + (w + 1) * X 2 0 0 + (w + 1) * X 2 0 1 + (w + 1) * X 2 1 1 + (w + 1) * X 2 1 2 + (w +
      1) * X 2 2 0 + (w + 1) * X 2 2 2 = 0)
    (h14 : X 0 0 2 + (w + 1) * X 0 2 1 + (w + 1) * X 1 0 2 + X 1 1 2 + w * X 1 2 1 + w * X 2 0 1 + w * X 2 1 2 +
      w * X 2 2 0 = 0)
    (h15 : w * X 0 0 0 + w * X 0 1 0 + X 0 1 1 + (w + 1) * X 0 2 2 + X 1 0 0 + w * X 1 0 2 + (w + 1) * X 1 1 1 +
      w * X 1 2 1 + w * X 1 2 2 + (w + 1) * X 2 0 0 + (w + 1) * X 2 1 1 = 0)
    (h16 : X 0 0 0 + X 0 0 2 + X 0 1 0 + X 0 1 1 + X 0 1 2 + X 0 2 0 + X 0 2 1 + X 0 2 2 + X 2 2 2 = 0)
    (h18 : (w + 1) * X 0 0 0 + X 0 0 1 + (w + 1) * X 0 1 1 + X 0 1 2 + X 0 2 0 + X 0 2 2 + w * X 1 0 0 + (w +
      1) * X 1 0 1 + w * X 1 0 2 + w * X 1 1 1 + w * X 1 2 1 + w * X 2 0 0 + w * X 2 0 1 + X 2 0 2 + X 2 1 0 +
      w * X 2 1 1 + w * X 2 1 2 + w * X 2 2 0 + X 2 2 1 + X 2 2 2 = 0)
    : X 1 + witness X * (gen 1).val = (gen 1).val * witness X := by
  funext i j
  fin_cases i <;> fin_cases j
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) (w + 1) * h2 + h3 + (w + 1) * h4 + w * h6 + h7 + h8 + h9 + h11 + (w +
      1) * h12 + h13 + h14 + w * h15 + w * h16 + h18
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) w * h1 + w * h3 + (w + 1) * h4 + (w + 1) * h5 + h6 + w * h7 +
      w * h8 + (w + 1) * h9 + h10 + h11 + h13 + h14 + w * h15 + w * h16 + w * h18
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) w * h2 + (w + 1) * h3 + w * h4 + (w + 1) * h6 + (w + 1) * h7 + h9 +
      h10 + w * h13
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) w * h0 + h4
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) w * h1 + (w + 1) * h2 + h3 + (w + 1) * h4 + h5 + w * h6 + h7 + h8 +
      h9 + h11 + (w + 1) * h12 + h13 + h14 + w * h15 + w * h16 + h18
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) w * h2 + h6
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) w * h3 + h7
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) w * h2 + h3 + (w + 1) * h4 + w * h6 + h7 + w * h9 + (w + 1) * h10 +
      (w + 1) * h13 + (w + 1) * h14
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) (w + 1) * h0 + w * h1 + h2 + h3 + w * h4 + w * h5 + (w + 1) * h6 +
      (w + 1) * h7 + h8 + w * h10 + h11 + (w + 1) * h12 + w * h14 + h15 + h18

private lemma generator2_coboundary (X : Fin 3 → Mat)
    (h0 : X 0 1 0 = 0)
    (h3 : X 0 2 0 = 0)
    (h6 : w * X 0 1 2 + X 1 1 2 = 0)
    (h7 : w * X 0 2 0 + X 1 2 0 = 0)
    (h8 : X 2 0 2 + X 2 1 0 + X 2 2 1 = 0)
    (h9 : X 2 0 0 + X 2 1 1 + X 2 2 2 = 0)
    (h10 : X 2 0 1 + X 2 1 2 + X 2 2 0 = 0)
    (h11 : (w + 1) * X 0 0 0 + w * X 0 0 2 + w * X 0 1 0 + w * X 0 1 1 + X 0 2 1 + X 0 2 2 + w * X 1 0 0 +
      w * X 1 1 0 + X 1 1 1 + w * X 1 1 2 + w * X 1 2 1 + (w + 1) * X 1 2 2 + w * X 2 0 0 + (w + 1) * X 2 0 1 +
      w * X 2 1 1 + (w + 1) * X 2 1 2 + (w + 1) * X 2 2 0 = 0)
    (h13 : X 0 0 2 + w * X 0 1 0 + w * X 0 1 2 + X 0 2 0 + (w + 1) * X 1 0 2 + X 1 1 0 + w * X 1 1 2 +
      w * X 1 2 0 + (w + 1) * X 2 0 0 + (w + 1) * X 2 0 1 + (w + 1) * X 2 1 1 + (w + 1) * X 2 1 2 + (w +
      1) * X 2 2 0 + (w + 1) * X 2 2 2 = 0)
    (h14 : X 0 0 2 + (w + 1) * X 0 2 1 + (w + 1) * X 1 0 2 + X 1 1 2 + w * X 1 2 1 + w * X 2 0 1 + w * X 2 1 2 +
      w * X 2 2 0 = 0)
    (h15 : w * X 0 0 0 + w * X 0 1 0 + X 0 1 1 + (w + 1) * X 0 2 2 + X 1 0 0 + w * X 1 0 2 + (w + 1) * X 1 1 1 +
      w * X 1 2 1 + w * X 1 2 2 + (w + 1) * X 2 0 0 + (w + 1) * X 2 1 1 = 0)
    (h16 : X 0 0 0 + X 0 0 2 + X 0 1 0 + X 0 1 1 + X 0 1 2 + X 0 2 0 + X 0 2 1 + X 0 2 2 + X 2 2 2 = 0)
    (h17 : X 0 0 0 + X 0 0 1 + X 0 1 0 + X 0 1 1 + X 0 1 2 + X 0 2 0 + X 0 2 2 + X 2 0 2 + X 2 2 1 = 0)
    : X 2 + witness X * (gen 2).val = (gen 2).val * witness X := by
  funext i j
  fin_cases i <;> fin_cases j
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    four_ring
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    four_ring
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) (w + 1) * h0 + h3 + (w + 1) * h6 + h7 + h8 + (w + 1) * h9 + h10 +
      w * h11 + (w + 1) * h13 + h14 + (w + 1) * h15 + h16 + h17
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) (w + 1) * h0 + h3 + (w + 1) * h6 + h7 + w * h9 + h10 + w * h11 + (w +
      1) * h13 + h14 + (w + 1) * h15
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    four_ring
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) h10
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) (w + 1) * h0 + h3 + (w + 1) * h6 + h7 + (w + 1) * h9 + h10 +
      w * h11 + (w + 1) * h13 + h14 + (w + 1) * h15 + h16 + h17
  · simp [witness, gen, Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (norm := four_ring) (w + 1) * h0 + h3 + (w + 1) * h6 + h7 + (w + 1) * h9 + h10 +
      w * h11 + (w + 1) * h13 + h14 + (w + 1) * h15

private lemma generator_coboundary (C : SL → Mat) (h1 : C 1 = 0)
    (hm : ∀ g h, C (g*h) = g.val * C h + C g * h.val) :
    ∃ M : Mat, ∀ i : Fin 3, C (gen i) + M * (gen i).val = (gen i).val * M := by
  let X : Fin 3 → Mat := fun i => C (gen i)
  have r0 : cross X [0, 0] = cross X [] :=
    relation C h1 hm _ _ (by decide +kernel)
  have r1 : cross X [1, 0] = cross X [0, 1] :=
    relation C h1 hm _ _ (by decide +kernel)
  have r2 : cross X [2, 2, 2] = cross X [] :=
    relation C h1 hm _ _ (by decide +kernel)
  have r3 : cross X [1, 2, 0, 1, 2, 2, 0, 2] = cross X [0, 2, 1, 2, 2, 1, 2, 0] :=
    relation C h1 hm _ _ (by decide +kernel)
  have r4 : cross X [0, 2, 0, 2, 0, 2, 0, 2, 0] = cross X [2, 2, 0, 2, 2, 0, 2, 2] :=
    relation C h1 hm _ _ (by decide +kernel)
  have r5 : cross X [1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 2] = cross X [0, 2, 1, 2, 1, 2, 1, 2, 1, 2, 0, 1] :=
    relation C h1 hm _ _ (by decide +kernel)
  have h0 := constraint0 X r0
  have h1 := constraint1 X r0
  have h2 := constraint2 X r0
  have h3 := constraint3 X r0
  have h4 := constraint4 X r1
  have h5 := constraint5 X r1
  have h6 := constraint6 X r1
  have h7 := constraint7 X r1
  have h8 := constraint8 X r2
  have h9 := constraint9 X r2
  have h10 := constraint10 X r2
  have h11 := constraint11 X r3
  have h12 := constraint12 X r3
  have h13 := constraint13 X r3
  have h14 := constraint14 X r3
  have h15 := constraint15 X r3
  have h16 := constraint16 X r4
  have h17 := constraint17 X r4
  have h18 := constraint18 X r5
  refine ⟨witness X, ?_⟩
  intro i
  fin_cases i
  · exact generator0_coboundary X h0 h1 h2 h3 h6 h7 h9 h10 h11 h13 h14 h15 h16
  · exact generator1_coboundary X h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h18
  · exact generator2_coboundary X h0 h3 h6 h7 h8 h9 h10 h11 h13 h14 h15 h16 h17

-- Explicit words for xᵢⱼ(1) and xᵢⱼ(ω); addition supplies xᵢⱼ(1+ω).
private def rootWord (b : Bool) (i j : Fin 3) : List (Fin 3) :=
  (if b then
    ![![[], [1], [0, 2, 1, 2, 2, 0, 2, 1, 2, 2]],
      ![[2, 0, 2, 1, 2, 2, 0, 2, 1, 2], [], [2, 1, 2, 2]],
      ![[2, 2, 1, 2], [0, 2, 2, 1, 2, 0, 2, 2, 1, 2], []]]
  else
    ![![[], [0], [0, 2, 0, 2, 2, 0, 2, 0, 2, 2]],
      ![[2, 0, 2, 0, 2, 2, 0, 2, 0, 2], [], [2, 0, 2, 2]],
      ![[2, 2, 0, 2], [0, 2, 2, 0, 2, 0, 2, 2, 0, 2], []]]) i j

private lemma rootWord_correct (i j : Fin 3) (hij : i ≠ j) (b : Bool) :
    word (rootWord b i j) = Matrix.SpecialLinearGroup.transvection hij (if b then w else 1) := by
  revert i j hij b
  decide +kernel

private lemma generation (P : SL → Prop) (h1 : P 1)
    (hm : ∀ g h, P g → P h → P (g*h)) (hg : ∀ i, P (gen i)) (g : SL) : P g := by
  have hw (l : List (Fin 3)) : P (word l) := by
    induction l with
    | nil => exact h1
    | cons i l ih => exact hm (gen i) (word l) (hg i) ih
  apply OneCohomology.SLHigherNatural.transvection_induction P ?_ hm g
  intro i j hij t
  have ht : t = 0 ∨ t = 1 ∨ t = w ∨ t = 1 + w := by revert t; decide +kernel
  rcases ht with rfl | rfl | rfl | rfl
  · convert h1 using 1
    apply Subtype.ext
    simp
  · simpa only [rootWord_correct i j hij, Bool.false_eq_true, ↓reduceIte] using hw (rootWord false i j)
  · simpa only [rootWord_correct i j hij, ↓reduceIte] using hw (rootWord true i j)
  · rw [Matrix.SpecialLinearGroup.transvection_add]
    apply hm
    · simpa only [rootWord_correct i j hij, Bool.false_eq_true, ↓reduceIte] using hw (rootWord false i j)
    · simpa only [rootWord_correct i j hij, ↓reduceIte] using hw (rootWord true i j)

/-- Every matrix cross block for the natural F₄ action is a coboundary. -/
public lemma matrix_coboundary (C : SL → Matrix (Fin 3) (Fin 3) F) (h1 : C 1 = 0)
    (hm : ∀ g h, C (g*h) = g.val * C h + C g * h.val) :
    ∃ M : Matrix (Fin 3) (Fin 3) F, ∀ g : SL, C g + M * g.val = g.val * M := by
  obtain ⟨M, hM⟩ := generator_coboundary C h1 hm
  refine ⟨M, fun g => eq_sub_iff_add_eq.mp ?_⟩
  apply generation (fun g => C g = g.val * M - M * g.val) ?_ ?_ ?_ g
  · simp [h1]
  · intro g h hg hh
    rw [hm, Matrix.SpecialLinearGroup.coe_mul, hg, hh]
    noncomm_ring
  · intro i
    exact eq_sub_iff_add_eq.mpr (hM i)
end Representation.SL3FourLocalCatalogue.HomogeneousCalculation
