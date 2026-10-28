module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.LeviDetection.FirstLayer

/-!
# The first two matrix layers of the linear Ree radical

In characteristic two, the degree-two part of a radical matrix squared is
exactly the square of its degree-one part. Inner conjugation by a radical
element leaves that first part unchanged. Consequently a radical factor in a
torus actor cannot erase a square detected in degree two.

These are calculations on the faithful F₄ matrices with the existing
middle-root grading. They support the linear local exclusion used in
Aschbacher–Smith 2.3.9(7), printed p.526, and E.6.8, printed pp.247–248,
`refs/quasithin.pdf`; the root radical is that of F.1.12(I)(5), p.263.
-/

@[expose] public section
open Theory.AlgebraicGroup
open ReeF4.SectionGeometry.LinearRadical.LeviDetection
namespace ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection
noncomputable section
variable {m : ℕ}

def degreeTwoPart : MatrixCarrier m →ₗ[CoefficientField m] MatrixCarrier m where
  toFun A i j := if basisDegree i = basisDegree j + 2 then A i j else 0
  map_add' A B := by
    ext i j
    change (if basisDegree i = basisDegree j + 2 then A i j + B i j else 0) =
      (if basisDegree i = basisDegree j + 2 then A i j else 0) +
      (if basisDegree i = basisDegree j + 2 then B i j else 0)
    split_ifs <;> simp
  map_smul' t A := by
    ext i j
    change (if basisDegree i = basisDegree j + 2 then t * A i j else 0) =
      t * (if basisDegree i = basisDegree j + 2 then A i j else 0)
    split_ifs <;> simp

@[simp] theorem degreeTwoPart_apply (A : MatrixCarrier m) (i j : F4Chevalley.BasisIndex) :
    degreeTwoPart A i j = if basisDegree i = basisDegree j + 2 then A i j else 0 := rfl

@[simp] theorem degreeTwoPart_one : degreeTwoPart (1 : MatrixCarrier m) = 0 := by
  ext i j
  by_cases h : basisDegree i = basisDegree j + 2
  · have hij : i ≠ j := by intro he; subst j; omega
    simp [h, hij]
  · simp [h]

theorem degreeTwoPart_mul_raises {A B : MatrixCarrier m}
    (hA : Raises A) (hB : Raises B) :
    degreeTwoPart (A * B) = degreeOnePart A * degreeOnePart B := by
  ext i j
  simp only [degreeTwoPart_apply, Matrix.mul_apply, degreeOnePart_apply]
  by_cases hij : basisDegree i = basisDegree j + 2
  · rw [if_pos hij]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : basisDegree i = basisDegree k + 1
    · rw [if_pos hik, if_pos (by omega)]
    · rw [if_neg hik, zero_mul]
      by_cases hik' : basisDegree i ≤ basisDegree k
      · rw [hA i k hik', zero_mul]
      · rw [hB k j (by omega), mul_zero]
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : basisDegree i = basisDegree k + 1
    · rw [if_neg (by omega : basisDegree k ≠ basisDegree j + 1), mul_zero]
    · rw [if_neg hik, zero_mul]

theorem degreeTwoPart_square {A : MatrixCarrier m} (hA : Raises (A - 1)) :
    degreeTwoPart (A * A) = degreeOnePart A * degreeOnePart A := by
  have hAA : A + A = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero (A i j)
  have he : (A - 1) * (A - 1) = A * A + 1 := by
    calc
      _ = A * A - (A + A) + 1 := by noncomm_ring
      _ = _ := by rw [hAA, sub_zero]
  have h := degreeTwoPart_mul_raises hA hA
  simpa only [he, map_add, degreeTwoPart_one, add_zero, map_sub,
    degreeOnePart_one, sub_zero] using h


theorem degreeTwoPart_mul_of_raises {A B : MatrixCarrier m}
    (hA : Raises (A - 1)) (hB : Raises (B - 1)) :
    degreeTwoPart (A * B) = degreeTwoPart A + degreeTwoPart B +
      degreeOnePart A * degreeOnePart B := by
  have he : A * B = A + B - 1 + (A - 1) * (B - 1) := by noncomm_ring
  rw [he, map_add, map_sub, map_add, degreeTwoPart_one, sub_zero,
    degreeTwoPart_mul_raises hA hB, map_sub, map_sub,
    degreeOnePart_one, sub_zero, sub_zero]

theorem degreeTwoPart_square_eq_of_degreeOnePart_eq {x y : Model m}
    (hx : x ∈ Parabolics.radical m .linear) (hy : y ∈ Parabolics.radical m .linear)
    (he : degreeOnePart (modelMatrix m x) = degreeOnePart (modelMatrix m y)) :
    degreeTwoPart (modelMatrix m (x ^ 2)) = degreeTwoPart (modelMatrix m (y ^ 2)) := by
  simp only [pow_two, modelMatrix_mul, degreeTwoPart_square (radical_raises x hx),
    degreeTwoPart_square (radical_raises y hy), he]

open Subgroup
open scoped commutatorElement

theorem degreeOnePart_inv (x : Model m) (hx : x ∈ Parabolics.radical m .linear) :
    degreeOnePart (modelMatrix m x⁻¹) = -degreeOnePart (modelMatrix m x) := by
  have h := degreeOnePart_model_mul x x⁻¹ hx ((Parabolics.radical m .linear).inv_mem hx)
  rw [mul_inv_cancel, modelMatrix_one, degreeOnePart_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem degreeOnePart_conj (r x : Model m)
    (hr : r ∈ Parabolics.radical m .linear) (hx : x ∈ Parabolics.radical m .linear) :
    degreeOnePart (modelMatrix m (r * x * r⁻¹)) = degreeOnePart (modelMatrix m x) := by
  rw [degreeOnePart_model_mul _ _ ((Parabolics.radical m .linear).mul_mem hr hx)
    ((Parabolics.radical m .linear).inv_mem hr), degreeOnePart_model_mul _ _ hr hx,
    degreeOnePart_inv _ hr]
  abel

/-- Inner radical factors cannot change the first layer of the commutator. -/
theorem degreeOnePart_commutator_radical_mul (q r l : Model m)
    (hq : q ∈ Parabolics.radical m .linear) (hr : r ∈ Parabolics.radical m .linear)
    (hlq : l * q⁻¹ * l⁻¹ ∈ Parabolics.radical m .linear) :
    degreeOnePart (modelMatrix m ⁅q, r * l⁆) = degreeOnePart (modelMatrix m ⁅q, l⁆) := by
  have he : ⁅q, r * l⁆ = q * (r * (l * q⁻¹ * l⁻¹) * r⁻¹) := by
    simp only [commutatorElement_def, mul_inv_rev]
    group
  have he' : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def, mul_assoc]
  have hc : r * (l * q⁻¹ * l⁻¹) * r⁻¹ ∈ Parabolics.radical m .linear :=
    (Parabolics.radical m .linear).mul_mem
      ((Parabolics.radical m .linear).mul_mem hr hlq)
      ((Parabolics.radical m .linear).inv_mem hr)
  rw [he, he', degreeOnePart_model_mul _ _ hq hc,
    degreeOnePart_model_mul _ _ hq hlq, degreeOnePart_conj _ _ hr hlq]

end
end ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection
