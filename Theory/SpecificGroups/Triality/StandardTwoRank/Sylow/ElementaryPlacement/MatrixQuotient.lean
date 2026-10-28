module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Unipotent.MatrixEntries

/-!
# A three-dimensional section detecting the triality square obstruction

In the full Geck lattice, let W contain all positive root lines, the Cartan
lines other than α₀, and the line on −α₁. Adjoin the lines on the Cartan
coordinate α₀, −α₀, and −(α₀+α₁) to obtain V. Every positive root curve
preserves W and V. The three retained coordinates describe V/W, on which
only roots α₀, α₁, and α₀+α₁ act nontrivially, by upper unitriangular matrices.

The finite checks concern only the existing binary coefficient matrices;
their proved comparison with the canonical integral root curves supplies the
actual group action. Multiplication on this section shows that the square of
an ordered positive product has highest entry a₀*a₃. Thus an element whose
square is one has a₀*a₃ = 0, over every binary extension field.

Source: the Geck realization of the root relations in GLS3 §§2.3–2.6,
`refs/KGroup/GLS3/chapter2.tex`. This is the square obstruction used to place
elementary subgroups in the two radicals in the parent module.
-/

public section


open scoped BigOperators
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.RadicalCoordinates.Centers.UnipotentMatrices
namespace Triality.Standard.TwoRank.ElementaryPlacement
noncomputable section

/-- Levels zero and at most one mark W and V, respectively. -/
private def level : Index → Fin 3
  | .inl i => if i = 0 then 1 else 0
  | .inr r => ![0,0,1,2,0,0,1,2,0,0,2,2,0,0,0,2,0,0,2,2,0,0,2,2] r

private def sectionIndex : Fin 3 → Index := ![.inl 0, .inr 2, .inr 6]

private theorem sectionIndex_injective : Function.Injective sectionIndex := by
  decide +kernel

private theorem level_sectionIndex (i : Fin 3) : level (sectionIndex i) = 1 := by
  fin_cases i <;> rfl

private theorem level_eq_one (r : Index) :
    level r = 1 ↔ ∃ i, sectionIndex i = r := by
  revert r
  decide +kernel

set_option maxRecDepth 4000 in
private theorem coefficient_preserves (k : Fin 12) (i j : Index)
    (h : level j < level i) :
    linearCoefficient (positiveIndex k) i j = 0 ∧
    quadraticCoefficient (positiveIndex k) i j = 0 := by
  have cert : ∀ (k : Fin 12) (i j : Index),
      level j < level i →
      linearCoefficient (positiveIndex k) i j = (0 : ZMod 2) ∧
      quadraticCoefficient (positiveIndex k) i j = (0 : ZMod 2) := by
    unfold linearCoefficient quadraticCoefficient
    decide +kernel
  exact cert k i j h

variable {F : Type*} [CommRing F]

private def Preserves (A : Matrix Index Index F) : Prop :=
  ∀ i j, level j < level i → A i j = 0

private theorem preserves_one : Preserves (1 : Matrix Index Index F) := by
  intro i j h
  simp only [Matrix.one_apply, if_neg (show i ≠ j from fun he => by subst j; omega)]

private theorem Preserves.mul {A B : Matrix Index Index F}
    (hA : Preserves A) (hB : Preserves B) : Preserves (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _
  by_cases h : level r < level i
  · rw [hA i r h, zero_mul]
  · rw [hB r j (by omega), mul_zero]

private theorem preserves_curve [CharP F 2] (k : Fin 12) (t : F) :
    Preserves (matrixCurve (positiveIndex k) t) := by
  intro i j h
  obtain ⟨h1, h2⟩ := coefficient_preserves k i j h
  simp [matrixCurve, h1, h2, preserves_one i j h]

private def project (A : Matrix Index Index F) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => A (sectionIndex i) (sectionIndex j)

private theorem project_mul {A B : Matrix Index Index F}
    (hA : Preserves A) (hB : Preserves B) :
    project (A * B) = project A * project B := by
  ext i j
  change (∑ r : Index, A (sectionIndex i) r * B r (sectionIndex j)) =
    ∑ r : Fin 3, A (sectionIndex i) (sectionIndex r) * B (sectionIndex r) (sectionIndex j)
  symm
  apply Finset.sum_of_injOn sectionIndex
  · exact sectionIndex_injective.injOn
  · intro r _; simp
  · intro r _ hr
    have hne : level r ≠ 1 := by
      intro h
      obtain ⟨s, rfl⟩ := (level_eq_one r).mp h
      exact hr ⟨s, Finset.mem_univ _, rfl⟩
    by_cases h : level r < 1
    · rw [hA _ _ (by rw [level_sectionIndex]; exact h), zero_mul]
    · rw [hB _ _ (by rw [level_sectionIndex]; omega), mul_zero]
  · intro r _; rfl


private def triangle (a b c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, a, c; 0, 1, b; 0, 0, 1]

private theorem triangle_mul (a b c d e f : F) :
    triangle a b c * triangle d e f = triangle (a+d) (b+e) (c+f+a*e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangle, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem triangle_zero : triangle (0 : F) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [triangle]

private theorem project_one : project (1 : Matrix Index Index F) = 1 := by
  ext i j
  simp [project, Matrix.one_apply, sectionIndex_injective.eq_iff]

private theorem section_coefficients (k : Fin 12) (i j : Fin 3) :
    linearCoefficient (positiveIndex k) (sectionIndex i) (sectionIndex j) =
      (if (k = 0 ∧ i = 0 ∧ j = 1) ∨ (k = 3 ∧ i = 1 ∧ j = 2) ∨
          (k = 4 ∧ i = 0 ∧ j = 2) then 1 else 0) ∧
    quadraticCoefficient (positiveIndex k) (sectionIndex i) (sectionIndex j) = 0 := by
  revert k i j
  unfold linearCoefficient quadraticCoefficient
  decide +kernel

private theorem project_curve [CharP F 2] (k : Fin 12) (t : F) :
    project (matrixCurve (positiveIndex k) t) =
      triangle (if k = 0 then t else 0) (if k = 3 then t else 0)
        (if k = 4 then t else 0) := by
  ext i j
  have h := section_coefficients k i j
  simp only [project, matrixCurve, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    RingHom.mapMatrix_apply, Matrix.map_apply, h.1, h.2, map_zero, mul_zero, add_zero,
    Matrix.one_apply, sectionIndex_injective.eq_iff]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [triangle]

private theorem preserves_prod (l : List (Matrix Index Index F))
    (h : ∀ A ∈ l, Preserves A) : Preserves l.prod := by
  induction l with
  | nil => exact preserves_one
  | cons A l ih =>
    exact (h A (by simp)).mul (ih (fun B hB => h B (by simp [hB])))

private theorem project_prod (l : List (Matrix Index Index F))
    (h : ∀ A ∈ l, Preserves A) : project l.prod = (l.map project).prod := by
  induction l with
  | nil => exact project_one
  | cons A l ih =>
    have ht : ∀ B ∈ l, Preserves B := fun B hB => h B (by simp [hB])
    simp only [List.prod_cons, List.map_cons, project_mul (h A (by simp))
      (preserves_prod l ht), ih ht]

private theorem matrix_orderedProduct (P : Parameters) (hp : P.prime = 2)
    (v : Coordinates P) :
    let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
    matrixHom P (orderedProduct P v) =
      (List.ofFn (fun i => matrixCurve (positiveIndex i) (v i))).prod := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  simp only [orderedProduct, map_list_prod, List.map_ofFn, Function.comp_def,
    matrixHom_curve P hp]

private theorem preserves_orderedProduct (P : Parameters) (hp : P.prime = 2)
    (v : Coordinates P) : Preserves (matrixHom P (orderedProduct P v)) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  rw [matrix_orderedProduct P hp]
  apply preserves_prod
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact preserves_curve i (v i)

private theorem project_orderedProduct (P : Parameters) (hp : P.prime = 2)
    (v : Coordinates P) :
    project (matrixHom P (orderedProduct P v)) = triangle (v 0) (v 3) (v 4 + v 0 * v 3) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  rw [matrix_orderedProduct P hp, project_prod]
  · simp only [List.map_ofFn, Function.comp_def, project_curve]
    simp [List.ofFn_succ, triangle_mul, triangle_zero, add_comm]
  · intro A hA
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
    exact preserves_curve i (v i)

/-- Squaring in the genuine positive group detects the product of the two
simple folded parameters in the highest entry of this three-dimensional section. -/
theorem simple_coordinates_square (P : Parameters) (hp : P.prime = 2)
    (v : Coordinates P) (h : orderedProduct P v ^ 2 = 1) : v 0 * v 3 = 0 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  have he := congrArg (fun g => project (matrixHom P g)) h
  simp only [pow_two, map_mul, map_one,
    project_mul (preserves_orderedProduct P hp v) (preserves_orderedProduct P hp v),
    project_orderedProduct P hp, triangle_mul, project_one] at he
  have hc := congrFun₂ he 0 2
  change (v 4 + v 0 * v 3) + (v 4 + v 0 * v 3) + v 0 * v 3 = 0 at hc
  simpa only [CharTwo.add_self_eq_zero, zero_add] using hc

end
end Triality.Standard.TwoRank.ElementaryPlacement
