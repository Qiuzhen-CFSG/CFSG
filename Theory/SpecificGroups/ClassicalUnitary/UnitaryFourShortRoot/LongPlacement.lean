module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.Stabilizer
public import Mathlib.Data.Matrix.Basis

/-!
# Long-root conjugates in the original plane endpoint

The nilpotent part of a conjugate of the long-root matrix is the outer
product of the conjugating matrix's first column and its Hermitian adjoint.
If that conjugate preserves the marked plane, two entries force the lower
coordinates of this column to vanish. Its plane restriction is therefore
the identity, putting the element in the actual Hermitian radical.

This supplies the marked pair-placement step for the binary ordinary
completion in Aschbacher–Smith F.4.42, printed p.295.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "SU₄" => SU F (form F σ hσ)

omit [CharP F 2] in
private theorem inverse_matrix (g : SU₄) :
    (g⁻¹).val.val = gram F * (form F σ hσ).conjTranspose g.val.val * gram F := by
  have hu := g.property.1
  change (form F σ hσ).conjTranspose g.val.val * gram F * g.val.val = gram F at hu
  have hl : (gram F * (form F σ hσ).conjTranspose g.val.val * gram F) * g.val.val = 1 := by
    calc
      _ = gram F * ((form F σ hσ).conjTranspose g.val.val * gram F * g.val.val) := by simp only [mul_assoc]
      _ = 1 := by rw [hu,gram_sq]
  calc
    _ = ((gram F * (form F σ hσ).conjTranspose g.val.val * gram F) * g.val.val) * (g⁻¹).val.val := by rw [hl,one_mul]
    _ = _ := by rw [mul_assoc,show g.val.val * (g⁻¹).val.val = 1 from g.val.val_inv,mul_one]

/-- The conjugate long-root nilpotent is the Hermitian rank-one outer product
of the conjugating matrix's first column with its adjoint. -/
theorem long_conjugate_entry (g : SU₄) (i j : Fin 4) :
    (g * unipotentSU F σ hσ (longParameter F σ) * g⁻¹).val.val i j =
      (1 : Matrix (Fin 4) (Fin 4) F) i j + g.val.val i 0 * σ (g.val.val j.rev 0) := by
  have hz : unipotentMatrix F (longParameter F σ).val =
      1 + Matrix.single (0 : Fin 4) 3 (1 : F) := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [unipotentMatrix,longParameter,Matrix.single]
  change (g.val.val * unipotentMatrix F (longParameter F σ).val * (g⁻¹).val.val) i j = _
  rw [hz,mul_add,add_mul,mul_one,show g.val.val * (g⁻¹).val.val = 1 from g.val.val_inv]
  simp only [Matrix.add_apply]
  congr 1
  rw [inverse_matrix]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single,form,gram,HermitianForm.conjTranspose,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

variable [Finite F]
/-- A long-root conjugate in the marked plane local belongs to its actual
Hermitian radical. No abstract involution-class catalogue is assumed. -/
theorem long_conjugate_in_plane_mem_radical
    (a : localFactor F (form F σ hσ))
    (h : IsConj (unipotentSU F σ hσ (longParameter F σ)) a.val) :
    a ∈ radical F σ hσ := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  have hp := (mem_planeParabolicSU F (form F σ hσ) a.val).mp
    (local_le_planeParabolic F (form F σ hσ) a.property)
  have hc (i j : Fin 4) : a.val.val.val i j =
      (1 : Matrix (Fin 4) (Fin 4) F) i j + g.val.val i 0 * σ (g.val.val j.rev 0) := by
    rw [← hg]
    exact long_conjugate_entry F σ hσ g i j
  have h20 : g.val.val 2 0 = 0 := by
    have he := hc 2 1
    simp only [hp.2.2.1, Matrix.one_apply, Fin.reduceEq, if_false,zero_add] at he
    exact (mul_eq_zero.mp he.symm).elim id (fun h => σ.injective (h.trans (map_zero σ).symm))
  have h30 : g.val.val 3 0 = 0 := by
    have he := hc 3 0
    simp only [hp.2.1, Matrix.one_apply, Fin.reduceEq, if_false,zero_add] at he
    exact (mul_eq_zero.mp he.symm).elim id (fun h => σ.injective (h.trans (map_zero σ).symm))
  rw [mem_radical]
  constructor
  · simpa [h30] using hc 0 0
  constructor
  · simpa [h20] using hc 0 1
  constructor
  · simpa [h30] using hc 1 0
  · simpa [h20] using hc 1 1
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
