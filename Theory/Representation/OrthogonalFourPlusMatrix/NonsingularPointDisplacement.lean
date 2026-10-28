module
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPoint

/-!
A nonsingular matrix is a single displacement under its own determinant
stabilizer in characteristic two. In identity coordinates the upper
transvection sends the matrix [[0,0],[1,1]] to itself plus the identity.
Transport through the given nonsingular matrix preserves the actual
left-right stabilizer convention.

Source application: Aschbacher--Smith 9.1.2(4) and 9.4.1, printed pp.729,735.
-/

public section
open Matrix Subgroup
namespace ClassicalOrthogonal.FourPlusMatrix
variable {F : Type*} [Field F] [CharP F 2]

/-- A nonsingular vector is one displacement for its own stabilizer. -/
theorem nonsingular_point_displacement (v : Mat (F := F)) (hv : v.det ≠ 0) :
    ∃ (g : pointStabilizer v) (w : Mat (F := F)), matrixAction g.val w - w = v := by
  let a : SpecialLinearGroup (Fin 2) F := ⟨!![1,1;0,1],by simp [det_fin_two]⟩
  let b : Mat (F := F) := !![0,0;1,1]
  have haa : a.val * a.val = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
  have hab : a.val * b * a.val - b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a,b,CharTwo.add_self_eq_zero,CharTwo.neg_eq]
  obtain ⟨g,hg⟩ := (pointProjection_bijective v hv).2 a
  change g.val.1 = a at hg
  have hfix : a.val * v * g.val.2⁻¹.val = v := by
    have h := (mem_pointStabilizer g.val v).mp g.property
    change g.val.1.val * v * g.val.2⁻¹.val = v at h
    rwa [hg] at h
  have hvb : v * g.val.2⁻¹.val = a.val * v := by
    calc
      _ = (a.val * a.val) * (v * g.val.2⁻¹.val) := by rw [haa,one_mul]
      _ = a.val * (a.val * v * g.val.2⁻¹.val) := by simp only [mul_assoc]
      _ = a.val * v := by rw [hfix]
  refine ⟨g,b * v,?_⟩
  change g.val.1.val * (b * v) * g.val.2⁻¹.val - b * v = v
  rw [hg]
  calc
    _ = (a.val * b * a.val - b) * v := by
      rw [mul_assoc,mul_assoc,hvb]
      simp only [sub_mul,mul_assoc]
    _ = v := by rw [hab,one_mul]

end ClassicalOrthogonal.FourPlusMatrix
