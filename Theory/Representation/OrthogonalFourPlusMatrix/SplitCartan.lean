module
public import Theory.Representation.OrthogonalFourPlusMatrix.NaturalTensor
public import Theory.SpecificGroups.SL2.OddBorelMarking

/-!
# Compatible split-Cartan and determinant coordinates

The upper root groups fix precisely the upper matrix-unit line. A pair of
diagonal matrices fixes a nonzero vector on that line exactly when its
unit coordinates are inverse. Simultaneous inner changes of the two group
markings are intertwined by the same determinant action on matrices.

The original Chapter 10 central Hall argument uses these identities to
identify its prescribed Hall subgroup inside the same split Cartan.
Source: Aschbacher--Smith 9.1.2(5), 9.2.7, pp.729,731--732,
refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace ClassicalOrthogonal.FourPlusMatrix.SplitCartan
variable {F : Type*} [Field F]

def upperPoint (a : F) : Mat (F := F) := !![0,a;0,0]

theorem upper_fixed (v : Mat (F := F))
    (hfix : ∀ g ∈ (SpecialLinearGroup.upperUnipotent F).prod
      (SpecialLinearGroup.upperUnipotent F), matrixAction g v = v) :
    v = upperPoint (v 0 1) := by
  let u : SL(2,F) := SpecialLinearGroup.transvection zero_ne_one (1:F)
  have hu : u ∈ SpecialLinearGroup.upperUnipotent F :=
    (SpecialLinearGroup.mem_upperUnipotent F _).mpr ⟨1,rfl⟩
  have hl := hfix (u,1) ⟨hu,one_mem _⟩
  have hr := hfix (1,u⁻¹) ⟨one_mem _,(SpecialLinearGroup.upperUnipotent F).inv_mem hu⟩
  have h10 : v 1 0 = 0 := by
    have hh := congrArg (fun M : Mat (F := F) => M 0 0) hl
    simp [matrixAction,u,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two] at hh
    exact hh
  have h11 : v 1 1 = 0 := by
    have hh := congrArg (fun M : Mat (F := F) => M 0 1) hl
    simpa [matrixAction,u,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two] using hh
  have h00 : v 0 0 = 0 := by
    have hh := congrArg (fun M : Mat (F := F) => M 0 1) hr
    simpa [matrixAction,u,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two] using hh
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperPoint,h10,h11,h00]

theorem upperPoint_ne_zero {a : F} (ha : a ≠ 0) : upperPoint a ≠ 0 := by
  intro h
  exact ha (congrArg (fun M : Mat (F := F) => M 0 1) h)

theorem diagonal_upperPoint (x y : Fˣ) (a : F) :
    matrixAction (SpecialLinearGroup.diag2 (x:F) x.ne_zero,
      SpecialLinearGroup.diag2 (y:F) y.ne_zero) (upperPoint a) =
        upperPoint ((x:F)*(y:F)*a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixAction,upperPoint,SpecialLinearGroup.diag2_coe',
      Matrix.adjugate_fin_two]
  ring

theorem diagonal_fixed_iff (x y : Fˣ) {a : F} (ha : a ≠ 0) :
    matrixAction (SpecialLinearGroup.diag2 (x:F) x.ne_zero,
      SpecialLinearGroup.diag2 (y:F) y.ne_zero) (upperPoint a) = upperPoint a ↔
      y = x⁻¹ := by
  rw [diagonal_upperPoint]
  constructor
  · intro h
    have he : (x:F)*(y:F)=1 := mul_right_cancel₀ ha
      ((congrArg (fun M : Mat (F := F) => M 0 1) h).trans (one_mul a).symm)
    apply Units.ext
    simpa only [Units.val_inv_eq_inv_val] using eq_inv_of_mul_eq_one_right he
  · intro h
    rw [h,Units.val_inv_eq_inv_val,mul_inv_cancel₀ x.ne_zero,one_mul]

/-- Simultaneous inner coordinate change. -/
theorem inner_coordinates (a g : PairSL (F := F)) (v : Mat (F := F)) :
    matrixAction a (matrixAction g v) =
      matrixAction ((MulAut.conj a) g) (matrixAction a v) := by
  change matrixHom a (matrixHom g v) = matrixHom ((MulAut.conj a) g) (matrixHom a v)
  rw [←LinearEquiv.mul_apply,←map_mul,←LinearEquiv.mul_apply,←map_mul]
  congr 2
  change a*g=(a*g*a⁻¹)*a
  group
end ClassicalOrthogonal.FourPlusMatrix.SplitCartan
