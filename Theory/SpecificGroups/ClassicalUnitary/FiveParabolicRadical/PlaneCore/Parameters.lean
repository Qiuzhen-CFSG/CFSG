module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Ring

/-!
# Coordinates for the unitary-five plane unipotent group

The matrices have blocks `[[I,x,z],[0,1,x*],[0,0,I]]`, where
`z + z* = x x*`. Multiplication adds the vectors and adds `x y*` to
the upper-right block. In characteristic two every element has fourth
power one. The representation is faithful and has determinant one.

The connection with the chosen identity-form flag is supplied in `Matrices`.
These results alone do not identify the full parabolic kernel or its core.

Source: the unitary plane-parabolic calculation underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp. 263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

structure Parameters where
  x : Fin 2 → F
  z : Matrix (Fin 2) (Fin 2) F
  relation : ∀ i j, z i j + J.conj (z j i) = x i * J.conj (x j)

namespace Parameters
variable {J}
@[simp]theorem conj_conj (a : F) : J.conj (J.conj a) = a := J.conj_involutive a
@[ext]theorem ext {u v : Parameters J} (hx : u.x = v.x) (hz : u.z = v.z) : u = v := by
  cases u; cases v; cases hx; cases hz; rfl

instance : One (Parameters J) := ⟨⟨0, 0, by simp⟩⟩
instance : Mul (Parameters J) := ⟨fun u v =>
  ⟨u.x + v.x, fun i j => u.z i j + v.z i j + u.x i * J.conj (v.x j), by
    intro i j
    simp only [map_add, map_mul, conj_conj, Pi.add_apply]
    calc
      _ = (u.z i j + J.conj (u.z j i)) + (v.z i j + J.conj (v.z j i)) +
          u.x i * J.conj (v.x j) + v.x i * J.conj (u.x j) := by ring
      _ = _ := by rw [u.relation, v.relation]; ring⟩⟩
@[simp]theorem one_x : (1 : Parameters J).x = 0 := rfl
@[simp]theorem one_z : (1 : Parameters J).z = 0 := rfl
@[simp]theorem mul_x (u v : Parameters J) : (u * v).x = u.x + v.x := rfl
@[simp]theorem mul_z (u v : Parameters J) (i j : Fin 2) :
    (u * v).z i j = u.z i j + v.z i j + u.x i * J.conj (v.x j) := rfl
variable [CharP F 2]

instance : Inv (Parameters J) := ⟨fun u =>
  ⟨u.x, fun i j => u.z i j + u.x i * J.conj (u.x j), by
    intro i j
    simp only [map_add, map_mul, conj_conj]
    calc
      _ = (u.z i j + J.conj (u.z j i)) +
          (u.x i * J.conj (u.x j) + u.x i * J.conj (u.x j)) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero, u.relation]⟩⟩

@[simp]theorem inv_x (u : Parameters J) : u⁻¹.x = u.x := rfl
@[simp]theorem inv_z (u : Parameters J) (i j : Fin 2) :
    u⁻¹.z i j = u.z i j + u.x i * J.conj (u.x j) := rfl

instance : Group (Parameters J) := Group.ofLeftAxioms
  (by
    intro u v w
    apply ext
    · simp [add_assoc]
    · funext i j
      simp only [mul_z, mul_x, Pi.add_apply, map_add]
      ring)
  (by
    intro u
    apply ext
    · simp
    · funext i j; simp)
  (by
    intro u
    apply ext
    · funext i; simp [CharTwo.add_self_eq_zero]
    · funext i j
      simp only [mul_z, inv_z, inv_x, one_z, Matrix.zero_apply]
      calc
        _ = (u.z i j + u.z i j) +
            (u.x i * J.conj (u.x j) + u.x i * J.conj (u.x j)) := by ring
        _ = 0 := by simp [CharTwo.add_self_eq_zero])

theorem pow_four (u : Parameters J) : u ^ 4 = 1 := by
  have he : u ^ 4 = (u * u) * (u * u) := by simp only [show 4 = 2 * 2 from rfl, pow_mul, pow_two]
  rw [he]
  apply ext
  · funext i; simp [CharTwo.add_self_eq_zero]
  · funext i j
    simp [CharTwo.add_self_eq_zero]

theorem isPGroup : IsPGroup 2 (Parameters J) := by
  intro u
  exact ⟨2, pow_four u⟩

/-- The unipotent matrix in coordinates of dimensions two, one and two. -/
def matrix (u : Parameters J) : Matrix (Fin 5) (Fin 5) F :=
  !![1, 0, u.x 0, u.z 0 0, u.z 0 1;
     0, 1, u.x 1, u.z 1 0, u.z 1 1;
     0, 0, 1, J.conj (u.x 0), J.conj (u.x 1);
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

omit [CharP F 2] in
@[simp]theorem matrix_one : matrix (1 : Parameters J) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

omit [CharP F 2] in
theorem matrix_mul (u v : Parameters J) : matrix (u * v) = matrix u * matrix v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

omit [CharP F 2] in
theorem matrix_injective : Function.Injective (matrix (J := J)) := by
  intro u v h
  apply ext
  · funext i
    fin_cases i
    · exact congrArg (fun A => A 0 2) h
    · exact congrArg (fun A => A 1 2) h
  · funext i j
    fin_cases i <;> fin_cases j
    · exact congrArg (fun A => A 0 3) h
    · exact congrArg (fun A => A 0 4) h
    · exact congrArg (fun A => A 1 3) h
    · exact congrArg (fun A => A 1 4) h

omit [CharP F 2] in
theorem matrix_det (u : Parameters J) : (matrix u).det = 1 := by
  have ht : (matrix u).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [matrix]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [matrix, Fin.prod_univ_succ]

/-- The matrix representation with its explicitly known inverse. -/
def toGL : Parameters J →* GL (Fin 5) F where
  toFun u := ⟨matrix u, matrix u⁻¹,
    by rw [← matrix_mul, mul_inv_cancel, matrix_one],
    by rw [← matrix_mul, inv_mul_cancel, matrix_one]⟩
  map_one' := Units.ext matrix_one
  map_mul' u v := Units.ext (matrix_mul u v)

theorem toGL_injective : Function.Injective (toGL (J := J)) := by
  intro u v h
  exact matrix_injective (congrArg Units.val h)

end Parameters
end Theory.SpecificGroups.UnitaryFive.PlaneCore
