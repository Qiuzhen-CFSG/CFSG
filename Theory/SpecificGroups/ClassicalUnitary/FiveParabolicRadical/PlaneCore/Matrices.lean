module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Parameters
import Mathlib.Tactic.Ring

/-!
# A faithful plane-unipotent subgroup in the identity-form unitary group

Conjugate the block matrices of `Parameters` by the basis with columns
`(1,1,0,0,0)`, `(0,0,1,1,0)`, `(0,0,0,0,1)`, `(0,1,0,0,0)` and
`(0,0,0,1,0)`. The resulting matrices have determinant one, preserve the
identity Hermitian form and fix the chosen plane pointwise. Their bottom
right entry is one, which rules out a nontrivial scalar kernel in PGL.

This constructs an actual subgroup of the projective plane parabolic and
identifies it with the parameter group. Identifying it as the full radical,
proving normality, and identifying the residual's canonical core require the
separate Levi calculation; they are not consequences asserted here.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12(7), printed pp. 263--264, standard unitary parabolic matrices.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- Basis with columns spanning the chosen isotropic plane first. -/
def flagBasis : Matrix (Fin 5) (Fin 5) F :=
  !![1,0,0,0,0; 1,0,0,1,0; 0,1,0,0,0; 0,1,0,0,1; 0,0,1,0,0]

def flagBasisInv : Matrix (Fin 5) (Fin 5) F :=
  !![1,0,0,0,0; 0,0,1,0,0; 0,0,0,0,1; 1,1,0,0,0; 0,0,1,1,0]

theorem flagBasis_mul_inv :
    (flagBasis : Matrix (Fin 5) (Fin 5) F) * flagBasisInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flagBasis, flagBasisInv, Matrix.mul_apply, Fin.sum_univ_succ,
      CharTwo.add_self_eq_zero]

theorem flagBasis_inv_mul :
    (flagBasisInv : Matrix (Fin 5) (Fin 5) F) * flagBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flagBasis, flagBasisInv, Matrix.mul_apply, Fin.sum_univ_succ,
      CharTwo.add_self_eq_zero]

def flagBasisGL : GL (Fin 5) F :=
  ⟨flagBasis, flagBasisInv, flagBasis_mul_inv, flagBasis_inv_mul⟩

namespace Parameters
variable {J}

/-- The same matrices in the original identity-form coordinates. -/
def ambientMatrix (u : Parameters J) : Matrix (Fin 5) (Fin 5) F :=
  !![1 + u.z 0 0, u.z 0 0, u.z 0 1, u.z 0 1, u.x 0;
     u.z 0 0, 1 + u.z 0 0, u.z 0 1, u.z 0 1, u.x 0;
     u.z 1 0, u.z 1 0, 1 + u.z 1 1, u.z 1 1, u.x 1;
     u.z 1 0, u.z 1 0, u.z 1 1, 1 + u.z 1 1, u.x 1;
     J.conj (u.x 0), J.conj (u.x 0), J.conj (u.x 1), J.conj (u.x 1), 1]

theorem ambientMatrix_eq (u : Parameters J) :
    ambientMatrix u = flagBasis * matrix u * flagBasisInv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientMatrix, flagBasis, flagBasisInv, matrix, Matrix.mul_apply,
      Fin.sum_univ_succ, add_comm] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

/-- A faithful representation on the original five coordinates. -/
def ambientGL : Parameters J →* GL (Fin 5) F :=
  (MulAut.conj (flagBasisGL (F := F))).toMonoidHom.comp toGL

theorem ambientGL_val (u : Parameters J) :
    (ambientGL u : Matrix (Fin 5) (Fin 5) F) = ambientMatrix u :=
  (ambientMatrix_eq u).symm

theorem ambientGL_injective : Function.Injective (ambientGL (J := J)) :=
  (MulAut.conj (flagBasisGL (F := F))).injective.comp toGL_injective

set_option maxRecDepth 2048 in
theorem ambientGL_det (u : Parameters J) :
    Matrix.GeneralLinearGroup.det (ambientGL u) = 1 := by
  change Matrix.GeneralLinearGroup.det (flagBasisGL * toGL u * flagBasisGL⁻¹) = 1
  rw [map_mul, map_mul, map_inv]
  have hu : Matrix.GeneralLinearGroup.det (toGL u) = 1 := Units.ext (matrix_det u)
  rw [hu, mul_one, mul_inv_cancel]

theorem ambientMatrix_preserves (u : Parameters J) :
    J.conjTranspose (ambientMatrix u) * ambientMatrix u = 1 := by
  have h00 := u.relation 0 0
  have h01 := u.relation 0 1
  have h10 := u.relation 1 0
  have h11 := u.relation 1 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientMatrix, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ, conj_conj] <;>
    ring_nf <;>
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add] <;>
    simp only [← h00, ← h01, ← h10, ← h11] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]


/-- The explicitly constructed special-unitary matrices. -/
def toSU (hJ : J.form = 1) : Parameters J →* J.specialSubgroup :=
  ambientGL.codRestrict _ (by
    intro u
    rw [J.mem_specialSubgroup_iff]
    refine ⟨?_, ambientGL_det u⟩
    rw [hJ, mul_one, ambientGL_val]
    exact ambientMatrix_preserves u)

theorem fixes_plane (u : Parameters J) (v : Fin 5 → F) (hv : v ∈ plane F) :
    ambientMatrix u *ᵥ v = v := by
  change v 1 = v 0 ∧ v 3 = v 2 ∧ v 4 = 0 at hv
  ext i
  fin_cases i <;>
    simp [ambientMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hv.1, hv.2.1, hv.2.2] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero]

theorem toSU_fixes_plane (hJ : J.form = 1) (u : Parameters J)
    (v : Fin 5 → F) (hv : v ∈ plane F) :
    linearAction J (toSU hJ u) v = v := by
  change (ambientGL u : Matrix (Fin 5) (Fin 5) F) *ᵥ v = v
  rw [ambientGL_val]
  exact fixes_plane u v hv

theorem toSU_mem_stabilizer (hJ : J.form = 1) (u : Parameters J) :
    toSU hJ u ∈ specialStabilizer J (plane F) := by
  rw [mem_specialStabilizer_iff]
  intro v
  change linearAction J (toSU hJ u) v ∈ plane F ↔ v ∈ plane F
  constructor
  · intro hv
    have he := toSU_fixes_plane hJ u⁻¹ _ hv
    have hi : linearAction J (toSU hJ u⁻¹)
        (linearAction J (toSU hJ u) v) = v := by
      rw [map_inv, map_inv]
      exact (linearAction J (toSU hJ u)).symm_apply_apply v
    rw [hi] at he
    exact he ▸ hv
  · intro hv
    rw [toSU_fixes_plane hJ u v hv]
    exact hv

/-- The homomorphism into the exact SU plane stabilizer. -/
def toStabilizer (hJ : J.form = 1) : Parameters J →* specialStabilizer J (plane F) :=
  (toSU hJ).codRestrict _ (toSU_mem_stabilizer hJ)

/-- The homomorphism into the actual projective plane parabolic. -/
def toParabolic (hJ : J.form = 1) : Parameters J →* planeParabolic J :=
  ((project J).subgroupMap (specialStabilizer J (plane F))).comp (toStabilizer hJ)

theorem toParabolic_injective (hJ : J.form = 1) :
    Function.Injective (toParabolic hJ) := by
  apply (injective_iff_map_eq_one _).mpr
  intro u hu
  have hp : project J (toSU hJ u) = 1 := congrArg Subtype.val hu
  have hs : Matrix.ProjGenLinGroup.mk (ambientGL u) = 1 := congrArg Subtype.val hp
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨a, ha⟩ := hs
  have he := congrArg (fun A : GL (Fin 5) F => (A : Matrix (Fin 5) (Fin 5) F) 4 4) ha
  rw [ambientGL_val] at he
  have hav : a.val = 1 := by simpa [ambientMatrix] using he
  have haone : a = 1 := Units.ext hav
  subst a
  have huone : ambientGL u = 1 := by simpa using ha.symm
  apply ambientGL_injective
  simpa using huone

end Parameters

/-- The concrete projective unipotent subgroup. Normality and maximality
are separate parabolic-structure assertions. -/
def projectiveUnipotent (hJ : J.form = 1) : Subgroup (planeParabolic J) :=
  (Parameters.toParabolic hJ).range

noncomputable def parametersEquiv (hJ : J.form = 1) :
    Parameters J ≃* projectiveUnipotent J hJ :=
  MonoidHom.ofInjective (Parameters.toParabolic_injective hJ)

theorem projectiveUnipotent_isPGroup (hJ : J.form = 1) :
    IsPGroup 2 (projectiveUnipotent J hJ) :=
  Parameters.isPGroup.of_equiv (parametersEquiv J hJ)

theorem projectiveUnipotent_card (hJ : J.form = 1) :
    Nat.card (projectiveUnipotent J hJ) = Nat.card (Parameters J) :=
  Nat.card_congr (parametersEquiv J hJ).symm.toEquiv

end Theory.SpecificGroups.UnitaryFive.PlaneCore
