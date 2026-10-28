module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Embedding

/-!
# The special-unitary Levi action in the five-dimensional line parabolic

The identity-form SU₃ embeds by the block matrix `diag(1,1,A)` in the original
basis. This embedding stays faithful after projectivizing. Conjugation sends
the radical coordinates `(v,t)` to `(Av,t)`, as verified by matrix multiplication.
The middle group has the model's actual involution and identity Hermitian form.

Source: the classical unitary calculation used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp.263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

def middleForm : HermitianForm 3 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := 1
  form_hermitian := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

def middleAction : (middleForm J).specialSubgroup →*
    ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 3 → F)).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp (middleForm J).specialSubgroup.subtype

theorem middle_unitary (A : (middleForm J).specialSubgroup) :
    (A.val.val.map J.conj).transpose * A.val.val = 1 := by
  have h := ((middleForm J).mem_specialSubgroup_iff A.val).mp A.property |>.1
  change (A.val.val.map J.conj).transpose * 1 * A.val.val = 1 at h
  simpa only [mul_one] using h

theorem middleAction_preserves_pairing (A : (middleForm J).specialSubgroup)
    (v w : Fin 3 → F) :
    pairing J (middleAction J A v) (middleAction J A w) = pairing J v w := by
  change (J.conj ∘ (A.val.val *ᵥ v)) ⬝ᵥ (A.val.val *ᵥ w) = (J.conj ∘ v) ⬝ᵥ w
  have hc : J.conj ∘ (A.val.val *ᵥ v) = A.val.val.map J.conj *ᵥ (J.conj ∘ v) := by
    ext i
    exact J.conj.toRingHom.map_mulVec _ _ i
  rw [hc, dotProduct_mulVec, vecMul_mulVec, middle_unitary, vecMul_one]

def leviAction : (middleForm J).specialSubgroup →* MulAut (Coord J) where
  toFun A := Coord.isometryAut (middleAction J A) (middleAction_preserves_pairing J A)
  map_one' := by
    apply MulEquiv.ext
    intro u
    apply Coord.ext
    · exact congrArg (fun e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) => e u.vector)
        (middleAction J).map_one
    · rfl
  map_mul' A B := by
    apply MulEquiv.ext
    intro u
    apply Coord.ext
    · exact congrArg (fun e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) => e u.vector)
        ((middleAction J).map_mul A B)
    · rfl

@[simp] theorem leviAction_vector (A : (middleForm J).specialSubgroup) (u : Coord J) :
    (leviAction J A u).vector = A.val.val *ᵥ u.vector := rfl

@[simp] theorem leviAction_scalar (A : (middleForm J).specialSubgroup) (u : Coord J) :
    (leviAction J A u).scalar = u.scalar := rfl

def leviMatrix (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 5) (Fin 5) F :=
  !![1,0,0,0,0; 0,1,0,0,0;
     0,0,A 0 0,A 0 1,A 0 2;
     0,0,A 1 0,A 1 1,A 1 2;
     0,0,A 2 0,A 2 1,A 2 2]

theorem leviMatrix_one : leviMatrix (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMatrix]

theorem leviMatrix_mul (A B : Matrix (Fin 3) (Fin 3) F) :
    leviMatrix (A * B) = leviMatrix A * leviMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem leviMatrix_det (A : Matrix (Fin 3) (Fin 3) F) : (leviMatrix A).det = A.det := by
  rw [det_succ_column_zero]
  simp only [leviMatrix, Fin.sum_univ_succ]
  rw [det_succ_column_zero]
  simp [Fin.sum_univ_succ, det_fin_three]

def leviGL : GL (Fin 3) F →* GL (Fin 5) F where
  toFun A := ⟨leviMatrix A.val, leviMatrix A.inv,
    by rw [← leviMatrix_mul, A.val_inv, leviMatrix_one],
    by rw [← leviMatrix_mul, A.inv_val, leviMatrix_one]⟩
  map_one' := Units.ext leviMatrix_one
  map_mul' A B := Units.ext (leviMatrix_mul A.val B.val)

theorem leviGL_injective : Function.Injective (leviGL (F := F)) := by
  intro A B h
  apply Units.ext
  ext i j
  have he := congrArg (fun X : GL (Fin 5) F =>
    X.val ⟨i.val + 2, by omega⟩ ⟨j.val + 2, by omega⟩) h
  fin_cases i <;> fin_cases j <;> exact he

theorem leviMatrix_preserves (A : (middleForm J).specialSubgroup) :
    J.conjTranspose (leviMatrix A.val.val) * leviMatrix A.val.val = 1 := by
  have hu := middle_unitary J A
  have h (i j : Fin 3) := congrArg (fun B : Matrix (Fin 3) (Fin 3) F => B i j) hu
  simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Fin.sum_univ_succ] at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMatrix, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals first
    | simpa using h 0 0
    | simpa using h 0 1
    | simpa using h 0 2
    | simpa using h 1 0
    | simpa using h 1 1
    | simpa using h 1 2
    | simpa using h 2 0
    | simpa using h 2 1
    | simpa using h 2 2

set_option maxRecDepth 2048 in
def leviSU (hJ : J.form = 1) : (middleForm J).specialSubgroup →* J.specialSubgroup :=
  ((leviGL (F := F)).comp (middleForm J).specialSubgroup.subtype).codRestrict _ (by
    intro A
    rw [J.mem_specialSubgroup_iff]
    constructor
    · change J.conjTranspose (leviMatrix A.val.val) * J.form * leviMatrix A.val.val = J.form
      rw [hJ, mul_one]
      exact leviMatrix_preserves J A
    · apply Units.ext
      change (leviMatrix A.val.val).det = 1
      rw [leviMatrix_det]
      exact congrArg Units.val A.property.2)

theorem leviSU_fixes_line (hJ : J.form = 1) (A : (middleForm J).specialSubgroup)
    (v : Fin 5 → F) (hv : v ∈ line F) :
    linearAction J (leviSU J hJ A) v = v := by
  change leviMatrix A.val.val *ᵥ v = v
  change v 1 = v 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 at hv
  ext i
  fin_cases i <;>
    simp [leviMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      hv.2.1, hv.2.2.1, hv.2.2.2]

theorem leviSU_mem_stabilizer (hJ : J.form = 1) (A : (middleForm J).specialSubgroup) :
    leviSU J hJ A ∈ specialStabilizer J (line F) := by
  rw [mem_specialStabilizer_iff]
  intro v
  change linearAction J (leviSU J hJ A) v ∈ line F ↔ v ∈ line F
  constructor
  · intro hv
    have he := leviSU_fixes_line J hJ A⁻¹ _ hv
    have hi : linearAction J (leviSU J hJ A⁻¹)
        (linearAction J (leviSU J hJ A) v) = v := by
      rw [map_inv, map_inv]
      exact (linearAction J (leviSU J hJ A)).symm_apply_apply v
    rw [hi] at he
    exact he ▸ hv
  · intro hv
    rw [leviSU_fixes_line J hJ A v hv]
    exact hv

def leviStabilizer (hJ : J.form = 1) :
    (middleForm J).specialSubgroup →* specialStabilizer J (line F) :=
  (leviSU J hJ).codRestrict _ (leviSU_mem_stabilizer J hJ)

def leviParabolic (hJ : J.form = 1) : (middleForm J).specialSubgroup →* lineParabolic J :=
  ((project J).subgroupMap (specialStabilizer J (line F))).comp (leviStabilizer J hJ)

theorem leviParabolic_injective (hJ : J.form = 1) :
    Function.Injective (leviParabolic J hJ) := by
  apply (injective_iff_map_eq_one _).mpr
  intro A hA
  have hp : project J (leviSU J hJ A) = 1 := congrArg Subtype.val hA
  have hs : Matrix.ProjGenLinGroup.mk (leviGL A.val) = 1 := congrArg Subtype.val hp
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨a, ha⟩ := hs
  have he := congrArg (fun X : GL (Fin 5) F => X.val 0 0) ha
  have haone : a = 1 := Units.ext he
  subst a
  have hle : leviGL A.val = 1 := by simpa using ha.symm
  apply Subtype.ext
  apply leviGL_injective
  simpa using hle

theorem leviMatrix_commutation (A : (middleForm J).specialSubgroup) (u : Coord J) :
    ambientMatrix J (leviAction J A u) * leviMatrix A.val.val =
      leviMatrix A.val.val * ambientMatrix J u := by
  have hc : J.conj ∘ (A.val.val *ᵥ u.vector) =
      A.val.val.map J.conj *ᵥ (J.conj ∘ u.vector) := by
    ext i
    exact J.conj.toRingHom.map_mulVec _ _ i
  have hr : (J.conj ∘ (A.val.val *ᵥ u.vector)) ᵥ* A.val.val = J.conj ∘ u.vector := by
    rw [hc, vecMul_mulVec, middle_unitary, vecMul_one]
  have h (i : Fin 3) := congrFun hr i
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientMatrix, leviMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.mulVec, dotProduct]
  all_goals first | exact h 0 | exact h 1 | exact h 2

variable [CharP F 2]

/-- The coordinate action is conjugation by the actual projective SU₃ matrices. -/
theorem toParabolic_leviAction (hJ : J.form = 1)
    (A : (middleForm J).specialSubgroup) (u : Coord J) :
    toParabolic J hJ (leviAction J A u) =
      leviParabolic J hJ A * toParabolic J hJ u * (leviParabolic J hJ A)⁻¹ := by
  have h : toSU J hJ (leviAction J A u) * leviSU J hJ A =
      leviSU J hJ A * toSU J hJ u := by
    apply Subtype.ext
    apply Units.ext
    change (ambientGL J (leviAction J A u)).val * leviMatrix A.val.val =
      leviMatrix A.val.val * (ambientGL J u).val
    rw [ambientGL_val, ambientGL_val]
    exact leviMatrix_commutation J A u
  have hs : toSU J hJ (leviAction J A u) =
      leviSU J hJ A * toSU J hJ u * (leviSU J hJ A)⁻¹ :=
    (eq_mul_inv_iff_mul_eq).mpr h
  apply Subtype.ext
  exact (congrArg (project J) hs).trans (by simp only [map_mul, map_inv]; rfl)

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
