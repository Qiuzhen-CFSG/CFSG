module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
public import BenderSuzuki.MatrixGroups.SpecialUnitaryFixedEquiv
public import Theory.SpecificGroups.SL2.TwoCore
public import Theory.Representation.SL2NaturalFirstCohomology
public import Theory.GroupTheory.PCoreSurjective

/-!
# The quotient and Levi factor of the unitary-four point local

The middle block of a matrix fixing the first isotropic vector preserves the
antidiagonal Hermitian form and has determinant one. The diagonal embedding
of this SU₂ is a section, so the quotient by the radical is this actual SU₂.
In characteristic two its Gram matrix is alternating, identifying it with
SL₂ over the fixed subfield, and hence with PSL₂. Its two-core is trivial,
including over the binary field. Once the radical is a two-group it is
therefore exactly the two-core of the vector stabilizer.

The Levi section and its conjugation on the entire Heisenberg radical are
explicit matrices. Source: Aschbacher--Smith F.1.12(I)(6), printed pp. 263--264
of `refs/quasithin.pdf`; the residual calculations use this action separately.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
variable (F : Type*) [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)
def middleForm : HermitianForm 2 F where
  conj := σ
  conj_involutive := hσ
  form := !![0,1;1,0]
  form_hermitian := by intro i j; fin_cases i <;> fin_cases j <;> simp
  form_nondegenerate := by simp [det_fin_two]

theorem middle_det (a : localSU F (form F σ hσ)) : (middleBlock F σ hσ a).det = 1 := by
  obtain ⟨h00,h10,h20,h30⟩ := (mem_localSU F _ a.val).mp a.property
  obtain ⟨_,h31,h32,h33⟩ := last_row F σ hσ a.val a.property
  have hd : a.val.val.val.det = 1 := congrArg Units.val a.val.property.2
  rw [det_succ_column_zero] at hd
  simpa [Fin.sum_univ_succ, h00,h10,h20,h30,h31,h32,h33,
    det_fin_three, det_fin_two, middleBlock] using hd

theorem middle_unitary (a : localSU F (form F σ hσ)) :
    (middleForm F σ hσ).conjTranspose (middleBlock F σ hσ a) *
      (middleForm F σ hσ).form * middleBlock F σ hσ a = (middleForm F σ hσ).form := by
  obtain ⟨_,h31,h32,_⟩ := last_row F σ hσ a.val a.property
  have hu := a.val.property.1
  change (form F σ hσ).conjTranspose a.val.val.val * gram F * a.val.val.val = gram F at hu
  have h11 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 1) hu
  have h12 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 2) hu
  have h21 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 1) hu
  have h22 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 2) hu
  simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ, h31,h32] at h11 h12 h21 h22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleForm, middleBlock, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ, h11,h12,h21,h22]

def middleSU : localSU F (form F σ hσ) →* (middleForm F σ hσ).specialSubgroup where
  toFun a := ⟨GeneralLinearGroup.mkOfDetNeZero (middleBlock F σ hσ a)
    (by rw [middle_det]; exact one_ne_zero),
    middle_unitary F σ hσ a, Units.ext (middle_det F σ hσ a)⟩
  map_one' := by apply Subtype.ext; apply Units.ext; exact (middleBlock F σ hσ).map_one
  map_mul' a b := by apply Subtype.ext; apply Units.ext; exact (middleBlock F σ hσ).map_mul a b

def leviMatrix (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![1,0,0,0; 0,B 0 0,B 0 1,0; 0,B 1 0,B 1 1,0; 0,0,0,1]

theorem leviMatrix_det (B : Matrix (Fin 2) (Fin 2) F) : (leviMatrix F B).det = B.det := by
  rw [det_succ_column_zero]
  simp [leviMatrix, Fin.sum_univ_succ, det_fin_three, det_fin_two]

theorem leviMatrix_unitary (B : (middleForm F σ hσ).specialSubgroup) :
    (form F σ hσ).conjTranspose (leviMatrix F B.val.val) * gram F *
      leviMatrix F B.val.val = gram F := by
  have hu := B.property.1
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hu
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hu
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hu
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hu
  simp [middleForm, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]
    at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [form, gram, leviMatrix, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ, h00,h01,h10,h11]

def levi : (middleForm F σ hσ).specialSubgroup →* localSU F (form F σ hσ) where
  toFun B := ⟨⟨GeneralLinearGroup.mkOfDetNeZero (leviMatrix F B.val.val)
    (by rw [leviMatrix_det]; exact B.val.det_ne_zero),
    leviMatrix_unitary F σ hσ B, Units.ext (by
      change (leviMatrix F B.val.val).det = 1
      rw [leviMatrix_det]; exact congrArg Units.val B.property.2)⟩, by
        rw [mem_localSU]; simp [leviMatrix]⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [leviMatrix]
  map_mul' A B := by
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [leviMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem middleSU_levi (B : (middleForm F σ hσ).specialSubgroup) :
    middleSU F σ hσ (levi F σ hσ B) = B := by
  apply Subtype.ext; apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem middleSU_surjective : Function.Surjective (middleSU F σ hσ) :=
  fun B => ⟨levi F σ hσ B, middleSU_levi F σ hσ B⟩

theorem middleSU_ker : (middleSU F σ hσ).ker = radical F σ hσ := by
  ext a
  change middleSU F σ hσ a = 1 ↔ middleBlock F σ hσ a = 1
  constructor
  · exact fun h => congrArg (fun x => x.val.val) h
  · intro h; exact Subtype.ext (Units.ext h)

variable [CharP F 2]
def middleEquivSL : (middleForm F σ hσ).specialSubgroup ≃*
    SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) :=
  (middleForm F σ hσ).specialUnitaryEquivFixed 1 1 one_ne_zero (by
    change ((1 : Matrix (Fin 2) (Fin 2) F).map σ).transpose * !![0,1;1,0] * 1 =
      (1 : F) • !![0,1;-1,0]
    simp [CharTwo.neg_eq])

/-- In the identity basis the inverse equivalence literally embeds coefficients. -/
@[simp] theorem middleEquivSL_symm_val
    (B : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) :
    ((middleEquivSL F σ hσ).symm B).val.val =
      B.val.map (FixedBy.subfield F σ).subtype := by
  have h := HermitianForm.specialUnitaryEquivFixed_symm_apply_val
    (middleForm F σ hσ) 1 1 one_ne_zero
    (by
      change ((1 : Matrix (Fin 2) (Fin 2) F).map σ).transpose * !![0,1;1,0] * 1 =
        (1 : F) • !![0,1;-1,0]
      simp [CharTwo.neg_eq]) B
  change ((middleEquivSL F σ hσ).symm B).val =
    1 * SpecialLinearGroup.toGL (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype B) *
      (1 : GL (Fin 2) F)⁻¹ at h
  simp only [one_mul, inv_one, mul_one] at h
  calc
    _ = (SpecialLinearGroup.toGL
        (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype B)).val := congrArg Units.val h
    _ = _ := rfl

/-- The action on the perpendicular quotient with entries in the fixed field. -/
def middleSL : localSU F (form F σ hσ) →*
    SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) :=
  (middleEquivSL F σ hσ).toMonoidHom.comp (middleSU F σ hσ)

/-- The diagonal Levi section parametrized by SL₂ over the actual fixed field. -/
def leviSL : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) →*
    localSU F (form F σ hσ) :=
  (levi F σ hσ).comp (middleEquivSL F σ hσ).symm.toMonoidHom

@[simp] theorem middleSL_leviSL (B : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) :
    middleSL F σ hσ (leviSL F σ hσ B) = B := by
  simp [middleSL, leviSL]

@[simp] theorem leviSL_val (B : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) :
    (leviSL F σ hσ B).val.val.val =
      leviMatrix F (B.val.map (FixedBy.subfield F σ).subtype) := by
  change leviMatrix F ((middleEquivSL F σ hσ).symm B).val.val = _
  rw [middleEquivSL_symm_val]

def quotientEquivSL : (localSU F (form F σ hσ) ⧸ radical F σ hσ) ≃*
    SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) :=
  (QuotientGroup.quotientMulEquivOfEq (middleSU_ker F σ hσ).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective (middleSU F σ hσ)
      (middleSU_surjective F σ hσ)).trans (middleEquivSL F σ hσ))

@[simp] theorem quotientEquivSL_mk (a : localSU F (form F σ hσ)) :
    quotientEquivSL F σ hσ (QuotientGroup.mk a) = middleSL F σ hσ a := rfl

/-- Conjugation by the actual diagonal Levi matrices on the entire radical. -/
def leviConjugate (B : (middleForm F σ hσ).specialSubgroup)
    (c : RadicalCoordinates F σ) : radical F σ hσ :=
  ⟨levi F σ hσ B * (radicalOfCoordinates F σ hσ c).val * (levi F σ hσ B)⁻¹,
    (radical_normal F σ hσ).conj_mem _ (radicalOfCoordinates F σ hσ c).property _⟩

theorem levi_conjugation_coordinates (B : (middleForm F σ hσ).specialSubgroup)
    (c : RadicalCoordinates F σ) :
    let d := coordinatesOfRadical F σ hσ (leviConjugate F σ hσ B c)
    d.x = B.val.val 0 0 * c.x + B.val.val 0 1 * c.y ∧
    d.y = B.val.val 1 0 * c.x + B.val.val 1 1 * c.y ∧ d.z = c.z := by
  dsimp only [coordinatesOfRadical, leviConjugate]
  rw [← map_inv]
  change ((leviMatrix F B.val.val * radicalMatrix F σ c) *
    leviMatrix F (B⁻¹).val.val) 1 3 = _ ∧
    ((leviMatrix F B.val.val * radicalMatrix F σ c) *
    leviMatrix F (B⁻¹).val.val) 2 3 = _ ∧
    ((leviMatrix F B.val.val * radicalMatrix F σ c) *
    leviMatrix F (B⁻¹).val.val) 0 3 = _
  simp [leviMatrix, radicalMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The fixed-field SL₂ section acts by its natural matrix on `(x,y)` and fixes `z`. -/
theorem leviSL_conjugation_coordinates
    (B : SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) (c : RadicalCoordinates F σ) :
    let d := coordinatesOfRadical F σ hσ
      (leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm B) c)
    d.x = (B.val 0 0 : F) * c.x + (B.val 0 1 : F) * c.y ∧
    d.y = (B.val 1 0 : F) * c.x + (B.val 1 1 : F) * c.y ∧ d.z = c.z := by
  simpa only [middleEquivSL_symm_val, Matrix.map_apply, Subfield.subtype_apply] using
    levi_conjugation_coordinates F σ hσ ((middleEquivSL F σ hσ).symm B) c


/-- The actual projective special linear quotient over the stored fixed field. -/
def quotientEquivPSL : (localSU F (form F σ hσ) ⧸ radical F σ hσ) ≃*
    ProjectiveSpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) :=
  (quotientEquivSL F σ hσ).trans Representation.SL2NaturalH1.projectiveEquiv.symm

/-- Triviality also holds when the fixed field has order two. -/
theorem quotient_twoCore_eq_bot [Finite F] :
    pCore 2 (localSU F (form F σ hσ) ⧸ radical F σ hσ) = ⊥ := by
  let e := quotientEquivSL F σ hσ
  have h := pCore_map_iso 2 e
  rw [Matrix.SL2.twoCore_eq_bot] at h
  exact (Subgroup.map_injective e.injective) (h.trans (Subgroup.map_bot _).symm)

/-- The kernel is the exact two-core whenever it is a two-group. -/
theorem radical_eq_twoCore [Finite F] (h : IsPGroup 2 (radical F σ hσ)) :
    radical F σ hσ = pCore 2 (localSU F (form F σ hσ)) := by
  have hker : IsPGroup 2 (QuotientGroup.mk' (radical F σ hσ)).ker := by
    rwa [QuotientGroup.ker_mk']
  have he := (QuotientGroup.mk' (radical F σ hσ)).comap_pCore_of_ker_isPGroup
    (QuotientGroup.mk'_surjective _) hker
  rw [quotient_twoCore_eq_bot] at he
  change (QuotientGroup.mk' (radical F σ hσ)).ker = _ at he
  rwa [QuotientGroup.ker_mk'] at he

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
