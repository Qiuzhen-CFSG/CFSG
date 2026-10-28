module
public import BenderSuzuki.MatrixGroups.HermitianConjugation
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Ring.Action.End

/-!
# Special unitary groups over the fixed field

For a two-dimensional Hermitian form J over a field F, suppose an invertible
basis matrix C transports its Gram matrix to a nonzero scalar multiple of
the standard alternating matrix. Then J's actual special unitary subgroup
is isomorphic to SL₂ over the actual fixed subfield of J's stored involution.
The inverse equivalence is specified as coefficient embedding followed by
conjugation by C. A concrete identity-Gram basis is supplied from a norm−1
element z and a nonzero anti-fixed element t, when 2 is nonzero.

These are the generic matrix proofs extracted from ABG II.2 Lemma 1(vi),
article p.17. The two-by-two determinant calculation says that a determinant-one
matrix preserves the alternating Hermitian form exactly when its entries
are fixed by the involution. The shared Hermitian conjugation criterion
then gives the equivalence. The explicit basis matrix [[1,t],[z,−zt]] has
nonzero determinant −2zt and transported Gram matrix 2t times the alternating
matrix. Its entry specification and the inverse-equivalence formula support
coefficient-equivariance in ABG II.3 Proposition 3, without replacing the
original form, involution, or group.
-/

open Matrix
open scoped Matrix
open BenderSuzuki.MatrixGroups

namespace BenderSuzuki.MatrixGroups.HermitianForm

variable {F : Type*} [Field F]

private theorem skew_preserves_iff_fixed (σ : F ≃+* F)
    (B : Matrix (Fin 2) (Fin 2) F) (hdet : B.det = 1) :
    (B.map σ).transpose * !![0, 1; -1, 0] * B = !![0, 1; -1, 0] ↔
      ∀ i j, σ (B i j) = B i j := by
  have hd : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [det_fin_two] using hdet
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) h
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) h
    simp [mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    intro i j
    fin_cases i <;> fin_cases j
    · change σ (B 0 0) = B 0 0
      linear_combination B 0 0 * h01 - B 0 1 * h00 - σ (B 0 0) * hd
    · change σ (B 0 1) = B 0 1
      linear_combination B 0 0 * h11 - B 0 1 * h10 - σ (B 0 1) * hd
    · change σ (B 1 0) = B 1 0
      linear_combination B 1 0 * h01 - B 1 1 * h00 - σ (B 1 0) * hd
    · change σ (B 1 1) = B 1 1
      linear_combination B 1 0 * h11 - B 1 1 * h10 - σ (B 1 1) * hd
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, h]
    · ring
    · linear_combination hd
    · linear_combination -hd
    · ring

private theorem special_mem_conjugate_iff (J : HermitianForm 2 F)
    (C : GL (Fin 2) F) (s : F) (hs : s ≠ 0)
    (hC : J.conjTranspose C.val * J.form * C.val = s • !![0, 1; -1, 0])
    (B : GL (Fin 2) F) :
    C * B * C⁻¹ ∈ J.specialSubgroup ↔
      B.val.det = 1 ∧ ∀ i j, J.conj (B.val i j) = B.val i j := by
  rw [J.mem_specialSubgroup_iff, J.conjugate_preserves_iff, hC]
  have hd : GeneralLinearGroup.det (C * B * C⁻¹) = 1 ↔ B.val.det = 1 := by
    simp only [map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel, one_mul]
    constructor
    · exact fun h => congrArg Units.val h
    · exact fun h => Units.ext h
  rw [hd, Matrix.mul_smul, Matrix.smul_mul, smul_right_inj hs]
  constructor
  · rintro ⟨hB, hdet⟩
    exact ⟨hdet, (skew_preserves_iff_fixed J.conj B.val hdet).mp hB⟩
  · rintro ⟨hdet, hB⟩
    exact ⟨(skew_preserves_iff_fixed J.conj B.val hdet).mpr hB, hdet⟩

public noncomputable def specialUnitaryEquivFixed (J : HermitianForm 2 F)
    (C : GL (Fin 2) F) (s : F) (hs : s ≠ 0)
    (hC : J.conjTranspose C.val * J.form * C.val = s • !![0, 1; -1, 0]) :
    J.specialSubgroup ≃* SpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj) := by
  let K := FixedBy.subfield F J.conj
  let φ : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) F :=
    (MulAut.conj C).toMonoidHom.comp
      (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map K.subtype))
  have hφ (A : SpecialLinearGroup (Fin 2) K) : φ A ∈ J.specialSubgroup := by
    apply (special_mem_conjugate_iff J C s hs hC _).mpr
    refine ⟨(SpecialLinearGroup.map K.subtype A).property, ?_⟩
    intro i j
    exact (A.val i j).property
  let ψ := φ.codRestrict J.specialSubgroup hφ
  apply (MulEquiv.ofBijective ψ ?_).symm
  constructor
  · intro A B h
    have he : φ A = φ B := congrArg Subtype.val h
    have hm := SpecialLinearGroup.toGL_injective ((MulAut.conj C).injective he)
    apply Subtype.ext
    ext i j
    exact congrArg (fun M : SpecialLinearGroup (Fin 2) F => M.val i j) hm
  · intro A
    let B : GL (Fin 2) F := C⁻¹ * A.val * C
    have hB : C * B * C⁻¹ ∈ J.specialSubgroup := by
      simp [B, mul_assoc]
    obtain ⟨hd, hf⟩ := (special_mem_conjugate_iff J C s hs hC B).mp hB
    let Dmat : Matrix (Fin 2) (Fin 2) K := fun i j => ⟨B.val i j, hf i j⟩
    let D : SpecialLinearGroup (Fin 2) K := ⟨Dmat, by
      apply K.subtype.injective
      change K.subtype Dmat.det = 1
      exact (K.subtype.map_det Dmat).trans hd⟩
    refine ⟨D, Subtype.ext ?_⟩
    change C * SpecialLinearGroup.toGL (SpecialLinearGroup.map K.subtype D) * C⁻¹ = A.val
    have he : SpecialLinearGroup.toGL (SpecialLinearGroup.map K.subtype D) = B :=
      Units.ext rfl
    rw [he]
    simp [B, mul_assoc]

/-- The inverse equivalence is the actual conjugated coefficient embedding. -/
@[simp] public theorem specialUnitaryEquivFixed_symm_apply_val (J : HermitianForm 2 F)
    (C : GL (Fin 2) F) (s : F) (hs : s ≠ 0)
    (hC : J.conjTranspose C.val * J.form * C.val = s • !![0, 1; -1, 0])
    (A : SpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj)) :
    ((J.specialUnitaryEquivFixed C s hs hC).symm A).val =
      C * SpecialLinearGroup.toGL
        (SpecialLinearGroup.map (FixedBy.subfield F J.conj).subtype A) * C⁻¹ := by
  rfl

public theorem exists_skew_basis (J : HermitianForm 2 F) (hJ : J.form = 1)
    (h2 : (2 : F) ≠ 0) (z t : F) (hz : z * J.conj z = -1)
    (ht0 : t ≠ 0) (ht : J.conj t = -t) :
    ∃ C : GL (Fin 2) F, C.val = !![1, t; z, -z * t] ∧
      J.conjTranspose C.val * J.form * C.val = (2 * t) • !![0, 1; -1, 0] := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  let M : Matrix (Fin 2) (Fin 2) F := !![1, t; z, -z * t]
  have hdet : M.det ≠ 0 := by
    have he : M.det = -(2 * z * t) := by simp [M, det_fin_two]; ring
    rw [he]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero h2 hz0) ht0)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hdet, rfl, ?_⟩
  change J.conjTranspose M * J.form * M = _
  rw [hJ, mul_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, HermitianForm.conjTranspose, mul_apply, Fin.sum_univ_two, ht]
  · linear_combination hz
  · linear_combination -t * hz
  · linear_combination t * hz
  · linear_combination -(t * t) * hz


end BenderSuzuki.MatrixGroups.HermitianForm

