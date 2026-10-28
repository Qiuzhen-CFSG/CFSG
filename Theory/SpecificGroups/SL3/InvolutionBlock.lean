module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination


/-!
# The standard involution centralizer in SL₃

Over a field of characteristic different from two, the centralizer of
`diag(-1,-1,1)` in SL₃ is GL₂. The actual embedding is
`A ↦ diag(A, det(A)⁻¹)`. Commutation with the involution forces the four
off-block entries to vanish, and determinant one then determines the final
entry. Reading the upper left block proves surjectivity and injectivity.

The construction works over any field and the embedding itself needs no
characteristic assumption. This is the linear standard-representative
calculation in Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.3.21(a), printed p. 55. Conjugacy of arbitrary involutions and the
prime residual of this centralizer are separate results.
-/

public section

open Matrix
open scoped Matrix
namespace Matrix.SL3
variable (F : Type*) [Field F]

/-- The determinant-one diagonal matrix with negative two-dimensional eigenspace. -/
@[expose] def standardInvolution : SpecialLinearGroup (Fin 3) F :=
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem standardInvolution_sq : standardInvolution F ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one]
  change (standardInvolution F).val * (standardInvolution F).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardInvolution, Matrix.mul_apply, Fin.sum_univ_three]

theorem standardInvolution_orderOf (h2 : (2 : F) ≠ 0) :
    orderOf (standardInvolution F) = 2 := by
  apply orderOf_eq_prime (standardInvolution_sq F)
  intro h
  have hh := congrArg (fun A : SpecialLinearGroup (Fin 3) F => A 0 0) h
  have hn : (-1 : F) = 1 := hh
  apply h2
  linear_combination -hn

/-- The determinant-corrected block matrix attached to an invertible two-by-two matrix. -/
@[expose] def blockMatrix (A : GL (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, ↑((GeneralLinearGroup.det A)⁻¹)]

theorem blockMatrix_det (A : GL (Fin 2) F) : (blockMatrix F A).det = 1 := by
  have hd : (A 0 0 * A 1 1 - A 0 1 * A 1 0) *
      (↑((GeneralLinearGroup.det A)⁻¹) : F) = 1 := by
    simpa [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using
      (Units.val_mul (GeneralLinearGroup.det A) (GeneralLinearGroup.det A)⁻¹).symm
  simp only [Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply] at hd
  simp [blockMatrix, Matrix.det_fin_three]
  linear_combination hd

/-- Embed GL₂ in SL₃ by correcting the last diagonal entry with the inverse determinant. -/
@[expose] def blockEmbedding : GL (Fin 2) F →* SpecialLinearGroup (Fin 3) F where
  toFun A := (⟨blockMatrix F A, blockMatrix_det F A⟩ : SpecialLinearGroup (Fin 3) F)
  map_one' := by
    apply Subtype.ext
    change blockMatrix F 1 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMatrix]
  map_mul' A B := by
    apply Subtype.ext
    change blockMatrix F (A * B) = blockMatrix F A * blockMatrix F B
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMatrix, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, mul_comm]

theorem blockEmbedding_injective : Function.Injective (blockEmbedding F) := by
  intro A B h
  apply GeneralLinearGroup.ext
  intro i j
  have hh := congrArg (fun x : SpecialLinearGroup (Fin 3) F => x.val) h
  change blockMatrix F A = blockMatrix F B at hh
  fin_cases i <;> fin_cases j
  · exact congrArg (fun M => M 0 0) hh
  · exact congrArg (fun M => M 0 1) hh
  · exact congrArg (fun M => M 1 0) hh
  · exact congrArg (fun M => M 1 1) hh

theorem mem_standardInvolution_centralizer_iff (h2 : (2 : F) ≠ 0)
    (A : SpecialLinearGroup (Fin 3) F) :
    A ∈ Subgroup.centralizer ({standardInvolution F} : Set (SpecialLinearGroup (Fin 3) F)) ↔
      A 0 2 = 0 ∧ A 1 2 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm := congrArg (fun B : SpecialLinearGroup (Fin 3) F => B.val) h
    change A.val * (standardInvolution F).val = (standardInvolution F).val * A.val at hm
    have he (i j : Fin 3) := congrArg (fun B : Matrix (Fin 3) (Fin 3) F => B i j) hm
    have h02 := he 0 2
    have h12 := he 1 2
    have h20 := he 2 0
    have h21 := he 2 1
    simp [standardInvolution, Matrix.mul_apply,
      Fin.sum_univ_three] at h02 h12 h20 h21
    have hz (x : F) (hx : 2 * x = 0) : x = 0 := (mul_eq_zero.mp hx).resolve_left h2
    exact ⟨hz _ (by linear_combination h02), hz _ (by linear_combination h12),
      hz _ (by linear_combination -h20), hz _ (by linear_combination -h21)⟩
  · rintro ⟨h02, h12, h20, h21⟩
    apply Subtype.ext
    change A.val * (standardInvolution F).val = (standardInvolution F).val * A.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [standardInvolution, Matrix.mul_apply, Fin.sum_univ_three,
        show A.val 0 2 = 0 from h02, show A.val 1 2 = 0 from h12,
        show A.val 2 0 = 0 from h20, show A.val 2 1 = 0 from h21]

theorem blockEmbedding_range (h2 : (2 : F) ≠ 0) :
    (blockEmbedding F).range =
      Subgroup.centralizer ({standardInvolution F} : Set (SpecialLinearGroup (Fin 3) F)) := by
  ext A
  rw [mem_standardInvolution_centralizer_iff F h2]
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h02, h12, h20, h21⟩
    let M : Matrix (Fin 2) (Fin 2) F := !![A 0 0, A 0 1; A 1 0, A 1 1]
    have hd : M.det * A 2 2 = 1 := by
      have hdet := A.property
      change A.val.det = 1 at hdet
      simp only [Matrix.det_fin_three] at hdet
      change A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 -
        A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0 +
        A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 = 1 at hdet
      simp only [h02, h12, h20, h21, mul_zero, zero_mul, sub_zero, add_zero] at hdet
      simpa [M, Matrix.det_fin_two, sub_mul] using hdet
    have hd0 : M.det ≠ 0 := by
      intro h
      rw [h, zero_mul] at hd
      exact zero_ne_one hd
    let B : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero M hd0
    have hlast : A 2 2 = M.det⁻¹ := by
      apply mul_left_cancel₀ hd0
      rw [hd, mul_inv_cancel₀ hd0]
    refine ⟨B, ?_⟩
    apply SpecialLinearGroup.ext
    intro i j
    change blockMatrix F B i j = A.val i j
    fin_cases i <;> fin_cases j <;>
      simp [blockMatrix, B, M, h02, h12, h20, h21, hlast]

/-- The explicit block embedding identifies GL₂ with the full involution centralizer. -/
noncomputable def standardInvolutionCentralizerEquiv (h2 : (2 : F) ≠ 0) :
    GL (Fin 2) F ≃*
      Subgroup.centralizer ({standardInvolution F} : Set (SpecialLinearGroup (Fin 3) F)) :=
  (MonoidHom.ofInjective (blockEmbedding_injective F)).trans
    (MulEquiv.subgroupCongr (blockEmbedding_range F h2))

theorem standardInvolutionCentralizerEquiv_apply_val (h2 : (2 : F) ≠ 0)
    (A : GL (Fin 2) F) :
    (standardInvolutionCentralizerEquiv F h2 A).val = blockEmbedding F A := by rfl

end Matrix.SL3

end
