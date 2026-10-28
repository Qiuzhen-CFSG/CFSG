module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.GroupAction.AutomorphismFixedSubgroup
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Group

/-!
# Inverse-transpose fixed matrices in characteristic two

Conjugation by the determinant-one matrix with columns (1,1,0), (1,1,1),
(0,1,1) changes the identity Gram matrix to the antidiagonal form. A matrix
preserving that form has middle row and column (0,1,0), by the diagonal
form equations and injectivity of squaring. Its corner block is in SL₂.
The converse block embedding and change of basis give an actual group
isomorphism from the inverse-transpose fixed subgroup of SL₃ to SL₂.

This is the matrix calculation behind Aschbacher--Smith 15.3.38, combined
manuscript of 1 March 2004, printed pp.1136–1137. The block-shape argument
is adapted from `Theory.SpecificGroups.SU3.ProjectiveGraphFixed`; here the
form is bilinear over the original field, and the automorphism is the
specified inverse transpose from `PSL3.OuterSolvable.Actions`.
-/

open scoped Matrix
namespace Matrix.PSL3Four.GraphFixed
variable (K : Type*) [Field K] [CharP K 2]

private abbrev SL3 := SpecialLinearGroup (Fin 3) K
private abbrev SL2 := SpecialLinearGroup (Fin 2) K

omit [CharP K 2] in
/-- The inverse-transpose fixed matrices preserve the identity bilinear form. -/
public theorem mem_graphSL_fixed_iff (x : SpecialLinearGroup (Fin 3) K) :
    x ∈ (PSL3.OuterSolvable.graphSL K).fixedSubgroup ↔ x.val.transpose * x.val = 1 := by
  rw [MulAut.mem_fixedSubgroup]
  change (SpecialLinearGroup.transpose x)⁻¹ = x ↔ _
  constructor
  · intro h
    have he : SpecialLinearGroup.transpose x * x = 1 := by
      calc
        _ = SpecialLinearGroup.transpose x * (SpecialLinearGroup.transpose x)⁻¹ :=
          congrArg (fun y => SpecialLinearGroup.transpose x * y) h.symm
        _ = 1 := mul_inv_cancel _
    exact congrArg Subtype.val he
  · intro h
    have he : SpecialLinearGroup.transpose x * x = 1 := Subtype.ext h
    exact (eq_inv_of_mul_eq_one_right he).symm

private def basis : SL3 K :=
  ⟨!![1, 1, 0; 1, 1, 1; 0, 1, 1], by
    simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

private def form : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private theorem basis_gram : (basis K).val.transpose * (basis K).val = form K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basis, form, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private def block (A : SL2 K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, 0, A 0 1; 0, 1, 0; A 1 0, 0, A 1 1]

omit [CharP K 2] in
private theorem block_det (A : SL2 K) : (block K A).det = 1 := by
  have hd := A.property
  rw [Matrix.det_fin_two] at hd
  simpa [block, Matrix.det_fin_three] using hd

private def blockHom : SL2 K →* SL3 K where
  toFun A := ⟨block K A, block_det K A⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [block]
  map_mul' A B := by
    apply Subtype.ext
    change block K (A * B) = block K A * block K B
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [block, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        Fin.sum_univ_three]

private theorem block_preserves (A : SL2 K) :
    (block K A).transpose * form K * block K A = form K := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    exact (Matrix.det_fin_two A.val).symm.trans A.property
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, form, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [mul_comm, CharTwo.add_self_eq_zero]
  · simpa [CharTwo.sub_eq_add, mul_comm, add_comm] using hd
  · simpa [CharTwo.sub_eq_add, mul_comm, add_comm] using hd
  · rw [mul_comm, CharTwo.add_self_eq_zero]

private theorem preserves_iff (A : SL3 K) :
    A.val.transpose * form K * A.val = form K ↔
      MulAut.conj (basis K) A ∈ (PSL3.OuterSolvable.graphSL K).fixedSubgroup := by
  rw [mem_graphSL_fixed_iff]
  let X := MulAut.conj (basis K) A
  have hpa : (basis K).val * A.val = X.val * (basis K).val := by
    have h : basis K * A = X * basis K := by dsimp [X]; group
    exact congrArg Subtype.val h
  have he : A.val.transpose * form K * A.val =
      (basis K).val.transpose * (X.val.transpose * X.val) * (basis K).val := by
    calc
      _ = ((basis K).val * A.val).transpose * ((basis K).val * A.val) := by
        rw [Matrix.transpose_mul, ← basis_gram]
        simp only [mul_assoc]
      _ = (X.val * (basis K).val).transpose * (X.val * (basis K).val) := by rw [hpa]
      _ = _ := by rw [Matrix.transpose_mul]; simp only [mul_assoc]
  constructor
  · intro h
    have he' : (basis K).val.transpose * (X.val.transpose * X.val) * (basis K).val =
        (basis K).val.transpose * (1 : Matrix (Fin 3) (Fin 3) K) * (basis K).val := by
      rw [← he, h, mul_one, basis_gram]
    have hcancel := congrArg
      (fun M => ((basis K)⁻¹).val.transpose * M * ((basis K)⁻¹).val) he'
    have hinv : (basis K).val * ((basis K)⁻¹).val = 1 :=
      congrArg Subtype.val (mul_inv_cancel (basis K))
    have htinv : ((basis K)⁻¹).val.transpose * (basis K).val.transpose = 1 := by
      rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
    have hcancel' :
        (((basis K)⁻¹).val.transpose * (basis K).val.transpose) *
            (X.val.transpose * X.val) * ((basis K).val * ((basis K)⁻¹).val) =
          (((basis K)⁻¹).val.transpose * (basis K).val.transpose) *
            (1 : Matrix (Fin 3) (Fin 3) K) * ((basis K).val * ((basis K)⁻¹).val) := by
      simpa only [mul_assoc] using hcancel
    simpa only [htinv, hinv, one_mul, mul_one] using hcancel'
  · intro h
    change X.val.transpose * X.val = 1 at h
    rw [he, h, mul_one, basis_gram]

private theorem preserved_shape (A : SL3 K)
    (hp : A.val.transpose * form K * A.val = form K) :
    A.val = !![A 0 0, 0, A 0 2; 0, 1, 0; A 2 0, 0, A 2 2] := by
  have hh (i j : Fin 3) : A 2 i * A 0 j + A 1 i * A 1 j + A 0 i * A 2 j = form K i j := by
    simpa [form, Matrix.mul_apply, Fin.sum_univ_three]
      using congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j) hp
  have hh00 := hh 0 0
  have hh11 := hh 1 1
  have hh22 := hh 2 2
  change A 2 0 * A 0 0 + A 1 0 * A 1 0 + A 0 0 * A 2 0 = 0 at hh00
  change A 2 1 * A 0 1 + A 1 1 * A 1 1 + A 0 1 * A 2 1 = 1 at hh11
  change A 2 2 * A 0 2 + A 1 2 * A 1 2 + A 0 2 * A 2 2 = 0 at hh22
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h10 : A 1 0 = 0 := by
    apply (pow_eq_zero_iff two_ne_zero).mp
    linear_combination hh00 - (A 0 0 * A 2 0) * h2
  have h11 : A 1 1 = 1 := by
    apply CharTwo.sq_inj.mp
    linear_combination hh11 - (A 0 1 * A 2 1) * h2
  have h12 : A 1 2 = 0 := by
    apply (pow_eq_zero_iff two_ne_zero).mp
    linear_combination hh22 - (A 0 2 * A 2 2) * h2
  have hd : A 0 0 * A 2 2 - A 0 2 * A 2 0 = 1 := by
    have hd := A.property
    rw [Matrix.det_fin_three] at hd
    simpa [h10, h11, h12] using hd
  have he0 : A 2 0 * A 0 1 + A 0 0 * A 2 1 = 0 := by
    simpa [h10, form] using hh 0 1
  have he2 : A 2 2 * A 0 1 + A 0 2 * A 2 1 = 0 := by
    simpa [h12, form] using hh 2 1
  have h01 : A 0 1 = 0 := by
    linear_combination A 0 0 * he2 - A 0 2 * he0 - A 0 1 * hd
  have h21 : A 2 1 = 0 := by
    linear_combination A 2 2 * he0 - A 2 0 * he2 - A 2 1 * hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h11, h12, h01, h21]

private def blockFixed : SL2 K →* (PSL3.OuterSolvable.graphSL K).fixedSubgroup :=
  ((MulAut.conj (basis K)).toMonoidHom.comp (blockHom K)).codRestrict _ (fun A =>
    (preserves_iff K (blockHom K A)).mp (block_preserves K A))

private theorem blockFixed_injective : Function.Injective (blockFixed K) := by
  intro A B h
  have he : blockHom K A = blockHom K B :=
    (MulAut.conj (basis K)).injective (congrArg Subtype.val h)
  have hm : block K A = block K B := congrArg Subtype.val he
  apply SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hm
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hm
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 0) hm
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hm

private theorem blockFixed_surjective : Function.Surjective (blockFixed K) := by
  intro x
  let A := (MulAut.conj (basis K)).symm x.val
  have hA : MulAut.conj (basis K) A = x.val := (MulAut.conj (basis K)).apply_symm_apply _
  have hp : A.val.transpose * form K * A.val = form K :=
    (preserves_iff K A).mpr (hA ▸ x.property)
  let M : Matrix (Fin 2) (Fin 2) K := !![A 0 0, A 0 2; A 2 0, A 2 2]
  have hd : M.det = 1 := by
    have hd := A.property
    rw [preserved_shape K A hp] at hd
    simpa [M, Matrix.det_fin_two, Matrix.det_fin_three] using hd
  refine ⟨⟨M, hd⟩, ?_⟩
  apply Subtype.ext
  change MulAut.conj (basis K) (blockHom K ⟨M, hd⟩) = x.val
  rw [← hA]
  congr 1
  apply Subtype.ext
  exact (preserved_shape K A hp).symm

/-- In characteristic two, the inverse-transpose fixed SL₃ is the actual SL₂. -/
public noncomputable def graphSLFixedEquivSL2 :
    (PSL3.OuterSolvable.graphSL K).fixedSubgroup ≃* SpecialLinearGroup (Fin 2) K :=
  (MulEquiv.ofBijective (blockFixed K)
    ⟨blockFixed_injective K, blockFixed_surjective K⟩).symm

end Matrix.PSL3Four.GraphFixed
