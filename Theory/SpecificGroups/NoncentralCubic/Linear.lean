module

public import Theory.GroupTheory.NoncentralElements
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FinCases

/-!
# Noncentral cubic elements in classical groups in characteristic two

The matrix `!![0,1;1,1]` has order three and does not commute with the upper
transvection. Extending by an identity block embeds this pair in SLₙ. When
there is an extra coordinate, its diagonal entry forces any scalar in the
embedded subgroup to be one, so the embedding survives passage to PSLₙ.
In degree two, characteristic two itself makes the scalar center trivial.
The block `diag(A,(A⁻¹)ᵀ)` gives the same pair in Sp₄.

No finiteness, order formula, simplicity, or representation certification is
needed. Source application: Aschbacher–Smith, B.5.6, printed p.105, and the
perfect-component argument in 15.3.49(i), printed pp.1143–1144.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.NoncentralCubic

variable (F : Type*) [Field F] [CharP F 2]

private theorem sl2 : ∃ x : SL(2,F), orderOf x = 3 ∧ x ∉ center SL(2,F) := by
  let x : SL(2,F) := ⟨!![0,1;1,1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
  let y : SL(2,F) := ⟨!![1,1;0,1], by simp [Matrix.det_fin_two]⟩
  have hp : x ^ 3 = 1 := by
    apply Subtype.ext
    change ((!![0,1;1,1] : Matrix (Fin 2) (Fin 2) F) ^ 3) = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hn : x ∉ center SL(2,F) := by
    intro hc
    have he := congrArg (fun a : SL(2,F) => a.val 0 0) (mem_center_iff.mp hc y)
    change (y.val * x.val) 0 0 = (x.val * y.val) 0 0 at he
    simp [x, y, Matrix.mul_apply, Fin.sum_univ_two] at he
  refine ⟨x, orderOf_eq_prime hp (fun h => hn (h ▸ (center _).one_mem)), hn⟩

omit [CharP F 2] in
private def extend (k : ℕ) : SL(2,F) →* SpecialLinearGroup (Fin 2 ⊕ Fin k) F where
  toFun A := ⟨Matrix.fromBlocks A.val 0 0 1, by simp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' A B := by
    apply Subtype.ext
    change Matrix.fromBlocks (A.val * B.val) 0 0 (1 : Matrix (Fin k) (Fin k) F) =
      Matrix.fromBlocks A.val 0 0 1 * Matrix.fromBlocks B.val 0 0 1
    simp [Matrix.fromBlocks_multiply]

omit [CharP F 2] in
private def reindex (k : ℕ) : SpecialLinearGroup (Fin 2 ⊕ Fin k) F →* SL(2+k,F) where
  toFun A := ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv A.val, by
    rw [Matrix.det_reindex_self]; exact A.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Matrix.reindexRingEquiv F finSumFinEquiv)
  map_mul' A B := by
    apply Subtype.ext
    exact map_mul (Matrix.reindexRingEquiv F finSumFinEquiv) A.val B.val

omit [CharP F 2] in
private theorem injective (k : ℕ) : Function.Injective ((reindex F k).comp (extend F k)) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have he := congrArg (fun C : SL(2+k,F) =>
    C.val (finSumFinEquiv (Sum.inl i : Fin 2 ⊕ Fin k))
      (finSumFinEquiv (Sum.inl j : Fin 2 ⊕ Fin k))) h
  change Matrix.fromBlocks A.val 0 0 (1 : Matrix (Fin k) (Fin k) F)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) =
    Matrix.fromBlocks B.val 0 0 (1 : Matrix (Fin k) (Fin k) F)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) at he
  simpa only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁] using he

omit [CharP F 2] in
private theorem projective_injective (k : ℕ) (hk : 0 < k) :
    Function.Injective ((QuotientGroup.mk' (center SL(2+k,F))).comp
      ((reindex F k).comp (extend F k))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have hc : ((reindex F k).comp (extend F k)) A ∈ center SL(2+k,F) :=
    (QuotientGroup.eq_one_iff _).mp hA
  obtain ⟨a, _, ha⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  let i : Fin (2+k) := finSumFinEquiv (Sum.inr (⟨0,hk⟩ : Fin k))
  have hdiag := congrArg (fun M : Matrix (Fin (2+k)) (Fin (2+k)) F => M i i) ha
  have ha1 : a = 1 := by
    change (Matrix.scalar _ a) i i =
      Matrix.fromBlocks A.val 0 0 (1 : Matrix (Fin k) (Fin k) F)
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr ⟨0,hk⟩)))
        (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr ⟨0,hk⟩))) at hdiag
    simpa only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using hdiag
  apply (injective F k)
  rw [map_one]
  apply Subtype.ext
  simpa [ha1] using ha.symm

private theorem sl (k : ℕ) : ∃ x : SL(2+k,F), orderOf x = 3 ∧ x ∉ center SL(2+k,F) :=
  Theory.GroupTheory.exists_noncentral_orderOf_of_injective _ (injective F k) (sl2 F)

private theorem psl (k : ℕ) (hk : 0 < k) :
    ∃ x : PSL(2+k,F), orderOf x = 3 ∧ x ∉ center PSL(2+k,F) :=
  Theory.GroupTheory.exists_noncentral_orderOf_of_injective _ (projective_injective F k hk) (sl2 F)

private theorem psl2 : ∃ x : PSL(2,F), orderOf x = 3 ∧ x ∉ center PSL(2,F) := by
  apply Theory.GroupTheory.exists_noncentral_orderOf_of_injective (QuotientGroup.mk' _) _ (sl2 F)
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', eq_bot_iff]
  intro A hA
  obtain ⟨a, ha, he⟩ := SpecialLinearGroup.mem_center_iff.mp hA
  have ha1 : a = 1 := by
    rcases sq_eq_one_iff.mp (show a^2 = 1 by simpa using ha) with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  apply Subtype.ext
  simpa [ha1] using he.symm

omit [CharP F 2] in
private def symplecticEmbedding : SL(2,F) →* symplecticGroup (Fin 2) F where
  toFun A := ⟨fromBlocks A.val 0 0 (A⁻¹).valᵀ, by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    simp only [mul_zero, transpose_zero, zero_mul, transpose_transpose,
      sub_zero, true_and]
    rw [← transpose_mul]
    have h : (A⁻¹).val * A.val = 1 := congrArg Subtype.val (inv_mul_cancel A)
    rw [h, transpose_one]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' A B := by
    apply Subtype.ext
    simp only [_root_.mul_inv_rev, SpecialLinearGroup.coe_mul]
    change fromBlocks (A.val * B.val) 0 0 ((B⁻¹).val * (A⁻¹).val)ᵀ =
      fromBlocks A.val 0 0 (A⁻¹).valᵀ * fromBlocks B.val 0 0 (B⁻¹).valᵀ
    simp [Matrix.fromBlocks_multiply, Matrix.transpose_mul]

omit [CharP F 2] in
private theorem symplecticEmbedding_injective : Function.Injective (symplecticEmbedding F) := by
  intro A B h
  apply Subtype.ext
  exact congrArg (fun C : symplecticGroup (Fin 2) F => C.val.toBlocks₁₁) h

/-- The determinant-one plane embeds as a symplectic block and its dual. -/
theorem exists_noncentral_cubic_symplecticFour : ∃ x : symplecticGroup (Fin 2) F,
    orderOf x = 3 ∧ x ∉ center (symplecticGroup (Fin 2) F) :=
  Theory.GroupTheory.exists_noncentral_orderOf_of_injective _ (symplecticEmbedding_injective F) (sl2 F)

/-- Every special linear group of degree at least two in characteristic two
contains a noncentral element of order three. -/
theorem exists_noncentral_cubic_specialLinear {n : ℕ} (hn : 2 ≤ n) :
    ∃ x : SL(n,F), orderOf x = 3 ∧ x ∉ center SL(n,F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact sl F k

/-- The same element survives the actual scalar-center quotient. The degree-two
case uses the trivial center in characteristic two; larger degrees use the
identity coordinate outside the embedded plane. -/
theorem exists_noncentral_cubic_projectiveSpecialLinear {n : ℕ} (hn : 2 ≤ n) :
    ∃ x : PSL(n,F), orderOf x = 3 ∧ x ∉ center PSL(n,F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  cases k with
  | zero => exact psl2 F
  | succ k => exact psl F (k+1) (Nat.succ_pos k)

end Theory.SpecificGroups.NoncentralCubic
