module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.SourceCubic.ModelTable
public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.LiteralPairs

/-!
# The matrix-containing blocks of the literal E cubic

The actual source tensors for `u` and `v` have pair-matrix coefficients
four and minus four. Short-vector orthogonality then gives zero for equal
short axes and minus eight for distinct short axes on the same unordered
pair. The symmetric block is four times the triangle sum, by the trace
formula with the fixed coordinate marking. No vectors are rescaled.

Source: Aschbacher, *Sporadic Groups*, 27.8, 28.2, 28.7 and the calculation
in 29.11, printed pp. 150–152, 159–160. The all-short extraspecial product
calculation is separate.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
namespace Sporadic.Monster.Construction.NMonomial.EAction.SourceCubic
open LocalC ShortFamilies Griess TrialitySpin Atlas.Codes

theorem gamma_pair (x y : Fin 24) (A : SymmetricPart) :
    symmetricGamma (pairMatrix x y) A = 2 * A.val x y := by
  simp only [symmetricGamma, pairMatrix, Matrix.add_mul, Matrix.trace_add,
    Matrix.trace_single_mul, one_smul]
  rw [A.prop.apply y x]
  ring

theorem gamma_ru (x y u v : Omega) (hxy : x ≠ y) (huv : u ≠ v) :
    symmetricGamma (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))
      (shortLiftTensor sourceLatticeComparison (ru u v huv)) =
      if ({x,y} : Finset Omega) = {u,v} then 4 else 0 := by
  rw [ru_tensor, gamma_pair, rankOne_leechVector]
  simp only [Equiv.apply_symm_apply, uRepresentative_apply, Int.cast_add, Int.cast_ite,
    Int.cast_ofNat, Int.cast_zero]
  simp only [pair_eq_iff]
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    by_cases hyu : y = u <;> by_cases hyv : y = v <;> simp_all <;> norm_num

theorem gamma_rv (x y u v : Omega) (hxy : x ≠ y) (huv : u ≠ v) :
    symmetricGamma (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))
      (shortLiftTensor sourceLatticeComparison (rv u v huv)) =
      if ({x,y} : Finset Omega) = {u,v} then -4 else 0 := by
  rw [rv_tensor, gamma_pair, rankOne_leechVector]
  simp only [Equiv.apply_symm_apply, vRepresentative_apply, Int.cast_sub, Int.cast_ite,
    Int.cast_ofNat, Int.cast_zero]
  simp only [pair_eq_iff]
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    by_cases hyu : y = u <;> by_cases hyv : y = v <;> simp_all <;> norm_num
theorem srr_uu (x y u v p q : Omega) (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    sourceSRR sourceLatticeComparison
      (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))
      (ShortFamilies.u u v huv) (ShortFamilies.u p q hpq) =
      if ({x,y} : Finset Omega) = {u,v} ∧ ({u,v} : Finset Omega) = {p,q} then 4 else 0 := by
  rw [show ShortFamilies.u u v huv = shortVector sourceLatticeComparison (ru u v huv) from rfl,
    show ShortFamilies.u p q hpq = shortVector sourceLatticeComparison (ru p q hpq) from rfl,
    sourceSRR_vector, gamma_ru x y u v hxy huv]
  change (if ({x,y} : Finset Omega) = {u,v} then 4 else 0) *
    shortForm sourceLatticeComparison (ShortFamilies.u u v huv) (ShortFamilies.u p q hpq) = _
  rw [form_u_u_all]
  split_ifs <;> simp_all

theorem srr_vv (x y u v p q : Omega) (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    sourceSRR sourceLatticeComparison
      (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))
      (ShortFamilies.v u v huv) (ShortFamilies.v p q hpq) =
      if ({x,y} : Finset Omega) = {u,v} ∧ ({u,v} : Finset Omega) = {p,q} then -4 else 0 := by
  rw [show ShortFamilies.v u v huv = shortVector sourceLatticeComparison (rv u v huv) from rfl,
    show ShortFamilies.v p q hpq = shortVector sourceLatticeComparison (rv p q hpq) from rfl,
    sourceSRR_vector, gamma_rv x y u v hxy huv]
  change (if ({x,y} : Finset Omega) = {u,v} then -4 else 0) *
    shortForm sourceLatticeComparison (ShortFamilies.v u v huv) (ShortFamilies.v p q hpq) = _
  rw [form_v_v_all]
  split_ifs <;> simp_all

theorem srr_uv (A : SymmetricPart) (u v p q : Omega) (huv : u ≠ v) (hpq : p ≠ q) :
    sourceSRR sourceLatticeComparison A
      (ShortFamilies.u u v huv) (ShortFamilies.v p q hpq) = 0 := by
  change sourceSRR sourceLatticeComparison A
    (shortVector sourceLatticeComparison _) (shortVector sourceLatticeComparison _) = 0
  rw [sourceSRR_vector]
  change _ * shortForm sourceLatticeComparison (ShortFamilies.u u v huv)
    (ShortFamilies.v p q hpq) = 0
  rw [form_u_v_all, mul_zero]

theorem srr_vu (A : SymmetricPart) (u v p q : Omega) (huv : u ≠ v) (hpq : p ≠ q) :
    sourceSRR sourceLatticeComparison A
      (ShortFamilies.v u v huv) (ShortFamilies.u p q hpq) = 0 := by
  rw [sourceSRR_symmetric]
  exact srr_uv A p q u v hpq huv

theorem srr_plus_plus (x y u v p q : Omega) (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    sourceSRR sourceLatticeComparison
      (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))
      (wPlus u v huv) (wPlus p q hpq) = 0 := by
  simp only [wPlus, map_add, LinearMap.add_apply, srr_uv, srr_vu,
    srr_uu x y u v p q hxy huv hpq, srr_vv x y u v p q hxy huv hpq, add_zero, zero_add]
  split_ifs <;> norm_num

theorem srr_minus_minus (x y u v p q : Omega) (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    sourceSRR sourceLatticeComparison
      (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))
      (wMinus u v huv) (wMinus p q hpq) = 0 := by
  simp only [wMinus, map_sub, LinearMap.sub_apply, srr_uv, srr_vu,
    srr_uu x y u v p q hxy huv hpq, srr_vv x y u v p q hxy huv hpq, sub_zero, zero_sub]
  split_ifs <;> norm_num

theorem srr_plus_minus (x y u v p q : Omega) (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    sourceSRR sourceLatticeComparison
      (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))
      (wPlus u v huv) (wMinus p q hpq) =
      if ({x,y} : Finset Omega) = {u,v} ∧ ({u,v} : Finset Omega) = {p,q} then -8 else 0 := by
  simp only [wPlus, wMinus, map_add, map_sub, LinearMap.add_apply, srr_uv, srr_vu,
    srr_uu x y u v p q hxy huv hpq, srr_vv x y u v p q hxy huv hpq]
  split_ifs <;> norm_num

theorem griess_pairOne_pairTwo_pairThree (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    griessBeta (eInclusion (ePairOne x y hxy)) (eInclusion (ePairTwo u v huv))
      (eInclusion (ePairThree p q hpq)) =
      if ({x,y} : Finset Omega) = {u,v} ∧ ({u,v} : Finset Omega) = {p,q} then -8 else 0 := by
  rw [eInclusion_pairOne, eInclusion_pairTwo, eInclusion_pairThree]
  exact (sourceBeta_SRR sourceLatticeComparison _ _ _).trans
    (srr_plus_minus x y u v p q hxy huv hpq)

theorem symmetricBeta_trace (A B C : SymmetricPart) :
    symmetricBeta A B C = 4 * Matrix.trace (A.val * B.val * C.val) := by
  have h : Matrix.trace (B.val * A.val * C.val) = Matrix.trace (A.val * B.val * C.val) := by
    rw [← Matrix.trace_transpose (B.val * A.val * C.val), Matrix.transpose_mul,
      Matrix.transpose_mul, A.prop.eq, B.prop.eq, C.prop.eq, ← Matrix.mul_assoc]
    exact (Matrix.trace_mul_cycle A.val B.val C.val).symm
  simp only [symmetricBeta, symmetricGamma, symmetricProduct, Matrix.smul_mul,
    Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, h]
  ring

/-- The two literal unscaled short families, with `false` denoting axis one. -/
def shortPair (b : Bool) (x y : Omega) (hxy : x ≠ y) : ShortFamilies.Space :=
  if b then wMinus x y hxy else wPlus x y hxy

theorem srr_shortPair (b c : Bool) (x y u v p q : Omega)
    (hxy : x ≠ y) (huv : u ≠ v) (hpq : p ≠ q) :
    sourceSRR sourceLatticeComparison
      (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))
      (shortPair b u v huv) (shortPair c p q hpq) =
      if b ≠ c ∧ ({x,y} : Finset Omega) = {u,v} ∧
        ({u,v} : Finset Omega) = {p,q} then -8 else 0 := by
  cases b <;> cases c
  · simpa [shortPair] using srr_plus_plus x y u v p q hxy huv hpq
  · simpa [shortPair] using srr_plus_minus x y u v p q hxy huv hpq
  · rw [sourceSRR_symmetric]
    change sourceSRR sourceLatticeComparison _ (wPlus p q hpq) (wMinus u v huv) = _
    rw [srr_plus_minus x y p q u v hxy hpq huv]
    simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, true_and]
    congr 1
    exact propext (by constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨h₁.trans h₂, h₂.symm⟩)
  · simpa [shortPair] using srr_minus_minus x y u v p q hxy huv hpq

theorem marked_pair_entry (x y a b : Omega) :
    (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y)).val
      (coordinateMarking.symm a) (coordinateMarking.symm b) = edge x y a b := by
  simp [pairMatrix, edge, Matrix.single]

theorem symmetricPair_beta (x y u v p q : Omega) :
    symmetricBeta
      (pairMatrix (coordinateMarking.symm x) (coordinateMarking.symm y))
      (pairMatrix (coordinateMarking.symm u) (coordinateMarking.symm v))
      (pairMatrix (coordinateMarking.symm p) (coordinateMarking.symm q)) =
      4 * triangle x y u v p q := by
  rw [symmetricBeta_trace]
  congr 1
  rw [Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
  rw [← Equiv.sum_comp coordinateMarking.symm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp coordinateMarking.symm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Equiv.sum_comp coordinateMarking.symm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [marked_pair_entry, mul_assoc]

end Sporadic.Monster.Construction.NMonomial.EAction.SourceCubic
