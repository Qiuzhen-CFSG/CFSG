module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Coordinates

/-!
# Safe first-row equality certificates in the source max2 subgroup

The existing kernel-word row recurrence and recovery certificates separate
first rows of all 8192 words. Under the allowed local order bound those words
exhaust the quotient kernel. Equal first rows therefore imply equality for
kernel elements. For arbitrary source elements, equality of the quotient
images puts their difference in that kernel; right multiplying the equal rows
then proves the complete group equality.

This extension adapts the induction in LowerBound/KernelSeparation/FirstRow
without changing that shared module. Crucially, no first-row lookup is used
without proving equality of quotient images. The source is the unchanged
ATLAS J4G1-max2W1 program, with attribution under TwoCoreCentralizer/source/;
see also FiberCensus/source/README.md and Aschbacher--Smith,
refs/quasithin.pdf, printed pp.64--65, A.6.1--4.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.KernelRows
open Coordinates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation Janko4.GeneratorCertificates

section

private def code {n : ℕ} (v : Fin n → Bool) : Fin (2^n) :=
  finFunctionFinEquiv (fun i => if v i then (1 : Fin 2) else 0)

private lemma code_injective {n : ℕ} : Function.Injective (@code n) := by
  intro v w h
  have h' := finFunctionFinEquiv.injective h
  funext i
  have hi := congrFun h' i
  cases hv : v i <;> cases hw : w i <;> simp_all

private lemma code_succ {n : ℕ} (v : Fin (n+1) → Bool) :
    (code v).val = (code (fun i => v i.castSucc)).val +
      if v (Fin.last n) then 2^n else 0 := by
  simp only [code, finFunctionFinEquiv_apply, Fin.sum_univ_castSucc,
    Fin.val_castSucc, Fin.val_last]
  cases v (Fin.last n) <;> simp

private lemma bit_packedRow (x : ℕ) (ys : Vector ℕ 112) (j : Fin 112) :
    bit (packedRow x ys) j.val =
      ∑ k : Fin 112, bit x k.val * decodeRows ys k j := by
  rw [packedRow, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  simp only [decodeRows, bit]
  cases h : x.testBit k.val <;> simp [h]

private lemma binaryProduct_last {n : ℕ} (e : Fin (n+1) → BinaryMatrix)
    (v : Fin (n+1) → Bool) :
    binaryProduct e v = binaryProduct (fun i => e i.castSucc) (fun i => v i.castSucc) *
      (if v (Fin.last n) then e (Fin.last n) else 1) := by
  simp only [binaryProduct, List.ofFn_succ', List.prod_concat]

variable (row : ℕ → ℕ) (hzero : row 0 = 1)
  (hstep : ∀ (n : Fin 13) (m : Fin (2^n.val)),
    row (m.val + 2^n.val) = packedRow (row m.val) (factorRows n))

include hzero hstep in
private lemma first_row (n : ℕ) (hn : n ≤ 13) (v : Fin n → Bool) (j : Fin 112) :
    binaryProduct (fun i : Fin n => decodeRows (factorRows ⟨i.val, lt_of_lt_of_le i.isLt hn⟩)) v 0 j =
      bit (row (code v).val) j.val := by
  induction n generalizing j with
  | zero =>
    have hc : (code v).val = 0 := by simp [code]
    rw [hc, hzero]
    simpa only [binaryProduct, List.ofFn_zero, List.prod_nil, decodeRows,
      packedOne, get_ofFn, Fin.val_zero, pow_zero, bit] using
      (congrFun (congrFun decode_packedOne 0) j).symm
  | succ n ih =>
    rw [binaryProduct_last, code_succ]
    cases hb : v (Fin.last n)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, mul_one]
      exact ih (by omega) (fun i => v i.castSucc) j
    · simp only [↓reduceIte]
      rw [hstep ⟨n, by omega⟩ (code (fun i => v i.castSucc)), bit_packedRow,
        Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun t => t * decodeRows (factorRows ⟨n, by omega⟩) k j)
        (ih (by omega) (fun i => v i.castSucc) k)

private lemma row_eq_of_bits {x y : ℕ} (hx : x < 2^112) (hy : y < 2^112)
    (h : ∀ j : Fin 112, bit x j.val = bit y j.val) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 112
  · have h' := h ⟨j, hj⟩
    cases hx' : x.testBit j <;> cases hy' : y.testBit j <;> simp_all [bit]
  · have hp : 2^112 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hp)]

variable (recover : ℕ → ℕ)
  (hrecover : ∀ m : Fin 8192, recover (row m.val) = m.val)
  (hbound : ∀ m : Fin 8192, row m.val < 2^112)

include hzero hstep hrecover hbound in
private lemma matrixProduct_firstRow_injective :
    Function.Injective (fun v => matrixProduct v 0) := by
  intro v w h
  apply code_injective
  apply Fin.ext
  have hr : row (code v).val = row (code w).val := by
    apply row_eq_of_bits (hbound (code v)) (hbound (code w))
    intro j
    have hv := first_row row hzero hstep 13 (by omega) v j
    have hw := first_row row hzero hstep 13 (by omega) w j
    change matrixProduct v 0 j = _ at hv
    change matrixProduct w 0 j = _ at hw
    rw [← hv, ← hw]
    exact congrFun h j
  have hh := congrArg recover hr
  simpa only [hrecover] using hh



end

def sourceMatrix : sourceSubgroup →* BinaryMatrix := toMatrix.comp sourceSubgroup.subtype

def firstRow (u : sourceSubgroup) : Fin 112 → ZMod 2 := sourceMatrix u 0

theorem eval_kernelProduct (i : Fin 8192) :
    sourceMatrix (kernelProduct i) = matrixProduct (fun j => i.val.testBit j.val) := by
  rw [kernelProduct, map_list_prod, List.map_ofFn]
  unfold matrixProduct binaryProduct
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  change sourceMatrix (if i.val.testBit j.val then kernelFactor j else 1) = _
  split_ifs
  · exact eval_factor j
  · exact sourceMatrix.map_one

/-- The checked row recurrence separates the actual source words. -/
theorem firstRow_kernelProduct_injective :
    Function.Injective (fun i => firstRow (kernelProduct i)) := by
  have hm := matrixProduct_firstRow_injective KernelSeparation.row row_zero row_step recover
    (fun m => (recover_bound m).1) (fun m => (recover_bound m).2)
  intro i j hij
  have hbits := hm (by simpa only [firstRow, eval_kernelProduct] using hij)
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 13
  · exact congrFun hbits ⟨k, hk⟩
  · have hp : 2^13 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le j.isLt hp)]

private theorem code_bits (i : Fin 8192) :
    code (fun j : Fin 13 => i.val.testBit j.val) = i := by
  change finFunctionFinEquiv (fun j : Fin 13 =>
    if i.val.testBit j.val then (1 : Fin 2) else 0) = i
  apply finFunctionFinEquiv.symm.injective
  rw [finFunctionFinEquiv.symm_apply_apply]
  funext j
  apply Fin.ext
  change (if i.val.testBit j.val then (1 : Fin 2) else 0).val =
    i.val / 2^j.val % 2
  rw [← Nat.toNat_testBit]
  cases i.val.testBit j.val <;> rfl

/-- The published packed row table is the first row of the literal word. -/
theorem firstRow_kernelProduct (i : Fin 8192) (j : Fin 112) :
    firstRow (kernelProduct i) j = bit (KernelSeparation.row i.val) j.val := by
  unfold firstRow
  rw [eval_kernelProduct]
  have he := first_row KernelSeparation.row row_zero row_step 13 (by omega)
    (fun k : Fin 13 => i.val.testBit k.val) j
  rw [code_bits] at he
  exact he

attribute [local irreducible] kernelProduct

/-- First rows determine elements only after membership in this kernel is known. -/
theorem kernel_eq_of_firstRow (hH : Nat.card H ≤ 21799895040)
    (u v : sourceSubgroup) (hu : u ∈ quotientMap.ker) (hv : v ∈ quotientMap.ker)
    (he : firstRow u = firstRow v) : u = v := by
  obtain ⟨i, hi⟩ := (kernelElement_bijective hH).surjective ⟨u, hu⟩
  obtain ⟨j, hj⟩ := (kernelElement_bijective hH).surjective ⟨v, hv⟩
  have hi' : kernelProduct i = u := congrArg Subtype.val hi
  have hj' : kernelProduct j = v := congrArg Subtype.val hj
  have he' : firstRow (kernelProduct i) = firstRow (kernelProduct j) :=
    (congrArg firstRow hi').trans (he.trans (congrArg firstRow hj').symm)
  have hij : i = j := firstRow_kernelProduct_injective he'
  exact hi'.symm.trans ((congrArg kernelProduct hij).trans hj')

/-- Equality of the quotient image and first row certifies full source equality.
This is the safe interface for the orbit forest's conjugation edges. -/
theorem eq_of_quotient_eq_of_firstRow (hH : Nat.card H ≤ 21799895040)
    (u v : sourceSubgroup) (hq : quotientMap u = quotientMap v)
    (hr : firstRow u = firstRow v) : u = v := by
  have hk : u * v⁻¹ ∈ quotientMap.ker := by
    change quotientMap (u * v⁻¹) = 1
    rw [map_mul, map_inv, hq, mul_inv_cancel]
  have he : firstRow (u * v⁻¹) = firstRow (1 : sourceSubgroup) := by
    funext j
    change sourceMatrix (u * v⁻¹) 0 j = sourceMatrix 1 0 j
    rw [map_mul, Matrix.mul_apply]
    calc
      ∑ k : Fin 112, sourceMatrix u 0 k * sourceMatrix v⁻¹ k j =
          ∑ k : Fin 112, sourceMatrix v 0 k * sourceMatrix v⁻¹ k j := by
        apply Finset.sum_congr rfl
        intro k _
        exact congrArg (fun a => a * sourceMatrix v⁻¹ k j) (congrFun hr k)
      _ = sourceMatrix 1 0 j := by
        rw [← Matrix.mul_apply, ← map_mul, mul_inv_cancel]
  exact mul_inv_eq_one.mp (kernel_eq_of_firstRow hH _ _ hk (Subgroup.one_mem _) he)

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.KernelRows
