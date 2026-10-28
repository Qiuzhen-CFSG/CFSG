module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.IndependenceRows

/-!
# Independence from the first-row recurrence

This specialization of `KernelCount.Injectivity.FirstRow` uses the ten matrices
of the native linear-five subgroup. The recurrence and inverse table are
certified separately; equality of matrices forces equality of all ten choices.
-/

public section
open Janko4 Janko4.GeneratorCertificates
namespace Janko4.LocalStructure.LinearFive.NativeIndependence
open Janko4.Cardinality.KernelCount
@[expose] def matrixProduct (v : Fin 10 → Bool) : Janko4.BinaryMatrix :=
  binaryProduct (fun i => Janko4.decodeRows (generatorRows i)) v

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
  (hstep : ∀ (n : Fin 10) (m : Fin (2^n.val)),
    row (m.val + 2^n.val) = packedRow (row m.val) (generatorRows n))

include hzero hstep in
private lemma first_row (n : ℕ) (hn : n ≤ 10) (v : Fin n → Bool) (j : Fin 112) :
    binaryProduct (fun i : Fin n => decodeRows (generatorRows ⟨i.val, lt_of_lt_of_le i.isLt hn⟩)) v 0 j =
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
      exact congrArg (fun t => t * decodeRows (generatorRows ⟨n, by omega⟩) k j)
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
  (hrecover : ∀ m : Fin 1024, recover (row m.val) = m.val)
  (hbound : ∀ m : Fin 1024, row m.val < 2^112)

include hzero hstep hrecover hbound in
lemma matrixProduct_injective_of_certificate : Function.Injective matrixProduct := by
  intro v w h
  apply code_injective
  apply Fin.ext
  have hr : row (code v).val = row (code w).val := by
    apply row_eq_of_bits (hbound (code v)) (hbound (code w))
    intro j
    have hv := first_row row hzero hstep 10 (by omega) v j
    have hw := first_row row hzero hstep 10 (by omega) w j
    change matrixProduct v 0 j = _ at hv
    change matrixProduct w 0 j = _ at hw
    rw [← hv, ← hw, h]
  have hh := congrArg recover hr
  simpa only [hrecover] using hh

end Janko4.LocalStructure.LinearFive.NativeIndependence
