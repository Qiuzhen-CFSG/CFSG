module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Arithmetic

/-!
Scalar, vector, transpose and trace checks for the two-bit-plane F₄ encoding.
The scalar table is the already proved ATLAS code table: 0,1,t,t+1. These
checks support the rank-one orbit certificate and its distinguishing trace.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed
open SmallModels.Arithmetic

def codeAt (a : Row) (j : ℕ) : Fin 4 :=
  if a.2.testBit j then (if a.1.testBit j then 3 else 2)
  else (if a.1.testBit j then 1 else 0)
def scaleRow (c : Fin 4) (a : Row) : Row :=
  if c = 0 then (0, 0) else if c = 1 then a else
    if c = 2 then timesT a else addRow a (timesT a)
def checkAdd (n : ℕ) (a b c : Mat) : Bool :=
  (List.range n).all fun i => addRow a[i]! b[i]! == c[i]!
def checkScale (n : ℕ) (c : Fin 4) (a b : Mat) : Bool :=
  (List.range n).all fun i => scaleRow c a[i]! == b[i]!
def checkOne (n : ℕ) (a : Mat) : Bool :=
  (List.range n).all fun i => a[i]! == (2 ^ i, 0)
def checkOuter (n : ℕ) (v lam : Row) (a : Mat) : Bool :=
  (List.range n).all fun i => scaleRow (codeAt v i) lam == a[i]!
def checkTranspose (n : ℕ) (a b : Mat) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    codeAt a[i]! j == codeAt b[j]! i
def checkTrace (n : ℕ) (a : Mat) (c : Fin 4) : Bool :=
  codeSum (List.ofFn fun i : Fin n => codeAt a[i.val]! i.val) == c

variable {F : Type*} [Field F] [CharP F 2]

def evalVector (t : F) (n : ℕ) (a : Row) : Fin n → F := fun i => entry t a i.val

omit [CharP F 2] in
theorem coefficient_codeAt (t : F) (a : Row) (j : ℕ) :
    coefficient t (codeAt a j) = entry t a j := by
  cases h0 : a.1.testBit j <;> cases h1 : a.2.testBit j <;>
    simp [codeAt, coefficient, entry, bit, h0, h1, add_comm]

theorem entry_scaleRow (t : F) (ht : t ^ 2 = t + 1) (c : Fin 4) (a : Row) (j : ℕ) :
    entry t (scaleRow c a) j = coefficient t c * entry t a j := by
  fin_cases c <;> simp [scaleRow, entry_add, entry_timesT t ht, coefficient, add_mul, add_comm]

theorem eval_add (t : F) (n : ℕ) (a b c : Mat)
    (h : checkAdd n a b c = true) : eval t n a + eval t n b = eval t n c := by
  ext i j
  have hi : addRow a[i.val]! b[i.val]! = c[i.val]! :=
    eq_of_beq (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change entry t a[i.val]! j.val + entry t b[i.val]! j.val = _
  rw [← entry_add, hi]
  rfl

theorem eval_scale (t : F) (ht : t ^ 2 = t + 1) (n : ℕ) (c : Fin 4) (a b : Mat)
    (h : checkScale n c a b = true) : coefficient t c • eval t n a = eval t n b := by
  ext i j
  have hi : scaleRow c a[i.val]! = b[i.val]! :=
    eq_of_beq (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change coefficient t c * entry t a[i.val]! j.val = _
  rw [← entry_scaleRow t ht, hi]
  rfl

omit [CharP F 2] in
theorem eval_one (t : F) (n : ℕ) (a : Mat)
    (h : checkOne n a = true) : eval t n a = 1 := by
  ext i j
  have hi : a[i.val]! = (2 ^ i.val, 0) :=
    eq_of_beq (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change entry t a[i.val]! j.val = _
  rw [hi]
  simp [entry, bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

theorem eval_outer (t : F) (ht : t ^ 2 = t + 1) (n : ℕ) (v lam : Row) (a : Mat)
    (h : checkOuter n v lam a = true) :
    eval t n a = Matrix.vecMulVec (evalVector t n v) (evalVector t n lam) := by
  ext i j
  have hi : scaleRow (codeAt v i.val) lam = a[i.val]! :=
    eq_of_beq (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change entry t a[i.val]! j.val = entry t v i.val * entry t lam j.val
  rw [← hi, entry_scaleRow t ht, coefficient_codeAt]

omit [CharP F 2] in
theorem eval_transpose (t : F) (n : ℕ) (a b : Mat)
    (h : checkTranspose n a b = true) : (eval t n a).transpose = eval t n b := by
  ext i j
  have hij : codeAt a[j.val]! i.val = codeAt b[i.val]! j.val :=
    eq_of_beq (List.all_eq_true.mp (List.all_eq_true.mp h j.val
      (List.mem_range.mpr j.isLt)) i.val (List.mem_range.mpr i.isLt))
  exact (coefficient_codeAt t _ _).symm.trans
    ((congrArg (coefficient t) hij).trans (coefficient_codeAt t _ _))

theorem eval_trace (t : F) (n : ℕ) (a : Mat) (c : Fin 4)
    (h : checkTrace n a c = true) : (eval t n a).trace = coefficient t c := by
  have hc := congrArg (coefficient t) (eq_of_beq h)
  rw [coefficient_sum, List.map_ofFn, List.sum_ofFn] at hc
  simpa only [Function.comp_apply, coefficient_codeAt, Matrix.trace, Matrix.diag, eval] using hc

theorem eval_vecMul (t : F) (ht : t ^ 2 = t + 1) (n : ℕ) (v : Row) (a : Mat) (w : Row)
    (h : rowProduct v a n = w) :
    Matrix.vecMul (evalVector t n v) (eval t n a) = evalVector t n w := by
  funext j
  change (∑ k : Fin n, entry t v k.val * entry t a[k.val]! j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k => entry t v k * entry t a[k]! j.val),
    ← entry_rowProduct t ht, h]
  rfl

theorem eval_mulVec (t : F) (ht : t ^ 2 = t + 1) (n : ℕ) (a aT : Mat) (v w : Row)
    (ha : checkTranspose n a aT = true) (h : rowProduct v aT n = w) :
    (eval t n a).mulVec (evalVector t n v) = evalVector t n w := by
  have hv := eval_vecMul t ht n v aT w h
  rw [← eval_transpose t n a aT ha] at hv
  simpa only [Matrix.vecMul_transpose] using hv

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed
