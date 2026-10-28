module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.TestFormData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Table
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.Expansion

/-!
# Packed outer products and polarization

Spacing a binary coefficient vector into base `2^125` digits allows an ordinary
natural-number product to encode its outer product without carries. XOR sums
therefore compute all ordered pullback coefficients at once. Contraction by an
upper-triangle functional has the same semantics as the existing matrix product.
The row-segment comparison retains the diagonal once and polarizes only strict
upper entries. These arithmetic results contain no numerical assumptions.

Source convention and ATLAS attribution: `../../../source/README.md` and
`Janko4/Model/Data.lean`. The task-specific data are checked separately.
-/

@[expose] public section
open Janko4.GeneratorCertificates
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable

def spread (d : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, x => 2^d * spread d n (x >>> 1) + if x.testBit 0 then 1 else 0

theorem bit_spread_mul (d n x y a b : ℕ) (ha : a < n) (hb : b < d)
    (hy : y < 2^d) :
    bit (spread d n x * y) (d*a+b) = bit x a * bit y b := by
  induction n generalizing x a with
  | zero => omega
  | succ n ih =>
    rw [spread, Nat.add_mul, Nat.mul_assoc]
    have hlo : (if x.testBit 0 then 1 else 0) * y < 2^d := by
      split <;> simp_all
    simp only [bit, Nat.testBit_two_pow_mul_add _ hlo]
    cases a with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, hb, if_true]
      cases x.testBit 0 <;> simp
    | succ a =>
      have hn : a < n := by omega
      have hnlt : ¬d*(a+1)+b < d := by rw [Nat.mul_add, Nat.mul_one]; omega
      have hsub : d*(a+1)+b-d = d*a+b := by rw [Nat.mul_add, Nat.mul_one]; omega
      simp only [hnlt, if_false, hsub]
      have h := ih (x >>> 1) a hn
      simpa only [bit, Nat.testBit_shiftRight, Nat.add_comm 1] using h
/-- A binary outer product packed in base `2^125` rows. -/
def outer (x y : ℕ) : ℕ := spread 125 125 x * (y % 2^125)

theorem bit_outer (x y : ℕ) (a b : Fin 125) :
    bit (outer x y) (125*a.val+b.val) = bit x a.val * bit y b.val := by
  rw [outer, bit_spread_mul _ _ _ _ _ _ a.isLt b.isLt (Nat.mod_lt _ (by decide))]
  simp only [bit, Nat.testBit_mod_two_pow, b.isLt, decide_true, Bool.true_and]

def tensor (xs ys : Vector ℕ 50) : ℕ :=
  xorList (List.ofFn (fun k : Fin 50 => outer (xs.get k) (ys.get k)))

theorem bit_tensor (xs ys : Vector ℕ 50) (a b : Fin 125) :
    bit (tensor xs ys) (125*a.val+b.val) =
      ∑ k : Fin 50, bit (xs.get k) a.val * bit (ys.get k) b.val := by
  simp only [tensor, bit_xorList, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    bit_outer]

theorem bit_rowProduct {n : ℕ} (x : ℕ) (rows : Vector ℕ n) (j : ℕ) :
    bit (rowProduct x rows) j = ∑ k : Fin n, bit x k.val * bit (rows.get k) j := by
  rw [rowProduct, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  cases h : x.testBit k.val <;> simp [bit, h]

theorem get_map {α β : Type*} {n : ℕ} (f : α → β) (xs : Vector α n) (i : Fin n) :
    (xs.map f).get i = f (xs.get i) := Vector.getElem_map f i.isLt

/-- For each output column, the 50 entries pack coefficients of the basis matrices. -/
abbrev ColumnCoefficients := Vector (Vector ℕ 50) 50

def coefficientBasis (C : ColumnCoefficients) (a : Fin 125) : RestrictionMatrix :=
  fun i j => bit ((C.get j).get i) a.val

def formColumns (R : Vector ℕ 50) (C : ColumnCoefficients) : ColumnCoefficients :=
  C.map (rowsProduct R)

def rawTensor (C D : ColumnCoefficients) (u v : Fin 50) : ℕ :=
  tensor (C.get u) (D.get v)

theorem rawTensor_spec (R : Vector ℕ 50) (C : ColumnCoefficients)
    (u v : Fin 50) (a b : Fin 125) :
    bit (rawTensor C (formColumns R C) u v) (125*a.val+b.val) =
      ((coefficientBasis C a)ᵀ * decodeRestrictionRows R * coefficientBasis C b) u v := by
  rw [Matrix.mul_assoc]
  simp only [rawTensor, bit_tensor, formColumns, get_map, rowsProduct,
    get_ofFn, bit_rowProduct, Matrix.mul_apply, Matrix.transpose_apply,
    coefficientBasis, decodeRestrictionRows, Finset.mul_sum]

/-- XOR selection applies the upper-triangle functional to coefficient tensors. -/
def contract (w : ℕ) (T : ColumnCoefficients) : ℕ :=
  xorList (List.ofFn (fun u : Fin 50 => rowProduct (weightRow w u) (T.get u)))

theorem bit_contract (w : ℕ) (T : ColumnCoefficients) (j : ℕ) :
    bit (contract w T) j =
      ∑ u : Fin 50, ∑ v : Fin 50,
        (if u < v then bit w (upperSlot u v) else 0) * bit ((T.get u).get v) j := by
  simp only [contract, bit_xorList, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, bit_rowProduct, bit_weightRow]

def rawBlock (C D : ColumnCoefficients) (reverse : Bool) : ColumnCoefficients :=
  Vector.ofFn (fun u => Vector.ofFn (fun v => if u < v then
    if reverse then tensor (D.get v) (C.get u) else tensor (C.get u) (D.get v)
    else 0))

theorem contract_rawBlock (w : ℕ) (R : Vector ℕ 50) (C : ColumnCoefficients)
    (reverse : Bool) (a b : Fin 125) :
    bit (contract w (rawBlock C (formColumns R C) reverse)) (125*a.val+b.val) =
      if reverse then
        upperValue w ((coefficientBasis C b)ᵀ * decodeRestrictionRows R * coefficientBasis C a)
      else upperValue w ((coefficientBasis C a)ᵀ * decodeRestrictionRows R * coefficientBasis C b) := by
  rw [bit_contract]
  cases reverse with
  | false =>
    simp only [Bool.false_eq_true, if_false, upperValue]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u < v
    · simp only [huv, if_true, rawBlock, get_ofFn, Bool.false_eq_true, if_false]
      apply congrArg (fun z : ZMod 2 => bit w (upperSlot u v) * z)
      exact rawTensor_spec R C u v a b
    · simp [huv]
  | true =>
    simp only [if_true, upperValue]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u < v
    · simp only [huv, if_true, rawBlock, get_ofFn]
      apply congrArg (fun z : ZMod 2 => bit w (upperSlot u v) * z)
      rw [bit_tensor]
      simp_rw [mul_comm (bit _ a.val)]
      exact (bit_tensor (C.get u) ((formColumns R C).get v) b a).symm.trans
        (rawTensor_spec R C u v b a)
    · simp [huv]
/-- Compare whole upper row segments, retaining the diagonal only in `s`. -/
def RowCheck (p s t : ℕ) (a : Fin 125) : Prop :=
  (p >>> slot a a) % 2^(125-a.val) =
    ((s >>> (125*a.val+a.val)) ^^^ ((t >>> (125*a.val+a.val+1)) <<< 1)) %
      2^(125-a.val)

instance (p s t : ℕ) (a : Fin 125) : Decidable (RowCheck p s t a) :=
  inferInstanceAs (Decidable (_ = _))

theorem bit_mod (x n j : ℕ) (h : j < n) : bit (x % 2^n) j = bit x j := by
  simp only [bit, Nat.testBit_mod_two_pow, h, decide_true, Bool.true_and]

theorem rowCheck_spec (p s t : ℕ) (a b : Fin 125) (hab : a ≤ b)
    (h : RowCheck p s t a) :
    bit p (slot a b) = bit s (125*a.val+b.val) +
      if a = b then 0 else bit t (125*a.val+b.val) := by
  have hlen : b.val-a.val < 125-a.val := by omega
  have he := congrArg (fun z => bit z (b.val-a.val)) h
  change bit ((_ >>> _) % _) _ = bit ((_ ^^^ _) % _) _ at he
  rw [bit_mod _ _ _ hlen, bit_mod _ _ _ hlen, bit_xor] at he
  have hs : slot a a + (b.val-a.val) = slot a b := by
    simp only [slot, Nat.sub_self, Nat.add_zero]
  have hi : 125*a.val+a.val+(b.val-a.val) = 125*a.val+b.val := by omega
  simp only [bit, Nat.testBit_shiftRight, hs, hi] at he
  by_cases hab' : a = b
  · subst b
    simpa only [Nat.sub_self, Nat.testBit_shiftLeft, show ¬1 ≤ 0 by omega,
      decide_false, Bool.false_and, Bool.false_eq_true, if_false, if_true] using he
  · have hj : 1 ≤ b.val-a.val := by
      have hne : a.val ≠ b.val := fun e => hab' (Fin.ext e)
      omega
    have he' : 125*a.val+a.val+1+(b.val-a.val-1) = 125*a.val+b.val := by omega
    -- `t` is the packed transpose, so this row position is the reverse coefficient.
    simp only [Nat.testBit_shiftLeft, hj, decide_true, Bool.true_and,
      Nat.testBit_shiftRight, he'] at he
    simp only [hab', if_false]
    exact he

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable
