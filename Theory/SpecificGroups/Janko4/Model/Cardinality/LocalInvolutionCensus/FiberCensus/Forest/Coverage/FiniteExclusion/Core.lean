module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.RowWords
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Blocks
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Lifts
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion.Factors

/-!
# Recurrence semantics for the inverse-word row table

The code records the selected inverse factors in their application order.
Induction on the last factor identifies a certified table with `rowWord`.
The natural-number scan is the packed XOR operation, proved independently
of the tables. Source: ATLAS J4G1-max2W1; see `Coverage/source/README.md`.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
open Janko4.GeneratorCertificates

def code {n : ℕ} (v : Fin n → Bool) : Fin (2^n) :=
  finFunctionFinEquiv (fun i => if v i then (1 : Fin 2) else 0)

lemma code_succ {n : ℕ} (v : Fin (n+1) → Bool) :
    (code v).val = (code (fun i => v i.castSucc)).val +
      if v (Fin.last n) then 2^n else 0 := by
  simp only [code, finFunctionFinEquiv_apply, Fin.sum_univ_castSucc,
    Fin.val_castSucc, Fin.val_last]
  cases v (Fin.last n) <;> simp

def reverseCode (m : Fin 8192) : Fin 8192 :=
  code (fun i : Fin 13 => m.val.testBit (12 - i.val))

lemma rowWord_append (as bs : List (Vector ℕ 112)) (r : ℕ) :
    rowWord (as ++ bs) r = rowWord bs (rowWord as r) := by
  induction as generalizing r with
  | nil => rfl
  | cons a as ih => exact ih (packedRow r a)

lemma table_word (t : ℕ → ℕ) (start : ℕ)
    (hzero : t 0 = start)
    (hstep : ∀ (n : Fin 13) (m : Fin (2^n.val)),
      t (m.val + 2^n.val) = packedRow (t m.val) (inverseFactorRows ⟨12-n.val, by omega⟩))
    (n : ℕ) (hn : n ≤ 13) (v : Fin n → Bool) :
    unpackRow (rowWord (List.ofFn (fun i : Fin n =>
      if v i then inverseFactorRows ⟨12-i.val, by omega⟩ else packedOne)) start) =
      unpackRow (t (code v).val) := by
  induction n with
  | zero =>
    have hc : (code v).val = 0 := by simp [code]
    simp only [List.ofFn_zero, rowWord, hc, hzero]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, rowWord_append, code_succ]
    simp only [rowWord, Fin.val_castSucc, Fin.val_last]
    rw [unpack_packedRow, ih (by omega) (fun i => v i.castSucc)]
    cases hb : v (Fin.last n)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
        decode_packedOne, Matrix.vecMul_one]
    · simp only [↓reduceIte]
      rw [hstep ⟨n, by omega⟩ (code (fun i => v i.castSucc)), unpack_packedRow]

lemma table_backward (t : ℕ → ℕ) (j : Fin 4)
    (hzero : t 0 = (liftRows j).get 0)
    (hstep : ∀ (n : Fin 13) (m : Fin (2^n.val)),
      t (m.val + 2^n.val) = packedRow (t m.val) (inverseFactorRows ⟨12-n.val, by omega⟩))
    (m : Fin 8192) : unpackRow (backwardRow j m) = unpackRow (t (reverseCode m).val) := by
  have hw : inverseFactors m = List.ofFn (fun i : Fin 13 =>
      if m.val.testBit (12-i.val) then inverseFactorRows ⟨12-i.val, by omega⟩ else packedOne) := by rfl
  unfold backwardRow
  rw [hw]
  exact table_word t _ hzero hstep 13 (by omega) _

noncomputable def scanRow (x : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | count + 1, offset =>
    (if x.testBit offset then f offset else 0) ^^^ scanRow x f count (offset + 1)

theorem scanRow_eq (x : ℕ) (f : ℕ → ℕ) (count offset : ℕ) :
    scanRow x f count offset = xorList (List.ofFn (fun i : Fin count =>
      if x.testBit (offset + i.val) then f (offset + i.val) else 0)) := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    rw [scanRow, List.ofFn_succ, xorList, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ,
      Nat.add_left_comm, Nat.add_comm]
    rfl

noncomputable def forwardAction (r : ℕ) (j : Fin 4) : ℕ :=
  scanRow r (liftEntry j) 112 0

noncomputable def backwardAction (r : ℕ) (n : Fin 13) : ℕ :=
  scanRow r (inverseEntry ⟨12-n.val, by omega⟩) 112 0

theorem forwardAction_eq (r : ℕ) (j : Fin 4) :
    forwardAction r j = packedRow r (liftRows j) := by
  simp only [forwardAction, scanRow_eq, Nat.zero_add, liftEntry_checked, packedRow]

theorem backwardAction_eq (r : ℕ) (n : Fin 13) :
    backwardAction r n = packedRow r (inverseFactorRows ⟨12-n.val, by omega⟩) := by
  simp only [backwardAction, scanRow_eq, Nat.zero_add, packedRow,
    inverseEntry_checked]

theorem unpackRow_inj {x y : ℕ} (hx : x < 2^112) (hy : y < 2^112)
    (h : unpackRow x = unpackRow y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 112
  · have h' := congrFun h ⟨j, hj⟩
    change bit x j = bit y j at h'
    cases hx' : x.testBit j <;> cases hy' : y.testBit j <;> simp_all [bit]
  · have hp : 2^112 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hp)]

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Coverage.FiniteExclusion
