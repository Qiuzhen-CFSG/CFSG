module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.Normalization
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison.Rules
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.SchreierCertificate
import Mathlib.Tactic.FinCases

/-!
# Literal Schreier inputs with central defects

Evaluate every Schreier symbol as its published word in arbitrary generators
`x,y`. The checked spanning-tree identities make omitted edges trivial; the
remaining edges telescope along the fixed table. Each relator loop therefore
evaluates to its original central defect. This is a word calculation in the
arbitrary group, with no assumed presentation map into that group.

The fixed table's loop checks and symbol dictionary are reused from the M₁
Schreier certificate. The four tail bits denote source relators 0, 4, 5, 6;
normalization makes relators 1, 2, 3 exact. The three protected-symbol equations
retain mask zero. Source: John Bray's ATLAS `HeG1-P1.M`, retained with its
attribution in `Held/Model/Source/`.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison
open FaithfulPresentation.M1Cosets
open Subgroup.CosetWordCertificate
variable {E : Type*} [Group E] {z x y : E}

def generators (x y : E) (i : Fin 2) : E := if i = 0 then x else y

theorem relator_eval (i : Fin 7) :
    eval (generators x y) (relatorWord i) = relationWord x y i := by
  fin_cases i <;>
    simp only [generators, relatorWord, eval_cons, eval_nil, relationWord,
      Bool.false_eq_true, if_false, if_true, pow_succ, pow_zero, one_mul, mul_one,
      mul_inv_rev, inv_inv, mul_assoc, Fin.isValue, Fin.reduceEq]

theorem defect_central (h : Normalized z x y) (i : Fin 7) :
    relationWord x y i ∈ Subgroup.center E := by
  rcases h.defects i with hi | hi
  · rw [hi]; exact Subgroup.one_mem _
  · rw [hi]; exact h.central

theorem defect_square (h : Normalized z x y) (i : Fin 7) :
    relationWord x y i ^ 2 = 1 := by
  rcases h.defects i with hi | hi
  · rw [hi, one_pow]
  · rw [hi]; exact h.square

def centralDefect (h : Normalized z x y) (i : Fin 7) : Subgroup.center E :=
  ⟨relationWord x y i, defect_central h i⟩
def maskBit (m : Mask) (i : Fin 4) : Nat := m.val / (2 ^ i.val) % 2

def tailCenter (h : Normalized z x y) (m : Mask) : Subgroup.center E :=
  centralDefect h 0 ^ maskBit m 0 * centralDefect h 4 ^ maskBit m 1 *
    centralDefect h 5 ^ maskBit m 2 * centralDefect h 6 ^ maskBit m 3

private theorem maskBit_xor : ∀ m n : Mask, ∀ i : Fin 4,
    maskBit (mxor m n) i = (maskBit m i + maskBit n i) % 2 := by decide +kernel

open scoped IsMulCommutative

theorem tailCenter_mul (h : Normalized z x y) (m n : Mask) :
    tailCenter h (mxor m n) = tailCenter h m * tailCenter h n := by
  have hp (j : Fin 7) (i : Fin 4) :
      centralDefect h j ^ maskBit (mxor m n) i =
        centralDefect h j ^ maskBit m i * centralDefect h j ^ maskBit n i := by
    rw [maskBit_xor, ← pow_eq_pow_mod _ (show centralDefect h j ^ 2 = 1 from
      Subtype.ext (defect_square h j)), pow_add]
  simp only [tailCenter, hp]
  ac_rfl

def tails (h : Normalized z x y) : Tails E where
  val m := (tailCenter h m : E)
  zero := by simp [tailCenter, maskBit]
  mul a b := congrArg Subtype.val (tailCenter_mul h a b)
  central m := (tailCenter h m).property
  square m := by
    have hx : mxor m m = 0 := by apply Fin.ext; simp [mxor]
    calc
      _ = (tailCenter h (mxor m m) : E) := (congrArg Subtype.val (tailCenter_mul h m m)).symm
      _ = 1 := by rw [hx]; simp [tailCenter, maskBit]

def symbolValue (x y : E) (n : Nat) : E := eval (generators x y) (Schreier.symbolWord n)
def representativeValue (x y : E) (i : Fin 2058) : E :=
  eval (generators x y) (Schreier.representativeWord i.val)

open Schreier

/-- A positive symbol is its literal Schreier element; tree edges evaluate to one. -/
theorem positiveWord_eval (i : Fin 2058) (a : Fin 2) :
    eval (symbolValue x y) (positiveWord i a) =
      (representativeValue x y i) * generators x y a * (representativeValue x y (destination i (a, true)))⁻¹ := by
  have hc := positiveCheck i a
  unfold PositiveCheck at hc
  unfold positiveWord
  dsimp only
  split <;> rename_i hn
  · rw [if_pos hn] at hc
    rw [eval_nil, eq_comm, mul_inv_eq_one]
    rcases hc with hf | hb
    · simp only [representativeValue, hf, eval_append, eval_letter, ↓reduceIte]
    · simp only [representativeValue, hb, eval_append, eval_letter, Bool.false_eq_true, ↓reduceIte]
      simp
  · rw [if_neg hn] at hc
    obtain ⟨hlo, hhi, he⟩ := hc
    rw [eval_letter]
    simp only [↓reduceIte]
    unfold symbolValue Schreier.symbolWord
    rw [if_neg hn, if_neg (by omega), if_pos hhi]
    simp only [he, eval_append, eval_invRev, eval_letter, ↓reduceIte]
    rfl

/-- Abstract interpretation of both signs of every table edge. -/
theorem edgeWord_eval (i : Fin 2058) (a : Letter (Fin 2)) :
    eval (symbolValue x y) (edgeWord i a) =
      (representativeValue x y i) * eval (generators x y : Fin 2 → E) [a] *
        (representativeValue x y (destination i a))⁻¹ := by
  rcases a with ⟨a, b⟩
  cases b
  · simp only [edgeWord, Bool.false_eq_true, ↓reduceIte, eval_invRev, positiveWord_eval,
      destination_reverse, eval_letter, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
  · simpa only [edgeWord, ↓reduceIte, eval_letter] using positiveWord_eval i a


/-- Schreier rewriting telescopes in the arbitrary target group. -/
theorem traceWord_eval (i : Fin 2058) (w : Word (Fin 2)) :
    eval (symbolValue x y) (traceWord i w) =
      (representativeValue x y i) * eval (generators x y : Fin 2 → E) w *
        (representativeValue x y (endpoint i w))⁻¹ := by
  induction w generalizing i with
  | nil => simp [traceWord, Schreier.endpoint]
  | cons a w ih =>
    rw [traceWord, eval_append, edgeWord_eval, ih, Schreier.endpoint,
      show eval (generators x y : Fin 2 → E) (a :: w) =
        eval (generators x y) [a] * eval (generators x y) w from eval_append _ [a] w]
    simp [mul_assoc]


def relatorMask : Fin 7 → Mask
  | 0 => 1
  | 4 => 2
  | 5 => 4
  | 6 => 8
  | _ => 0

def initialMask (i : Fin 14409) : Mask :=
  if i.val < 14406 then relatorMask (Fin.ofNat 7 i.val) else 0

theorem relator_tail (h : Normalized z x y) (i : Fin 7) :
    relationWord x y i = (tails h).val (relatorMask i) := by
  fin_cases i <;> simp [relatorMask, tails, tailCenter, maskBit, centralDefect]
  · exact h.seventh
  · exact h.seventeenth
  · exact h.long_commutator

theorem initialRelator_eval (h : Normalized z x y) (r : Fin 14409) :
    Theory.GroupTheory.CosetEnumeration.eval (symbolValue x y) (initialRelator r) =
      (tails h).val (initialMask r) := by
  rw [Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.eval_eq_free]
  unfold initialRelator initialMask
  split <;> rename_i hr
  · rw [eval_reduce, traceWord_eval, Schreier.relator_loop, relator_eval]
    rw [Subgroup.mem_center_iff.mp (defect_central h _) _, mul_assoc, mul_inv_cancel,
      mul_one, relator_tail h]
  · rw [(tails h).zero]
    have hroot : representativeValue x y 1205 = 1 := rfl
    have cases : r.val = 14406 ∨ r.val = 14407 ∨ r.val = 14408 := by omega
    rcases cases with h | h | h <;>
      simp only [h, eval_append, eval_reduce, traceWord_eval, Schreier.subgroup_loop,
        hroot, one_mul, inv_one, mul_one, eval_letter]
    all_goals exact mul_inv_cancel _

end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison
