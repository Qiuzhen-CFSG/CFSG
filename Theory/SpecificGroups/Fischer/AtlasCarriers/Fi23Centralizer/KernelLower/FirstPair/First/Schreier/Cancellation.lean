module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.First.Initial
import Mathlib.Tactic.FinCases
/-!
# Cancellation and reversal of Fi23 suffix edges

The source generators with indices 2 and 3 are definitionally the already
certified involutory target generators. Canonical signed words identify each
of these target letters with its inverse. Adjacent inverse cancellation is
proved sound in the actual permutation group, so a finite word check can
recover one orientation of an involution edge from the other. No enumeration
of the 31671 letters is needed for this deduction.

The residual contract keeps only noninitial, nontree edges that cannot be
recovered from an earlier edge or a defining tree edge. Strong induction on
the representative index proves that this contract implies the original Step.
The reverse defining-tree family for source generator 2 is discharged here.

Source application: retained ATLAS F23G1-p31671B0, in the inverse right-action
convention of FirstPair/source/README.md; GLS3 Table 5.3u and the Fischer
paragraph in refs/KGroup/GLS3/Chapter5(sec3-).tex near line 1042. This is a
certificate reduction, not an unconditional stabilizer bound.
-/

set_option Elab.async false

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.First.Schreier
open KernelUpperThird (wordValue)

def canonical (i : Fin 8) : Fin 8 := if i = 5 then 1 else if i = 6 then 2 else i

def inverseLetter (i : Fin 8) : Fin 8 := canonical (Fin.ofNat 8 (i.val + 4))

theorem canonical_eq (i : Fin 8) : signedGenerator (canonical i) = signedGenerator i := by
  fin_cases i <;> apply Equiv.ext <;> intro x <;> rfl

theorem inverseLetter_eq (i : Fin 8) :
    signedGenerator (inverseLetter i) = (signedGenerator i)⁻¹ := by
  fin_cases i <;> apply Equiv.ext <;> intro x <;> rfl

def letters : Nat → Nat → List (Fin 8)
  | 0, _ => []
  | k + 1, w => canonical (Fin.ofNat 8 (w % 16)) :: letters k (w / 16)

def evaluate : List (Fin 8) → Equiv.Perm (Fin 31671)
  | [] => 1
  | i :: w => signedGenerator i * evaluate w

def cancel : List (Fin 8) → List (Fin 8)
  | [] => []
  | i :: w => match cancel w with
    | [] => [i]
    | j :: t => if inverseLetter i = j then t else i :: j :: t

theorem evaluate_letters (k w : Nat) :
    evaluate (letters k w) = wordValue signedGenerator k w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih => simp only [letters, evaluate, wordValue, canonical_eq, ih]

theorem evaluate_append (u v : List (Fin 8)) :
    evaluate (u ++ v) = evaluate u * evaluate v := by
  induction u with
  | nil => simp only [List.nil_append, evaluate, one_mul]
  | cons i u ih => simp only [List.cons_append, evaluate, ih, mul_assoc]

theorem evaluate_cancel (w : List (Fin 8)) : evaluate (cancel w) = evaluate w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    cases hc : cancel w with
    | nil =>
      simp only [hc, evaluate] at ih
      simp only [cancel, hc, evaluate, ← ih, mul_one]
    | cons j t =>
      simp only [hc, evaluate] at ih
      by_cases hij : inverseLetter i = j
      · simp only [cancel, hc, if_pos hij, evaluate, ← ih]
        rw [← hij, inverseLetter_eq, ← mul_assoc, mul_inv_cancel, one_mul]
      · simp only [cancel, hc, if_neg hij, evaluate, ← ih]

def factorLetters (a : Fin 7) (r : Fin 180) : List (Fin 8) :=
  letters (factorCode a r.val).1 (factorCode a r.val).2

theorem evaluate_factorLetters (a : Fin 7) (r : Fin 180) :
    evaluate (factorLetters a r) = (factor a r).val := evaluate_letters _ _

def inverseTest (a : Fin 7) (r : Fin 180) : Bool :=
  decide (cancel (factorLetters a (transitionForward a r) ++ factorLetters a r) = [])

theorem inverseTest_sound (a : Fin 7) (r : Fin 180) (h : inverseTest a r = true) :
    (factor a (transitionForward a r)).val * (factor a r).val = 1 := by
  have hc : cancel (factorLetters a (transitionForward a r) ++ factorLetters a r) = [] :=
    of_decide_eq_true h
  rw [← evaluate_factorLetters, ← evaluate_factorLetters, ← evaluate_append,
    ← evaluate_cancel, hc, evaluate]

theorem source_two : KernelUpperThird.packedGenerator 2 = afterOneGenerator 2 := by
  apply Equiv.ext
  intro x
  rfl

theorem source_three : KernelUpperThird.packedGenerator 3 = afterOneGenerator 1 := by
  apply Equiv.ext
  intro x
  rfl

theorem source_involutive (a : Fin 7) (h : a = 2 ∨ a = 3) :
    KernelUpperThird.packedGenerator a * KernelUpperThird.packedGenerator a = 1 := by
  rcases h with rfl | rfl
  · rw [source_two]
    have hi : (afterOneGenerator 2)⁻¹ = afterOneGenerator 2 := by
      apply Equiv.ext
      intro x
      rfl
    conv_lhs => lhs; rw [← hi]
    exact inv_mul_cancel _
  · rw [source_three]
    have hi : (afterOneGenerator 1)⁻¹ = afterOneGenerator 1 := by
      apply Equiv.ext
      intro x
      rfl
    conv_lhs => lhs; rw [← hi]
    exact inv_mul_cancel _

def Edge (a : Fin 7) (r : Fin 180) : Prop :=
  ∀ x : Fin 31671,
    KernelUpperThird.packedForward a (representativeRun r x) =
      representativeRun (transitionForward a r) (factorRun a r x)

theorem edge_iff (a : Fin 7) (r : Fin 180) : Edge a r ↔
    KernelUpperThird.packedGenerator a * representative r =
      representative (transitionForward a r) * (factor a r).val := by
  constructor
  · intro h
    apply Equiv.ext
    intro x
    simpa only [KernelUpperThird.packedForward_eq, representativeRun_eq, factorRun_eq,
      Equiv.Perm.mul_apply] using h x
  · intro h x
    have hx := congrArg (fun p : Equiv.Perm (Fin 31671) => p x) h
    simpa only [KernelUpperThird.packedForward_eq, representativeRun_eq, factorRun_eq,
      Equiv.Perm.mul_apply] using hx

theorem edge_reverse (a : Fin 7) (ha : a = 2 ∨ a = 3) (r : Fin 180)
    (ht : transitionForward a (transitionForward a r) = r)
    (hf : inverseTest a r = true) (h : Edge a (transitionForward a r)) : Edge a r := by
  apply (edge_iff a r).mpr
  have hg := source_involutive a ha
  have hw := inverseTest_sound a r hf
  have he := (edge_iff _ _).mp h
  rw [ht] at he
  apply mul_left_cancel (a := KernelUpperThird.packedGenerator a)
  calc
    _ = representative r := by rw [← mul_assoc, hg, one_mul]
    _ = (representative r * (factor a (transitionForward a r)).val) * (factor a r).val := by
      rw [mul_assoc, hw, mul_one]
    _ = (KernelUpperThird.packedGenerator a * representative (transitionForward a r)) *
        (factor a r).val := by rw [he]
    _ = _ := mul_assoc _ _ _

/-- A reverse edge is usable only after its factor cancellation is checked. -/
def reverseAvailable (a : Fin 7) (r : Fin 180) : Bool :=
  decide (a = 2 ∨ a = 3) &&
  decide (transitionForward a (transitionForward a r) = r) && inverseTest a r &&
  (decide ((transitionForward a r).val < r.val) ||
    treeEdge a (transitionForward a r).val || decide (transitionForward a r = 0))

/-- The finite equations left after tree, initial, and reverse-edge deductions. -/
def Residual (a : Fin 7) : Prop :=
  ∀ r : Fin 180, r ≠ 0 → treeEdge a r.val = false → reverseAvailable a r = false → Edge a r

theorem step_of_residual (a : Fin 7) (h : Residual a) : Step a := by
  have all : ∀ n : Nat, ∀ r : Fin 180, r.val = n → Edge a r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r hn
      by_cases hi : r = 0
      · subst r
        exact initial_step a
      cases ht : treeEdge a r.val with
      | true => exact tree_step a r ht
      | false =>
        cases hv : reverseAvailable a r with
        | false => exact h r hi ht hv
        | true =>
          simp only [reverseAvailable, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq] at hv
          obtain ⟨⟨⟨ha, hi⟩, hf⟩, hl⟩ := hv
          apply edge_reverse a ha r hi hf
          rcases hl with (hl | hl) | hl
          · exact ih (transitionForward a r).val (by omega) _ rfl
          · exact tree_step a _ hl
          · rw [hl]
            exact initial_step a
  intro r
  exact all r.val r rfl

open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

private def reverseTreeTest (n : Nat) : Bool :=
  let r := Fin.ofNat 180 n
  decide (treeEdge 2 (transitionForward 2 r).val = true →
    transitionForward 2 (transitionForward 2 r) = r ∧ inverseTest 2 r = true)

private theorem reverse_tree_checked : checkPow reverseTreeTest 0 8 = true := by decide +kernel

/-- All opposite orientations of source generator 2's defining tree edges. -/
theorem reverse_tree_two (r : Fin 180)
    (h : treeEdge 2 (transitionForward 2 r).val = true) : Edge 2 r := by
  have hc := checkPow_sound reverseTreeTest 8 0 reverse_tree_checked r.val (Nat.zero_le _)
    (Nat.lt_trans r.isLt (by decide))
  have hr : Fin.ofNat 180 r.val = r := by simp
  simp only [reverseTreeTest, hr, decide_eq_true_eq] at hc
  obtain ⟨hi, hf⟩ := hc h
  exact edge_reverse 2 (Or.inl rfl) r hi hf (tree_step 2 _ h)

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.First.Schreier
