module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.Second.Representatives
public import Theory.GroupAction.GeneratorStabilizerReduction
import Mathlib.Tactic.FinCases

/-!
# Word factors and tree transitions for suffix letter 46

Signed factors are proved members of the literal target subgroup. All defining
Schreier tree edges are proved as word identities, without enumerating 31671
letters. The remaining positive transitions are explicit finite equations.
The checked bijective index maps recover every inverse transition algebraically;
representative separation then gives the stabilizer upper bound.
Source application: ATLAS F23G1-p31671B0; GLS3 Table 5.3u.
-/

set_option Elab.async false

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.Second
open KernelUpperThird (wordValue wordRun wordRun_eq wordValue_mem)
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

def factor (a : Fin 4) (r : Fin 48) : KernelLowerData.afterTwo :=
  ⟨wordValue signedGenerator (factorCode a r.val).1 (factorCode a r.val).2,
   wordValue_mem KernelLowerData.afterTwo signedGenerator signedGenerator_mem _ _⟩

def factorRun (a : Fin 4) (r : Fin 48) (x : Fin 31671) : Fin 31671 :=
  wordRun signedMap (factorCode a r.val).1 (factorCode a r.val).2 x

theorem factorRun_eq (a : Fin 4) (r : Fin 48) (x : Fin 31671) :
    factorRun a r x = (factor a r).val x :=
  wordRun_eq signedGenerator signedMap signedMap_eq _ _ _

/-- Exact all-letter positive transition; no externally claimed identity. -/
def Step (a : Fin 4) : Prop :=
  ∀ r : Fin 48, ∀ x : Fin 31671,
    afterOneForward a (representativeRun r x) =
      representativeRun (transitionForward a r) (factorRun a r x)

theorem step_eq (a : Fin 4) (h : Step a) (r : Fin 48) :
    afterOneGenerator a * representative r =
      representative (transition a r) * (factor a r).val := by
  apply Equiv.ext
  intro x
  simpa only [afterOneForward_eq, representativeRun_eq, factorRun_eq,
    Equiv.Perm.mul_apply, transition_apply] using h r x

private def treeTest (a : Fin 4) (i : Nat) : Bool :=
  let r := Fin.ofNat 48 i
  let t := transitionForward a r
  decide (treeEdge a r.val = true →
    (representativeCode t.val).1 = (representativeCode r.val).1 + 1 ∧
    (representativeCode t.val).2 % 16 = a.val ∧
    (representativeCode t.val).2 / 16 = (representativeCode r.val).2 ∧
    (factorCode a r.val).1 = 0)

private theorem tree_checked (a : Fin 4) : checkPow (treeTest a) 0 6 = true := by
  fin_cases a <;> decide +kernel

theorem tree_step_eq (a : Fin 4) (r : Fin 48) (ht : treeEdge a r.val = true) :
    afterOneGenerator a * representative r =
      representative (transition a r) * (factor a r).val := by
  have hc := checkPow_sound (treeTest a) 6 0 (tree_checked a) r.val (Nat.zero_le _)
    (Nat.lt_trans r.isLt (by decide))
  have hr : Fin.ofNat 48 r.val = r := by simp
  simp only [treeTest, hr, decide_eq_true_eq] at hc
  obtain ⟨hk, hw₀, hw₁, hf⟩ := hc ht
  have hfactor : (factor a r).val = 1 := by
    change wordValue signedGenerator (factorCode a r.val).1 (factorCode a r.val).2 = 1
    rw [hf]
    rfl
  rw [hfactor, mul_one]
  change afterOneGenerator a * wordValue afterOneGenerator
    (representativeCode r.val).1 (representativeCode r.val).2 =
    wordValue afterOneGenerator (representativeCode (transitionForward a r).val).1
      (representativeCode (transitionForward a r).val).2
  rw [hk, wordValue, hw₀, hw₁]
  simp

theorem tree_step (a : Fin 4) (r : Fin 48) (ht : treeEdge a r.val = true)
    (x : Fin 31671) :
    afterOneForward a (representativeRun r x) =
      representativeRun (transitionForward a r) (factorRun a r x) := by
  have h := congrArg (fun p : Equiv.Perm (Fin 31671) => p x) (tree_step_eq a r ht)
  simpa only [afterOneForward_eq, representativeRun_eq, factorRun_eq,
    Equiv.Perm.mul_apply, transition_apply] using h

/-- The defining tree edges are already discharged for the remaining checker. -/
theorem step_of_nontree (a : Fin 4)
    (h : ∀ r : Fin 48, treeEdge a r.val = false → ∀ x : Fin 31671,
      afterOneForward a (representativeRun r x) =
        representativeRun (transitionForward a r) (factorRun a r x)) : Step a := by
  intro r x
  cases ht : treeEdge a r.val with
  | false => exact h r ht x
  | true => exact tree_step a r ht x

/-- Positive identities, including every remaining edge, recover inverse steps. -/
def reduction (h : ∀ a, Step a) :
    Subgroup.GeneratorStabilizerReduction afterOneGenerator KernelLowerData.afterTwo
      (46 : Fin 31671) (Fin 48) :=
  Subgroup.GeneratorStabilizerReduction.ofPermutations afterOneGenerator KernelLowerData.afterTwo
    (46 : Fin 31671) representative 0 representative_initial transition factor
    (fun a r => step_eq a (h a) r) (fun p => KernelLowerData.afterTwo_fixes_46 p.property) representative_returns

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.Second
