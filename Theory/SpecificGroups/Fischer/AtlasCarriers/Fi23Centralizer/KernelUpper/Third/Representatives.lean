module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Witnesses
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Data
import Mathlib.Tactic.FinCases

/-!
# Checked representatives for the stabilizer at letter 27

The actual second-stage permutations evaluate the representative words to their
listed base images. Only index zero returns letter 27, and its representative is
the identity. The six transition maps are genuine permutations of the 693 indices.
This supplies the orbit part and the inverse-step mechanism of Schreier rewriting;
full permutation transition identities remain separate obligations.

Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u.
-/

set_option Elab.async false

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird
open KernelUpperData
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

def secondMap : Fin 6 → Fin 31671 → Fin 31671
  | 0 => Two0.forward
  | 1 => Two1.forward
  | 2 => Two2.forward
  | 3 => Two3.forward
  | 4 => Two4.forward
  | 5 => Two5.forward

theorem secondMap_eq (a : Fin 6) (x : Fin 31671) :
    secondMap a x = secondGenerator a x := by
  fin_cases a <;> rfl

def representative (r : Fin 693) : Equiv.Perm (Fin 31671) :=
  wordValue secondGenerator (representativeCode r.val).1 (representativeCode r.val).2

def representativeRun (r : Fin 693) (x : Fin 31671) : Fin 31671 :=
  wordRun secondMap (representativeCode r.val).1 (representativeCode r.val).2 x

theorem representativeRun_eq (r : Fin 693) (x : Fin 31671) :
    representativeRun r x = representative r x :=
  wordRun_eq secondGenerator secondMap secondMap_eq _ _ _

theorem representative_initial : representative 0 = 1 := rfl

private def baseTest (i : Nat) : Bool :=
  let r := Fin.ofNat 693 i
  decide (representativeRun r 27 = point r) && decide (point r = 27 ↔ r = 0)

private theorem base_checked : checkPow baseTest 0 10 = true := by decide +kernel

theorem representative_base (r : Fin 693) : representative r 27 = point r := by
  have h := checkPow_sound baseTest 10 0 base_checked r.val (Nat.zero_le _)
    (Nat.lt_trans r.isLt (by decide))
  have hr : Fin.ofNat 693 r.val = r := by simp
  simp only [baseTest, hr, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (representativeRun_eq r 27).symm.trans h.1

theorem representative_returns (r : Fin 693)
    (h : representative r 27 = 27) : representative r = 1 := by
  have hc := checkPow_sound baseTest 10 0 base_checked r.val (Nat.zero_le _)
    (Nat.lt_trans r.isLt (by decide))
  have hr : Fin.ofNat 693 r.val = r := by simp
  simp only [baseTest, hr, Bool.and_eq_true, decide_eq_true_eq] at hc
  have he : r = 0 := hc.2.mp ((representative_base r).symm.trans h)
  rw [he, representative_initial]

private def inverseTest (a : Fin 6) (i : Nat) : Bool :=
  let r := Fin.ofNat 693 i
  decide (transitionBackward a (transitionForward a r) = r)

private theorem inverse_checked (a : Fin 6) : checkPow (inverseTest a) 0 10 = true := by
  fin_cases a <;> decide +kernel

theorem transition_left_inverse (a : Fin 6) :
    Function.LeftInverse (transitionBackward a) (transitionForward a) := by
  intro r
  have h := checkPow_sound (inverseTest a) 10 0 (inverse_checked a) r.val (Nat.zero_le _)
    (Nat.lt_trans r.isLt (by decide))
  have hr : Fin.ofNat 693 r.val = r := by simp
  simpa only [inverseTest, hr, decide_eq_true_eq] using h

/-- Bijective positive transitions suffice to recover all inverse steps. -/
def transition (a : Fin 6) : Equiv.Perm (Fin 693) where
  toFun := transitionForward a
  invFun := transitionBackward a
  left_inv := transition_left_inverse a
  right_inv := (transition_left_inverse a).rightInverse_of_surjective
    (Finite.surjective_of_injective (transition_left_inverse a).injective)

@[simp] theorem transition_apply (a : Fin 6) (r : Fin 693) :
    transition a r = transitionForward a r := rfl

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird
