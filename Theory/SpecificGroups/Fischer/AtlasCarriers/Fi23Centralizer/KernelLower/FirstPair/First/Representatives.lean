module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.Actions
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.FirstPair.First.Witnesses
import Mathlib.Tactic.FinCases

/-!
# Checked representatives at suffix letter 40

Every representative has its stated base image, only the identity returns the
base point, and the positive index transitions have checked inverses. These
checks use only 180 base images; they do not assert the remaining
full-permutation Schreier identities. Source: ATLAS F23G1-p31671B0; GLS3 5.3u.
-/

set_option Elab.async false

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.First
open KernelUpperThird (wordValue wordRun wordRun_eq)
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

def representative (r : Fin 180) : Equiv.Perm (Fin 31671) :=
  wordValue KernelUpperThird.packedGenerator (representativeCode r.val).1 (representativeCode r.val).2

def representativeRun (r : Fin 180) (x : Fin 31671) : Fin 31671 :=
  wordRun KernelUpperThird.packedForward (representativeCode r.val).1 (representativeCode r.val).2 x

theorem representativeRun_eq (r : Fin 180) (x : Fin 31671) :
    representativeRun r x = representative r x :=
  wordRun_eq KernelUpperThird.packedGenerator KernelUpperThird.packedForward KernelUpperThird.packedForward_eq _ _ _

theorem representative_initial : representative 0 = 1 := rfl

private def baseTest (i : Nat) : Bool :=
  let r := Fin.ofNat 180 i
  decide (representativeRun r 40 = point r) && decide (point r = 40 ↔ r = 0)

private theorem base_checked : checkPow baseTest 0 8 = true := by decide +kernel

theorem representative_base (r : Fin 180) : representative r 40 = point r := by
  have h := checkPow_sound baseTest 8 0 base_checked r.val (Nat.zero_le _)
    (Nat.lt_trans r.isLt (by decide))
  have hr : Fin.ofNat 180 r.val = r := by simp
  simp only [baseTest, hr, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (representativeRun_eq r 40).symm.trans h.1

theorem representative_returns (r : Fin 180)
    (h : representative r 40 = 40) : representative r = 1 := by
  have hc := checkPow_sound baseTest 8 0 base_checked r.val (Nat.zero_le _)
    (Nat.lt_trans r.isLt (by decide))
  have hr : Fin.ofNat 180 r.val = r := by simp
  simp only [baseTest, hr, Bool.and_eq_true, decide_eq_true_eq] at hc
  have he : r = 0 := hc.2.mp ((representative_base r).symm.trans h)
  rw [he, representative_initial]

private def inverseTest (a : Fin 7) (i : Nat) : Bool :=
  let r := Fin.ofNat 180 i
  decide (transitionBackward a (transitionForward a r) = r)

private theorem inverse_checked (a : Fin 7) : checkPow (inverseTest a) 0 8 = true := by
  fin_cases a <;> decide +kernel

theorem transition_left_inverse (a : Fin 7) :
    Function.LeftInverse (transitionBackward a) (transitionForward a) := by
  intro r
  have h := checkPow_sound (inverseTest a) 8 0 (inverse_checked a) r.val (Nat.zero_le _)
    (Nat.lt_trans r.isLt (by decide))
  have hr : Fin.ofNat 180 r.val = r := by simp
  simpa only [inverseTest, hr, decide_eq_true_eq] using h

def transition (a : Fin 7) : Equiv.Perm (Fin 180) where
  toFun := transitionForward a
  invFun := transitionBackward a
  left_inv := transition_left_inverse a
  right_inv := (transition_left_inverse a).rightInverse_of_surjective
    (Finite.surjective_of_injective (transition_left_inverse a).injective)

@[simp] theorem transition_apply (a : Fin 7) (r : Fin 180) :
    transition a r = transitionForward a r := rfl

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerFirstPair.First
