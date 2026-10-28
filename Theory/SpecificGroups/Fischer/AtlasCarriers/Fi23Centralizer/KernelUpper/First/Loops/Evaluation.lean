module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Witnesses
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Data

/-!
# Interpreting the finite Fi23 loop action certificates

A checked path recovers the exact representative. The product of shared
registers is already an element of the unchanged auxiliary subgroup. Its
inverse is the desired Schreier element when the numerical action square
commutes on every letter. The shared-register comparison and the numerical
squares remain explicit, independent certificate obligations.

Source: retained ATLAS F23G1-p31671B0 and GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

/-- Numeric evaluation of a tree path, with the leaf edge in the low bit. -/
def evalPath : Nat → Nat → Fin 31671 → Fin 31671
  | 0, _, x => x
  | d + 1, w, x =>
    if w % 2 == 1 then sourceB (evalPath d (w / 2) x)
    else sourceA (evalPath d (w / 2) x)

/-- Numeric evaluation of a packed list of shared-register indices. -/
def evalFactors : Nat → Nat → Fin 31671 → Fin 31671
  | 0, _, x => x
  | d + 1, w, x => coreMap (w % 256) (evalFactors d (w / 256) x)

/-- The actual permutation word associated with a packed tree path. -/
def pathPerm : Nat → Nat → Equiv.Perm (Fin 31671)
  | 0, _ => 1
  | d + 1, w => (if w % 2 == 1 then generatorB else generatorA) * pathPerm d (w / 2)

theorem pathPerm_apply (d w : Nat) (x : Fin 31671) :
    pathPerm d w x = evalPath d w x := by
  induction d generalizing w with
  | zero => rfl
  | succ d ih =>
    simp only [pathPerm, evalPath, Equiv.Perm.mul_apply, ih]
    split <;> simp only [generatorA_apply_eq_sourceA, generatorB_apply_eq_sourceB]

theorem representative_eq_pathPerm (d w : Nat) (x : Fin 31671)
    (h : pathOK d w x = true) : representative x = pathPerm d w := by
  induction d generalizing w x with
  | zero =>
    have hx : x = 1 := by simpa only [pathOK, decide_eq_true_eq] using h
    subst x
    exact representative_one
  | succ d ih =>
    simp only [pathOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rw [representative_step x h.1.1, ih _ _ h.2]
    simp only [treeGenerator, pathPerm, h.1.2]

theorem sourceGenerator_eq (i : Fin 722) (x : Fin 31671) :
    sourceGenerator i x = loopGenerator i x := by
  simp only [sourceGenerator, loopGenerator]
  split <;> simp only [generatorA_apply_eq_sourceA, generatorB_apply_eq_sourceB]

/-- The shared tables must act as the corresponding actual subgroup words. -/
def CoreActions : Prop := ∀ i x, coreMap i x = (coreWord i).val x

theorem factorWord_apply (h : CoreActions) (d w : Nat) (x : Fin 31671) :
    (factorWord d w).val x = evalFactors d w x := by
  induction d generalizing w with
  | zero => rfl
  | succ d ih =>
    change (coreWord (w % 256)).val ((factorWord d (w / 256)).val x) = _
    rw [ih, ← h]
    rfl

/-- The commuting action square; its orientation avoids inverse table lookup. -/
abbrev ActionCheck (i : Fin 722) (x : Fin 31671) : Prop :=
  sourceGenerator i
      (evalPath (pathLength i) (pathBits i) (evalFactors (factorLength i) (factorBits i) x)) =
    evalPath (pathLength i) (pathBits i) x

/-- Exact action square for the literal representative and the actual word. -/
theorem loop_equation (hc : CoreActions) (i : Fin 722)
    (hp : pathOK (pathLength i) (pathBits i) (loopPoint i) = true)
    (ha : ∀ x, ActionCheck i x) :
    loopGenerator i * representative (loopPoint i) * factorWord (factorLength i) (factorBits i) =
      representative (loopPoint i) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply,
    representative_eq_pathPerm _ _ _ hp, pathPerm_apply, factorWord_apply hc]
  exact (sourceGenerator_eq _ _).symm.trans (ha x)

/-- A complete numerical square identifies the inverse subgroup word with the
actual Schreier element. No subgroup equality or order is used. -/
theorem loop_edge_mem (hc : CoreActions) (i : Fin 722)
    (hp : pathOK (pathLength i) (pathBits i) (loopPoint i) = true)
    (hf : loopGenerator i (loopPoint i) = loopPoint i)
    (ha : ∀ x, ActionCheck i x) :
    edge (loopGenerator i) (loopPoint i) ∈ KernelUpperData.first := by
  let f := factorWord (factorLength i) (factorBits i)
  have he : edge (loopGenerator i) (loopPoint i) * (f : Equiv.Perm (Fin 31671)) = 1 := by
    rw [edge, hf]
    calc
      _ = (representative (loopPoint i))⁻¹ *
          (loopGenerator i * representative (loopPoint i) * f) := by simp only [mul_assoc]
      _ = (representative (loopPoint i))⁻¹ * representative (loopPoint i) := by
        rw [loop_equation hc i hp ha]
      _ = 1 := inv_mul_cancel _
  have heq : edge (loopGenerator i) (loopPoint i) = (f : Equiv.Perm (Fin 31671))⁻¹ :=
    eq_inv_of_mul_eq_one_left he
  rw [heq]
  exact KernelUpperData.first.inv_mem f.property

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops
