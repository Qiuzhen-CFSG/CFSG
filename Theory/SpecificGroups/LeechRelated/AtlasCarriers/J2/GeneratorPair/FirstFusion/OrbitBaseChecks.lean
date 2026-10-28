module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.OrbitData

/-!
# Small checks for the J₂ conjugacy-orbit certificate

The kernel verifies the base row, the spanning-tree word identities, and
a left inverse of the four-point fingerprint. The Boolean finite checker
avoids expanding the less efficient universal quantifier decision instance.
The generator transitions are verified in the separate `OrbitChecks` module.

Source: ATLAS `J2G1-p100B0`; candidate data are in `OrbitData`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
open OrbitData
set_option maxRecDepth 100000
set_option Elab.async false

def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)

theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

theorem value_zero : ∀ p : Fin 100, value 0 p = tPerm p := by
  apply allFin
  decide +kernel

theorem word_data : ∀ i : Fin 315, i ≠ 0 →
    (parent i).val < i.val ∧
    words i = words (parent i) ++ [parentLetter i] ∧
    next (parent i) (parentLetter i) = i := by
  apply allFin
  decide +kernel

theorem fingerprint_left_inverse : ∀ i : Fin 315, identify (fingerprint (value i)) = i := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
