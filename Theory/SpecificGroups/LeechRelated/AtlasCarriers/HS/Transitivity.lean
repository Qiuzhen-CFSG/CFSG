module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Transitivity of the fixed degree-100 HS carrier

For each letter, a positive word in the two defining ATLAS permutations
sends zero to that letter. The 100 identities are checked in Lean's kernel.
They prove transitivity of this exact carrier, without an order calculation,
a simplicity assumption, or comparison with a lattice or graph model.

The words were found by breadth-first search in the generator action. The
reproducible search is in `Transitivity/source/generate.py`; it reads the
zero-based cycles from `HS.lean` and respects its inverse-action convention.
The original permutations are ATLAS HSG1-p100B0. This supplies the transitive
action used for the point-stabilizer argument in GLS3, Table 5.3m, p.274.
-/

public section
open Subgroup MulAction
namespace Sporadic.LeechRelated.HS
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

private def orbitWords : List (List Bool) :=
  [[],
    [false, true, true, true, false],
    [false, true, true, false, true, false],
    [true, false, true, true, true, true, false, true],
    [false, true, true, false, true, true, true, true, false, true, false],
    [false, true, true, false, true, true, true, true, false],
    [true, true, true, true, false, true, true, true],
    [true, true, false, true, true, true, false],
    [true, false, true],
    [true, true],
    [true, true, false, true, true, true, true, false, true, false],
    [true, true, true, true, false, true, false],
    [true, true, true],
    [true, true, true, false, true, false],
    [false, true, false, true, true, true, true, false, true, false],
    [true, true, false, true, true, true],
    [true, false, true, true, false, true, false],
    [false, true, false, true, false, true],
    [false, true, true, false, true, false, true, false],
    [true, false, true, true, true],
    [true, true, true, true, false, true, false, true, false, true, false],
    [true, true, true, false, true, false, true, false, true, false],
    [false, true],
    [true, false, true, true, false, true, true, true, true, false],
    [true, true, false, true, true, false, true, false],
    [false, true, false, true, true, true, true, false],
    [true, true, false, true, true, true, false, true, true, true, true, false],
    [false, true, true, true],
    [false, true, true, true, true, false, true],
    [true, true, true, false, true, true, true, false],
    [true, false, true, true, false, true, true, false, true, false, true, false],
    [true, true, true, false, true, true, true, true, false, true, false],
    [false, true, true, false, true],
    [false, true, true, true, true, false, true, true, true],
    [true, true, false, true, true, false, true, false, true, false],
    [true, true, false],
    [false, true, true, true, true, false, true, true, true, true],
    [true, false, true, true, true, false],
    [true, false, true, false, true, false, true, false],
    [true, true, true, true, false, true, true, false, true, false],
    [true, true, true, false, true, true, true, true],
    [true, false, true, true, true, true, false, true, false],
    [false, true, false, true, true, true, true, false, true],
    [true, false, true, true, false, true],
    [true, true, true, false, true, false, true, false, true],
    [false, true, true, true, true, false, true, false],
    [true],
    [true, true, true, false, true, true, false, true, false],
    [false, true, true, true, true],
    [false, true, true, true, true, false],
    [true, false, true, true, true, false, true, true, true, true, false],
    [true, true, false, true, false, true, false],
    [false, true, true, true, false, true, false, true],
    [false, true, false, true, true, false, true, true, true, true, false],
    [true, false, true, false],
    [false, true, true, false, true, true, false, true, false, true, false],
    [true, false, true, false, true],
    [true, true, true, true, false, true, false, true, true, true, true, false],
    [false, true, true, true, false, true, true, false, true, false],
    [false],
    [true, true, false, true],
    [true, true, true, false, true, true, true, true, false],
    [false, true, false, true],
    [true, true, false, true, false, true, false, true, false],
    [false, true, true, true, false, true, true, false, true, false, true, false],
    [true, false, true, false, true, true, false, true, true, true, true, false],
    [true, true, true, true, false, true, true, true, true],
    [false, true, false],
    [true, true, true, true, false, true, false, true, false, true],
    [true, false, true, true, true, true],
    [false, true, true, true, false, true, false],
    [true, true, true, false],
    [false, true, true, true, false, true, true, true, true, false],
    [true, true, true, true, false],
    [false, true, false, true, false],
    [true, false, true, false, true, false, true],
    [true, false, true, false, true, true, true, true, false],
    [true, false, true, true, true, true, false],
    [true, true, true, false, true, true, false, true, false, true, false],
    [true, true, false, true, true, true, true],
    [true, true, false, true, false],
    [true, false],
    [true, true, true, false, true, true, true],
    [true, true, false, true, false, true, false, true],
    [true, true, false, true, false, true, true, true, true, false],
    [true, true, true, true],
    [true, true, false, true, true, true, true, false],
    [false, true, true, true, false, true, false, true, false, true],
    [true, true, true, true, false, true],
    [false, true, true, false, true, false, true, false, true],
    [true, true, true, true, false, true, true, true, true, false, true, false],
    [false, true, false, true, false, true, true, true, true, false],
    [true, false, true, true, false, true, false, true, false],
    [true, false, true, false, true, false],
    [true, true, true, false, true],
    [true, true, true, false, true, false, true, true, true, true, false],
    [true, true, false, true, false, true],
    [false, true, true, false, true, false, true, true, true, true, false],
    [true, true, true, false, true, false, true],
    [false, true, false, true, false, true, false]]

private def orbitWord : List Bool → Carrier
  | [] => 1
  | false :: w => generatorAElement * orbitWord w
  | true :: w => generatorBElement * orbitWord w

private def representative (i : Fin 100) : Carrier := orbitWord (orbitWords[i.val]!)

private def checkFin (f : Fin 100 → Bool) : Bool :=
  (List.range 100).all (fun i => if h : i < 100 then f ⟨i, h⟩ else true)

private theorem allFin (P : Fin 100 → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

private theorem representative_apply (i : Fin 100) :
    (representative i : Equiv.Perm (Fin 100)) 0 = i := by
  have h : ∀ j : Fin 100, (representative j : Equiv.Perm (Fin 100)) 0 = j := by
    apply allFin
    decide +kernel
  exact h i

/-- Every letter is reached from zero by an element of the defining carrier. -/
theorem exists_apply_zero (i : Fin 100) : ∃ g : Carrier, (g : Equiv.Perm (Fin 100)) 0 = i :=
  ⟨representative i, representative_apply i⟩

/-- The natural action of the ATLAS carrier on its 100 letters is transitive. -/
instance carrier_isPretransitive : IsPretransitive Carrier (Fin 100) where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := exists_apply_zero x
    obtain ⟨h, hh⟩ := exists_apply_zero y
    refine ⟨h * g⁻¹, ?_⟩
    change ((h : Equiv.Perm (Fin 100)) * (g : Equiv.Perm (Fin 100))⁻¹) x = y
    rw [Equiv.Perm.mul_apply, ← hg, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hh]
end Sporadic.LeechRelated.HS
