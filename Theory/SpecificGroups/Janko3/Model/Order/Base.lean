module

public import Theory.SpecificGroups.Janko3.Model.Basic
public import Theory.GroupTheory.WordSubgroup
import Mathlib.Tactic.FinCases

/-!
# The initial subgroup of the J₃ stabilizer chain

The signed alphabet consists of the two ATLAS generators and their inverses.
Its word subgroup is exactly the public concrete model. A small exhaustive
checker supports the finite witness tables in the subsequent chain modules.
Source: ATLAS J3G1-p6156B0, retained under `Model/data/`.
-/

namespace Sporadic.Janko3.OrderCertificate
open Theory.GroupTheory

/-- Exhaustive Boolean checking over a finite ordinal. -/
@[expose] public def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)

public theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

public theorem allFin₂ {n m : Nat} (P : Fin n → Fin m → Prop)
    [∀ i j, Decidable (P i j)]
    (h : checkFin (fun i => checkFin (fun j => decide (P i j))) = true) :
    ∀ i j, P i j := by
  intro i
  apply allFin
  have hi := allFin (fun i => checkFin (fun j => decide (P i j)) = true) (by
    simpa only [Bool.decide_eq_true] using h)
  exact hi i

@[expose] public def L0Gen : Fin 4 → Equiv.Perm (Fin 6156)
  | 0 => atlasA
  | 1 => atlasB
  | 2 => atlasA⁻¹
  | 3 => atlasB⁻¹

@[expose] public def L0Inv : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1

public theorem L0Inv_spec (i : Fin 4) : L0Gen (L0Inv i) = (L0Gen i)⁻¹ := by
  fin_cases i <;> simp only [L0Inv, L0Gen, inv_inv]

@[expose] public def H0 : Subgroup (Equiv.Perm (Fin 6156)) :=
  wordSubgroup L0Gen L0Inv L0Inv_spec

public theorem H0_eq_modelSubgroup : H0 = modelSubgroup := by
  apply le_antisymm
  · intro g hg
    obtain ⟨w, rfl⟩ := hg
    have hgen (i : Fin 4) : L0Gen i ∈ modelSubgroup := by
      fin_cases i <;> simp only [L0Gen]
      · exact atlasA_mem
      · exact atlasB_mem
      · exact modelSubgroup.inv_mem atlasA_mem
      · exact modelSubgroup.inv_mem atlasB_mem
    induction w with
    | nil => exact modelSubgroup.one_mem
    | cons i w ih => exact modelSubgroup.mul_mem (hgen i) ih
  · apply (Subgroup.closure_le H0).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨[0], by simp [evalWord, L0Gen]⟩
    · have hg' : g = atlasB := hg
      subst g
      exact ⟨[1], by simp [evalWord, L0Gen]⟩

end Sporadic.Janko3.OrderCertificate
