module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Links.Seeds.Program
import Mathlib.Tactic.FinCases

/-!
# The precise finite obligations for the Fi23 seed program

The dependency order and the eleven seed indices are checked here. Local
equations realize the shared tables inside the original auxiliary subgroup;
pointwise output comparisons then identify the actual Schreier edges.
Neither family of equations is assumed to have been proved by its generator.

Source: the retained ATLAS F23G1-p31671B0 program in
`Links/source/seed-nodes.json`, applied to GLS3 Table 5.3u.
-/

set_option Elab.async false

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

private def orderTest (k : Nat) : Bool :=
  if k < 345 then decide (Earlier k (program k)) else true

private theorem order_checked : checkPow orderTest 0 9 = true := by decide +kernel

theorem program_earlier (k : Nat) (hk : k < 345) : Earlier k (program k) := by
  have h := checkPow_sound orderTest 9 0 order_checked k (Nat.zero_le _)
    (Nat.lt_trans hk (by decide))
  simpa only [orderTest, if_pos hk, decide_eq_true_eq] using h

theorem output_lt (i : Fin 11) : output i < 345 := by
  fin_cases i <;> decide

/-- The output order agrees with the literal Boolean seed predicate. -/
theorem seed_iff_output (x : Fin 31671) :
    seed x = true ↔ ∃ i : Fin 11, seedLetter i = x := by
  constructor
  · intro h
    simp only [seed, Bool.or_eq_true, beq_iff_eq, or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, Fin.ext h.symm⟩
    · exact ⟨1, Fin.ext h.symm⟩
    · exact ⟨2, Fin.ext h.symm⟩
    · exact ⟨3, Fin.ext h.symm⟩
    · exact ⟨4, Fin.ext h.symm⟩
    · exact ⟨5, Fin.ext h.symm⟩
    · exact ⟨6, Fin.ext h.symm⟩
    · exact ⟨7, Fin.ext h.symm⟩
    · exact ⟨8, Fin.ext h.symm⟩
    · exact ⟨9, Fin.ext h.symm⟩
    · exact ⟨10, Fin.ext h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> decide

/-- All local equations, each checked on every letter of the actual carrier. -/
def Steps : Prop := ∀ k, k < 345 → Equation table k (program k)

/-- Comparison of the eleven computed outputs with the literal tree edges. -/
def Outputs : Prop := ∀ i : Fin 11, ∀ x : Fin 31671,
  table (output i) x = edge generatorA (seedLetter i) x

theorem table_realized (hsteps : Steps) (k : Nat) (hk : k < 345) :
    Realized (table k) :=
  realized_of_equations 345 program table program_earlier hsteps k hk

/-- Conditional certificate assembly; the equations remain genuine obligations. -/
theorem seed_edges_mem_of_equations (hsteps : Steps) (houtputs : Outputs)
    (x : Fin 31671) (hx : seed x = true) :
    edge generatorA x ∈ KernelUpperData.first := by
  obtain ⟨i, rfl⟩ := (seed_iff_output x).mp hx
  exact mem_of_realized (table_realized hsteps (output i) (output_lt i))
    (edge generatorA (seedLetter i)) (houtputs i)

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Links.Seeds
