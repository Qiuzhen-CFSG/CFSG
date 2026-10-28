module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneOrbit.Data
/-!
# Checked native sextet forest

Each row certifies its minimum tetrad, its descending transport edge, and
strict ordering of the next minimum. Coverage is supplied independently by
`Native.plane_card`. A 64-row sample took 16.23 seconds and 2,003,208 KiB;
sequential elaboration bounds the number of live reduction contexts.

Source: AS91 (3.11.2), p.596.
-/
@[expose] public section
set_option Elab.async false
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneOrbit
private theorem checks00 : ∀ j : Fin 64, rowCheck (index 0 j) ∧ orderedNext (index 0 j) := by decide +kernel
private theorem checks01 : ∀ j : Fin 64, rowCheck (index 1 j) ∧ orderedNext (index 1 j) := by decide +kernel
private theorem checks02 : ∀ j : Fin 64, rowCheck (index 2 j) ∧ orderedNext (index 2 j) := by decide +kernel
private theorem checks03 : ∀ j : Fin 64, rowCheck (index 3 j) ∧ orderedNext (index 3 j) := by decide +kernel
private theorem checks04 : ∀ j : Fin 64, rowCheck (index 4 j) ∧ orderedNext (index 4 j) := by decide +kernel
private theorem checks05 : ∀ j : Fin 64, rowCheck (index 5 j) ∧ orderedNext (index 5 j) := by decide +kernel
private theorem checks06 : ∀ j : Fin 64, rowCheck (index 6 j) ∧ orderedNext (index 6 j) := by decide +kernel
private theorem checks07 : ∀ j : Fin 64, rowCheck (index 7 j) ∧ orderedNext (index 7 j) := by decide +kernel
private theorem checks08 : ∀ j : Fin 64, rowCheck (index 8 j) ∧ orderedNext (index 8 j) := by decide +kernel
private theorem checks09 : ∀ j : Fin 64, rowCheck (index 9 j) ∧ orderedNext (index 9 j) := by decide +kernel
private theorem checks10 : ∀ j : Fin 64, rowCheck (index 10 j) ∧ orderedNext (index 10 j) := by decide +kernel
private theorem checks11 : ∀ j : Fin 64, rowCheck (index 11 j) ∧ orderedNext (index 11 j) := by decide +kernel
private theorem checks12 : ∀ j : Fin 64, rowCheck (index 12 j) ∧ orderedNext (index 12 j) := by decide +kernel
private theorem checks13 : ∀ j : Fin 64, rowCheck (index 13 j) ∧ orderedNext (index 13 j) := by decide +kernel
private theorem checks14 : ∀ j : Fin 64, rowCheck (index 14 j) ∧ orderedNext (index 14 j) := by decide +kernel
private theorem checks15 : ∀ j : Fin 64, rowCheck (index 15 j) ∧ orderedNext (index 15 j) := by decide +kernel
private theorem checks16 : ∀ j : Fin 64, rowCheck (index 16 j) ∧ orderedNext (index 16 j) := by decide +kernel
private theorem checks17 : ∀ j : Fin 64, rowCheck (index 17 j) ∧ orderedNext (index 17 j) := by decide +kernel
private theorem checks18 : ∀ j : Fin 64, rowCheck (index 18 j) ∧ orderedNext (index 18 j) := by decide +kernel
private theorem checks19 : ∀ j : Fin 64, rowCheck (index 19 j) ∧ orderedNext (index 19 j) := by decide +kernel
private theorem checks20 : ∀ j : Fin 64, rowCheck (index 20 j) ∧ orderedNext (index 20 j) := by decide +kernel
private theorem checks21 : ∀ j : Fin 64, rowCheck (index 21 j) ∧ orderedNext (index 21 j) := by decide +kernel
private theorem checks22 : ∀ j : Fin 64, rowCheck (index 22 j) ∧ orderedNext (index 22 j) := by decide +kernel
private theorem checks23 : ∀ j : Fin 64, rowCheck (index 23 j) ∧ orderedNext (index 23 j) := by decide +kernel
private theorem checks24 : ∀ j : Fin 64, rowCheck (index 24 j) ∧ orderedNext (index 24 j) := by decide +kernel
private theorem checks25 : ∀ j : Fin 64, rowCheck (index 25 j) ∧ orderedNext (index 25 j) := by decide +kernel
private theorem checks26 : ∀ j : Fin 64, rowCheck (index 26 j) ∧ orderedNext (index 26 j) := by decide +kernel
private theorem checks27 : ∀ j : Fin 64, rowCheck (index 27 j) ∧ orderedNext (index 27 j) := by decide +kernel

theorem checks (k : Fin 28) (j : Fin 64) : rowCheck (index k j) ∧ orderedNext (index k j) := by
  fin_cases k
  · exact checks00 j
  · exact checks01 j
  · exact checks02 j
  · exact checks03 j
  · exact checks04 j
  · exact checks05 j
  · exact checks06 j
  · exact checks07 j
  · exact checks08 j
  · exact checks09 j
  · exact checks10 j
  · exact checks11 j
  · exact checks12 j
  · exact checks13 j
  · exact checks14 j
  · exact checks15 j
  · exact checks16 j
  · exact checks17 j
  · exact checks18 j
  · exact checks19 j
  · exact checks20 j
  · exact checks21 j
  · exact checks22 j
  · exact checks23 j
  · exact checks24 j
  · exact checks25 j
  · exact checks26 j
  · exact checks27 j

theorem all_rows (i : Fin 1771) : rowCheck i ∧ orderedNext i := by
  have he : index ⟨i.val/64,by omega⟩ ⟨i.val%64,by omega⟩ = i := by
    apply Fin.ext
    simp only [index]
    omega
  rw [←he]
  exact checks _ _
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneOrbit
