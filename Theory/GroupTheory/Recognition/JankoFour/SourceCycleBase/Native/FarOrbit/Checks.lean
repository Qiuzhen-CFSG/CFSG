module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit.Data
/-!
# Checked forest edges and distinct trio keys

Each chunk certifies sorted octad masks, the root or a descending forest edge,
and the next strict key comparison. `all_rows` covers the entire 3795-entry
table. The mathematical assembly uses the forest for transporters and the
ordered keys for injectivity; coverage then follows from the native trio count.

Source: AS91 (3.8). Every finite equality is checked by the Lean kernel.
-/
@[expose] public section
-- The parallel 60-chunk probe peaked at 7.4 GB. Keep the reduction contexts
-- sequential while retaining the default kernel limits and Lake threading.
set_option Elab.async false
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit

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

private theorem checks28 : ∀ j : Fin 64, rowCheck (index 28 j) ∧ orderedNext (index 28 j) := by decide +kernel

private theorem checks29 : ∀ j : Fin 64, rowCheck (index 29 j) ∧ orderedNext (index 29 j) := by decide +kernel

private theorem checks30 : ∀ j : Fin 64, rowCheck (index 30 j) ∧ orderedNext (index 30 j) := by decide +kernel

private theorem checks31 : ∀ j : Fin 64, rowCheck (index 31 j) ∧ orderedNext (index 31 j) := by decide +kernel

private theorem checks32 : ∀ j : Fin 64, rowCheck (index 32 j) ∧ orderedNext (index 32 j) := by decide +kernel

private theorem checks33 : ∀ j : Fin 64, rowCheck (index 33 j) ∧ orderedNext (index 33 j) := by decide +kernel

private theorem checks34 : ∀ j : Fin 64, rowCheck (index 34 j) ∧ orderedNext (index 34 j) := by decide +kernel

private theorem checks35 : ∀ j : Fin 64, rowCheck (index 35 j) ∧ orderedNext (index 35 j) := by decide +kernel

private theorem checks36 : ∀ j : Fin 64, rowCheck (index 36 j) ∧ orderedNext (index 36 j) := by decide +kernel

private theorem checks37 : ∀ j : Fin 64, rowCheck (index 37 j) ∧ orderedNext (index 37 j) := by decide +kernel

private theorem checks38 : ∀ j : Fin 64, rowCheck (index 38 j) ∧ orderedNext (index 38 j) := by decide +kernel

private theorem checks39 : ∀ j : Fin 64, rowCheck (index 39 j) ∧ orderedNext (index 39 j) := by decide +kernel

private theorem checks40 : ∀ j : Fin 64, rowCheck (index 40 j) ∧ orderedNext (index 40 j) := by decide +kernel

private theorem checks41 : ∀ j : Fin 64, rowCheck (index 41 j) ∧ orderedNext (index 41 j) := by decide +kernel

private theorem checks42 : ∀ j : Fin 64, rowCheck (index 42 j) ∧ orderedNext (index 42 j) := by decide +kernel

private theorem checks43 : ∀ j : Fin 64, rowCheck (index 43 j) ∧ orderedNext (index 43 j) := by decide +kernel

private theorem checks44 : ∀ j : Fin 64, rowCheck (index 44 j) ∧ orderedNext (index 44 j) := by decide +kernel

private theorem checks45 : ∀ j : Fin 64, rowCheck (index 45 j) ∧ orderedNext (index 45 j) := by decide +kernel

private theorem checks46 : ∀ j : Fin 64, rowCheck (index 46 j) ∧ orderedNext (index 46 j) := by decide +kernel

private theorem checks47 : ∀ j : Fin 64, rowCheck (index 47 j) ∧ orderedNext (index 47 j) := by decide +kernel

private theorem checks48 : ∀ j : Fin 64, rowCheck (index 48 j) ∧ orderedNext (index 48 j) := by decide +kernel

private theorem checks49 : ∀ j : Fin 64, rowCheck (index 49 j) ∧ orderedNext (index 49 j) := by decide +kernel

private theorem checks50 : ∀ j : Fin 64, rowCheck (index 50 j) ∧ orderedNext (index 50 j) := by decide +kernel

private theorem checks51 : ∀ j : Fin 64, rowCheck (index 51 j) ∧ orderedNext (index 51 j) := by decide +kernel

private theorem checks52 : ∀ j : Fin 64, rowCheck (index 52 j) ∧ orderedNext (index 52 j) := by decide +kernel

private theorem checks53 : ∀ j : Fin 64, rowCheck (index 53 j) ∧ orderedNext (index 53 j) := by decide +kernel

private theorem checks54 : ∀ j : Fin 64, rowCheck (index 54 j) ∧ orderedNext (index 54 j) := by decide +kernel

private theorem checks55 : ∀ j : Fin 64, rowCheck (index 55 j) ∧ orderedNext (index 55 j) := by decide +kernel

private theorem checks56 : ∀ j : Fin 64, rowCheck (index 56 j) ∧ orderedNext (index 56 j) := by decide +kernel

private theorem checks57 : ∀ j : Fin 64, rowCheck (index 57 j) ∧ orderedNext (index 57 j) := by decide +kernel

private theorem checks58 : ∀ j : Fin 64, rowCheck (index 58 j) ∧ orderedNext (index 58 j) := by decide +kernel

private theorem checks59 : ∀ j : Fin 64, rowCheck (index 59 j) ∧ orderedNext (index 59 j) := by decide +kernel

theorem checks (k : Fin 60) (j : Fin 64) : rowCheck (index k j) ∧ orderedNext (index k j) := by
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
  · exact checks28 j
  · exact checks29 j
  · exact checks30 j
  · exact checks31 j
  · exact checks32 j
  · exact checks33 j
  · exact checks34 j
  · exact checks35 j
  · exact checks36 j
  · exact checks37 j
  · exact checks38 j
  · exact checks39 j
  · exact checks40 j
  · exact checks41 j
  · exact checks42 j
  · exact checks43 j
  · exact checks44 j
  · exact checks45 j
  · exact checks46 j
  · exact checks47 j
  · exact checks48 j
  · exact checks49 j
  · exact checks50 j
  · exact checks51 j
  · exact checks52 j
  · exact checks53 j
  · exact checks54 j
  · exact checks55 j
  · exact checks56 j
  · exact checks57 j
  · exact checks58 j
  · exact checks59 j

theorem all_rows (i : Fin 3795) : rowCheck i ∧ orderedNext i := by
  have he : index ⟨i.val/64,by omega⟩ ⟨i.val%64,by omega⟩ = i := by
    apply Fin.ext
    simp only [index]
    omega
  rw [←he]
  exact checks _ _
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
