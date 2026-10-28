module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.LineOrbit.Data
/-!
# Checked edges of the five-orbit transporter forest

Each of the 3795 old catalogue entries either is its declared root or is
obtained from a parent of smaller depth by a certified trio stabilizer.
No catalogue or source label is inferred from unverified external computation.

Source: AS91 (3.4), (5.4)(1), pp.594,600.
-/
public section
-- A representative 64-edge check, including Lake preparation, took 40.34 s
-- and 2.07 GiB peak RSS. Keep finite reductions sequential.
set_option Elab.async false
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit
open SourceCycleBase.Native
private theorem checks00 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 0 j) := by decide +kernel

private theorem checks01 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 1 j) := by decide +kernel

private theorem checks02 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 2 j) := by decide +kernel

private theorem checks03 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 3 j) := by decide +kernel

private theorem checks04 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 4 j) := by decide +kernel

private theorem checks05 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 5 j) := by decide +kernel

private theorem checks06 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 6 j) := by decide +kernel

private theorem checks07 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 7 j) := by decide +kernel

private theorem checks08 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 8 j) := by decide +kernel

private theorem checks09 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 9 j) := by decide +kernel

private theorem checks10 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 10 j) := by decide +kernel

private theorem checks11 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 11 j) := by decide +kernel

private theorem checks12 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 12 j) := by decide +kernel

private theorem checks13 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 13 j) := by decide +kernel

private theorem checks14 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 14 j) := by decide +kernel

private theorem checks15 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 15 j) := by decide +kernel

private theorem checks16 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 16 j) := by decide +kernel

private theorem checks17 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 17 j) := by decide +kernel

private theorem checks18 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 18 j) := by decide +kernel

private theorem checks19 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 19 j) := by decide +kernel

private theorem checks20 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 20 j) := by decide +kernel

private theorem checks21 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 21 j) := by decide +kernel

private theorem checks22 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 22 j) := by decide +kernel

private theorem checks23 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 23 j) := by decide +kernel

private theorem checks24 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 24 j) := by decide +kernel

private theorem checks25 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 25 j) := by decide +kernel

private theorem checks26 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 26 j) := by decide +kernel

private theorem checks27 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 27 j) := by decide +kernel

private theorem checks28 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 28 j) := by decide +kernel

private theorem checks29 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 29 j) := by decide +kernel

private theorem checks30 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 30 j) := by decide +kernel

private theorem checks31 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 31 j) := by decide +kernel

private theorem checks32 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 32 j) := by decide +kernel

private theorem checks33 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 33 j) := by decide +kernel

private theorem checks34 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 34 j) := by decide +kernel

private theorem checks35 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 35 j) := by decide +kernel

private theorem checks36 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 36 j) := by decide +kernel

private theorem checks37 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 37 j) := by decide +kernel

private theorem checks38 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 38 j) := by decide +kernel

private theorem checks39 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 39 j) := by decide +kernel

private theorem checks40 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 40 j) := by decide +kernel

private theorem checks41 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 41 j) := by decide +kernel

private theorem checks42 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 42 j) := by decide +kernel

private theorem checks43 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 43 j) := by decide +kernel

private theorem checks44 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 44 j) := by decide +kernel

private theorem checks45 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 45 j) := by decide +kernel

private theorem checks46 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 46 j) := by decide +kernel

private theorem checks47 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 47 j) := by decide +kernel

private theorem checks48 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 48 j) := by decide +kernel

private theorem checks49 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 49 j) := by decide +kernel

private theorem checks50 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 50 j) := by decide +kernel

private theorem checks51 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 51 j) := by decide +kernel

private theorem checks52 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 52 j) := by decide +kernel

private theorem checks53 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 53 j) := by decide +kernel

private theorem checks54 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 54 j) := by decide +kernel

private theorem checks55 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 55 j) := by decide +kernel

private theorem checks56 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 56 j) := by decide +kernel

private theorem checks57 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 57 j) := by decide +kernel

private theorem checks58 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 58 j) := by decide +kernel

private theorem checks59 : ∀ j : Fin 64, edgeCheck (FarOrbit.index 59 j) := by decide +kernel

theorem checks (k : Fin 60) (j : Fin 64) : edgeCheck (FarOrbit.index k j) := by
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

theorem all_edges (i : Fin 3795) : edgeCheck i := by
  have he : FarOrbit.index ⟨i.val / 64,by omega⟩ ⟨i.val % 64,by omega⟩ = i := by
    apply Fin.ext
    simp only [FarOrbit.index]
    omega
  rw [←he]
  exact checks _ _
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit
