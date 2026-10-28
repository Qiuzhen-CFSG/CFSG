module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.Setup
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.ATree
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.BTree
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.WordData

/-!
# From shared-prefix checks to the literal degree-1000 row orbit

A checked transition identifies the source word as its earlier parent's word
followed by one letter, and checks the candidate vector's right multiplication
by that letter's published matrix. Strong induction then identifies every
candidate with `rowOrbit`, without evaluating any full word matrix.

Source: `Binary/source/density1000.json`; attribution and certificate boundaries
are documented in `RowSpan/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan
open RowArithmetic Matrix

/-- Both word orientation and numerical right multiplication are checked. -/
def StepCheck (i : ℕ) : Prop :=
  parents[i]! < i ∧
    Data.rowWords[i]! = Data.rowWords[parents[i]!]! ++ [letters[i]!] ∧
    (if letters[i]! then bTree else aTree).product Data.rowRows[parents[i]!]! =
      Data.rowRows[i]!

instance (i : ℕ) : Decidable (StepCheck i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem generator_vecMul (b : Bool) (x y : ℕ)
    (h : (if b then bTree else aTree).product x = y) :
    vecMul (vector 1000 x) (generator b) = vector 1000 y := by
  cases b
  · exact vecMul_of_tree 1000 aTree D1000.aRows aTree_valid aTree_rows aTree_size x y h
  · exact vecMul_of_tree 1000 bTree D1000.bRows bTree_valid bTree_rows bTree_size x y h

/-- Appending a letter means right multiplication, with the actual source word. -/
theorem rowOrbit_step (i p : Fin 1000) (b : Bool)
    (hw : Data.rowWords[i.val]! = Data.rowWords[p.val]! ++ [b]) :
    rowOrbit i = vecMul (rowOrbit p) (generator b) := by
  unfold rowOrbit rowActor
  rw [hw, wordMatrix_append]
  simp only [wordMatrix, mul_one, vecMul_vecMul]

private theorem root_word : Data.rowWords[0]! = [] := by decide +kernel
private theorem root_row : Data.rowRows[0]! = Data.functional := by decide +kernel

/-- The source root is precisely the supplied functional, acted on by one. -/
theorem rowOrbit_zero : rowOrbit 0 = vector 1000 Data.rowRows[0]! := by
  simp only [rowOrbit, rowActor, Fin.val_zero, root_word, wordMatrix, vecMul_one,
    root_row, functionalVector]

/-- Checked recurrences identify all 1000 literal orbit vectors. -/
theorem rowOrbit_eq_of_checks (h : On 1 1000 StepCheck) (i : Fin 1000) :
    rowOrbit i = vector 1000 Data.rowRows[i.val]! := by
  have hi : ∀ k, (hk : k < 1000) →
      rowOrbit ⟨k, hk⟩ = vector 1000 Data.rowRows[k]! := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hz : k = 0
      · subst k
        exact rowOrbit_zero
      · have hs := h k (by omega) hk
        have hp : parents[k]! < 1000 := lt_trans hs.1 hk
        rw [rowOrbit_step ⟨k, hk⟩ ⟨parents[k]!, hp⟩ letters[k]! hs.2.1,
          ih _ hs.1 hp]
        exact generator_vecMul _ _ _ hs.2.2
  exact hi i.val i.isLt

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan
