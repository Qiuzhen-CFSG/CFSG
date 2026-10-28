module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Assembly

/-!
# Bounded checks for the shared packed columns

There are 126 consecutive blocks of eight output roots. The division/remainder
argument below shows that checking all blocks checks every root exactly once.
It does not assume any numerical result. The word and row producers can use
these lemmas to bound the size of each kernel computation.

Source: the exact 1008-column contracts in Coefficients/Arithmetic.lean.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

/-- A bounded block of eight original output indices. -/
def outputIndex (q : Fin 126) (r : Fin 8) : Fin 1008 :=
  ⟨8 * q.val + r.val, by have := q.isLt; have := r.isLt; omega⟩

def WordBlock (d : Fin 26) (q : Fin 126) : Prop :=
  ∀ r : Fin 8, wordColumn leftAction rightAction (words d) (outputIndex q r) =
    candidate d (outputIndex q r)

def RowBlock (k : Fin 9) (q : Fin 126) : Prop :=
  ∀ r : Fin 8, combined k (outputIndex q r) =
    columnFromRows (outputIndex q r).val (rows k).toList

private theorem outputIndex_div_mod (j : Fin 1008) :
    outputIndex ⟨j.val / 8, by have := j.isLt; omega⟩
      ⟨j.val % 8, Nat.mod_lt _ (by decide)⟩ = j := by
  apply Fin.ext
  simp only [outputIndex]
  omega

theorem wordChecks_of_blocks (d : Fin 26) (h : ∀ q, WordBlock d q) : WordChecks d := by
  intro j
  have hj := h ⟨j.val / 8, by have := j.isLt; omega⟩
    ⟨j.val % 8, Nat.mod_lt _ (by decide)⟩
  simpa only [outputIndex_div_mod] using hj

theorem rowChecks_of_blocks (h : ∀ k q, RowBlock k q) : RowChecks := by
  intro k j
  have hj := h k ⟨j.val / 8, by have := j.isLt; omega⟩
    ⟨j.val % 8, Nat.mod_lt _ (by decide)⟩
  simpa only [outputIndex_div_mod] using hj

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns
