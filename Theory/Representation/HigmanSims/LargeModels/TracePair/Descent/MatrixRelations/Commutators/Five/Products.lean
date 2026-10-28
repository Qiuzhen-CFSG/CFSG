module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Data
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Streaming

/-!
# Eight finite products for the commutator fifth power

The first five gates identify the candidate C with A B⁴ A B. The last three
identify C², C⁴ and C⁴ C = I. Every gate concerns fixed literal matrices, so
the two batches can be checked independently. The assembly retains all eight
premises; the candidate generator and the representative row do not prove them.

Source: relator 4 of the unchanged `Descent/source/HSG1-P1.M`, after the inverse
substitution proved in `PositiveWords.lean`. All multiplication orders are
preserved. Candidate provenance and measurements are in `Five/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five
open Certificates

def identityRows : Packed.Mat := (List.range 896).map fun i => (2 ^ i, 0)

theorem identityRows_length : identityRows.length = 896 := by simp [identityRows]

theorem identityRows_eval : Packed.eval 896 identityRows = 1 := by
  funext i j
  simp [Packed.eval, identityRows, Packed.decode, Packed.Base.entry,
    Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit,
    Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

def rowsAt : ℕ → Packed.Mat
  | 0 => generatorRowsA
  | 1 => generatorRowsB
  | 2 => bTwoRows
  | 3 => bFourRows
  | 4 => abFourRows
  | 5 => abFourARows
  | 6 => commutatorRows
  | 7 => commutatorTwoRows
  | 8 => commutatorFourRows
  | _ => identityRows

theorem rowsAt_length (i : ℕ) : (rowsAt i).length = 896 := by
  unfold rowsAt
  split
  · exact generatorRowsA_length
  · exact generatorRowsB_length
  · exact bTwoRows_length
  · exact bFourRows_length
  · exact abFourRows_length
  · exact abFourARows_length
  · exact commutatorRows_length
  · exact commutatorTwoRows_length
  · exact commutatorFourRows_length
  · exact identityRows_length

def candidate (i : ℕ) : Matrix (Fin 896) (Fin 896) Four := Packed.eval 896 (rowsAt i)

def inputs (i : Fin 8) : ℕ × ℕ :=
  match i.val with
  | 0 => (1, 1)
  | 1 => (2, 2)
  | 2 => (0, 3)
  | 3 => (4, 0)
  | 4 => (5, 1)
  | 5 => (6, 6)
  | 6 => (7, 7)
  | _ => (8, 6)

/-- One numerical equality, with no interpretation of its inputs assumed. -/
def ProductCheck (i : Fin 8) : Prop :=
  candidate (inputs i).1 * candidate (inputs i).2 = candidate (i.val + 2)

def RowChecks (i : Fin 8) : Prop := ∀ r : Fin 896,
  Streaming.product ((rowsAt (inputs i).1).getD r.val (0, 0)) (rowsAt (inputs i).2) =
    (rowsAt (i.val + 2)).getD r.val (0, 0)

theorem productCheck_of_rows (i : Fin 8) (h : RowChecks i) : ProductCheck i :=
  Streaming.eval_product 896 _ _ _ (rowsAt_length _) h

/-- The first five finite products give the exact seven-letter commutator. -/
theorem commutator_value_of_checks
    (h : ∀ i : Fin 8, i.val < 5 → ProductCheck i) :
    Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB ^ 4 *
      Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB =
        Packed.eval 896 commutatorRows := by
  have h0 : candidate 1 * candidate 1 = candidate 2 := h 0 (by decide)
  have h1 : candidate 2 * candidate 2 = candidate 3 := h 1 (by decide)
  have h2 : candidate 0 * candidate 3 = candidate 4 := h 2 (by decide)
  have h3 : candidate 4 * candidate 0 = candidate 5 := h 3 (by decide)
  have h4 : candidate 5 * candidate 1 = candidate 6 := h 4 (by decide)
  change candidate 0 * candidate 1 ^ 4 * candidate 0 * candidate 1 = candidate 6
  have hb : candidate 1 ^ 4 = candidate 3 := by
    calc
      candidate 1 ^ 4 = (candidate 1 * candidate 1) * (candidate 1 * candidate 1) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = candidate 3 := by rw [h0, h1]
  rw [hb, h2, h3, h4]

/-- Three independent finite products prove the fifth power of the literal C. -/
theorem commutator_power_of_checks
    (h : ∀ i : Fin 8, 5 ≤ i.val → ProductCheck i) :
    (Packed.eval 896 commutatorRows) ^ 5 = 1 := by
  have h5 : candidate 6 * candidate 6 = candidate 7 := h 5 (by decide)
  have h6 : candidate 7 * candidate 7 = candidate 8 := h 6 (by decide)
  have h7 : candidate 8 * candidate 6 = candidate 9 := h 7 (by decide)
  have h9 : candidate 9 = 1 := identityRows_eval
  change candidate 6 ^ 5 = 1
  calc
    candidate 6 ^ 5 = ((candidate 6 * candidate 6) *
        (candidate 6 * candidate 6)) * candidate 6 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [h5, h6, h7, h9]

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five
