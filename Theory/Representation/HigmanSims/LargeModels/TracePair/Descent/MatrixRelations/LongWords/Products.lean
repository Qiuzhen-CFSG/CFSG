module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Data

import Mathlib.Data.List.GetD

/-!
# Numerical multiplication obligations for the long-word circuit

Each gate compares the product of two fixed earlier candidate matrices with a
fixed output. The final six outputs are the identity. The row-checking bridge
uses the proved packed arithmetic; it makes no claim that these checks hold.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
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
  | 2 => rows02
  | 3 => rows03
  | 4 => rows04
  | 5 => rows05
  | 6 => rows06
  | 7 => rows07
  | 8 => rows08
  | 9 => rows09
  | 10 => rows10
  | 11 => rows11
  | 12 => rows12
  | 13 => rows13
  | 14 => rows14
  | 15 => rows15
  | 16 => rows16
  | 17 => rows17
  | 18 => rows18
  | 19 => rows19
  | 20 => rows20
  | 21 => rows21
  | 23 => rows23
  | 24 => rows24
  | 25 => rows25
  | 26 => rows26
  | 28 => rows28
  | 29 => rows29
  | 30 => rows30
  | 31 => rows31
  | 32 => rows32
  | 33 => rows33
  | 36 => rows36
  | 37 => rows37
  | 38 => rows38
  | 39 => rows39
  | 41 => rows41
  | 42 => rows42
  | 43 => rows43
  | 44 => rows44
  | 45 => rows45
  | 46 => rows46
  | _ => identityRows

theorem rowsAt_length (i : ℕ) : (rowsAt i).length = 896 := by
  unfold rowsAt
  split
  · exact generatorRowsA_length
  · exact generatorRowsB_length
  · exact rows02_length
  · exact rows03_length
  · exact rows04_length
  · exact rows05_length
  · exact rows06_length
  · exact rows07_length
  · exact rows08_length
  · exact rows09_length
  · exact rows10_length
  · exact rows11_length
  · exact rows12_length
  · exact rows13_length
  · exact rows14_length
  · exact rows15_length
  · exact rows16_length
  · exact rows17_length
  · exact rows18_length
  · exact rows19_length
  · exact rows20_length
  · exact rows21_length
  · exact rows23_length
  · exact rows24_length
  · exact rows25_length
  · exact rows26_length
  · exact rows28_length
  · exact rows29_length
  · exact rows30_length
  · exact rows31_length
  · exact rows32_length
  · exact rows33_length
  · exact rows36_length
  · exact rows37_length
  · exact rows38_length
  · exact rows39_length
  · exact rows41_length
  · exact rows42_length
  · exact rows43_length
  · exact rows44_length
  · exact rows45_length
  · exact rows46_length
  · exact identityRows_length

def candidate (i : ℕ) : Matrix (Fin 896) (Fin 896) Four := Packed.eval 896 (rowsAt i)

def inputs (i : Fin 46) : ℕ × ℕ :=
  match i.val with
  | 0 => (1, 1)
  | 1 => (0, 2)
  | 2 => (0, 1)
  | 3 => (4, 3)
  | 4 => (4, 5)
  | 5 => (3, 1)
  | 6 => (3, 2)
  | 7 => (6, 8)
  | 8 => (7, 7)
  | 9 => (6, 2)
  | 10 => (9, 7)
  | 11 => (8, 3)
  | 12 => (6, 1)
  | 13 => (10, 3)
  | 14 => (6, 3)
  | 15 => (5, 2)
  | 16 => (12, 11)
  | 17 => (12, 13)
  | 18 => (14, 10)
  | 19 => (19, 20)
  | 20 => (21, 7)
  | 21 => (5, 15)
  | 22 => (15, 5)
  | 23 => (13, 13)
  | 24 => (23, 24)
  | 25 => (26, 25)
  | 26 => (16, 17)
  | 27 => (8, 5)
  | 28 => (3, 14)
  | 29 => (8, 7)
  | 30 => (28, 29)
  | 31 => (30, 31)
  | 32 => (32, 33)
  | 33 => (18, 18)
  | 34 => (6, 6)
  | 35 => (11, 16)
  | 36 => (3, 11)
  | 37 => (36, 37)
  | 38 => (39, 38)
  | 39 => (6, 5)
  | 40 => (5, 9)
  | 41 => (5, 1)
  | 42 => (17, 3)
  | 43 => (41, 42)
  | 44 => (43, 44)
  | _ => (45, 46)

/-- One concrete matrix-product identity, independent of every other gate. -/
def ProductCheck (i : Fin 46) : Prop :=
  candidate (inputs i).1 * candidate (inputs i).2 = candidate (i.val + 2)

/-- A pointwise packed certificate sufficient for a single product gate. -/
def RowChecks (i : Fin 46) : Prop := ∀ r : Fin 896,
  Packed.rowProduct ((rowsAt (inputs i).1).getD r.val (0, 0)) (rowsAt (inputs i).2) =
    (rowsAt (i.val + 2)).getD r.val (0, 0)

theorem productCheck_of_rows (i : Fin 46) (h : RowChecks i) : ProductCheck i :=
  Packed.eval_product 896 _ _ _ (rowsAt_length _) h

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
