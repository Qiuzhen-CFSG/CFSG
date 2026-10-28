module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.NormalWeights.PositiveData
import Mathlib.Tactic.FinCases

/-!
# Conjugacy coverage of all positive weights

For each positive nonidentity entry, `transport` gives a conjugator and one
of the 22 checked representatives. The finite tests prove the conjugacy on
all 24 points and equality of the assigned weight with the checked bound.
The identity is the separate, trivial inclusion into all 2048 masks.

The enumeration comes from the ATLAS-derived `SylowData` transversals.
The untrusted witness generator in `source/` is not part of the proof.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
open Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions

def transport (i : Index) : Index × Fin 22 :=
  match i.1.val, i.2.1.val, i.2.2.val with
  | 0, 0, 5 => ((0, 0, 0), 0)
  | 0, 0, 6 => ((0, 0, 0), 1)
  | 0, 0, 7 => ((0, 0, 1), 1)
  | 0, 1, 0 => ((0, 0, 0), 2)
  | 0, 1, 2 => ((0, 0, 0), 3)
  | 0, 2, 0 => ((0, 0, 0), 4)
  | 0, 2, 5 => ((0, 0, 1), 4)
  | 0, 2, 6 => ((0, 0, 0), 5)
  | 0, 2, 7 => ((0, 1, 0), 0)
  | 0, 3, 3 => ((0, 0, 4), 3)
  | 0, 3, 6 => ((0, 0, 4), 2)
  | 0, 4, 1 => ((0, 0, 1), 2)
  | 0, 4, 5 => ((0, 0, 1), 3)
  | 0, 5, 0 => ((0, 1, 0), 4)
  | 0, 5, 5 => ((0, 4, 0), 1)
  | 0, 5, 6 => ((0, 0, 0), 6)
  | 0, 5, 7 => ((0, 0, 0), 7)
  | 0, 6, 4 => ((0, 0, 3), 2)
  | 0, 6, 7 => ((0, 0, 3), 3)
  | 0, 7, 0 => ((0, 0, 1), 6)
  | 0, 7, 5 => ((0, 0, 1), 7)
  | 0, 7, 6 => ((0, 1, 0), 1)
  | 0, 7, 7 => ((0, 4, 0), 4)
  | 1, 3, 6 => ((0, 0, 0), 8)
  | 1, 4, 1 => ((0, 0, 0), 9)
  | 2, 2, 6 => ((0, 0, 6), 9)
  | 2, 5, 6 => ((0, 0, 6), 8)
  | 3, 3, 3 => ((0, 0, 1), 8)
  | 3, 4, 0 => ((0, 0, 1), 9)
  | 4, 0, 0 => ((1, 0, 0), 2)
  | 4, 0, 2 => ((0, 0, 0), 10)
  | 4, 1, 0 => ((0, 0, 0), 11)
  | 4, 1, 5 => ((6, 0, 0), 0)
  | 4, 1, 6 => ((2, 0, 0), 1)
  | 4, 1, 7 => ((2, 0, 1), 1)
  | 4, 2, 4 => ((0, 0, 1), 10)
  | 4, 2, 6 => ((1, 0, 1), 2)
  | 4, 3, 0 => ((0, 0, 0), 12)
  | 4, 3, 5 => ((1, 0, 1), 1)
  | 4, 3, 6 => ((1, 0, 0), 6)
  | 4, 3, 7 => ((0, 0, 0), 13)
  | 4, 4, 1 => ((1, 0, 0), 5)
  | 4, 4, 2 => ((8, 2, 6), 0)
  | 4, 4, 3 => ((0, 4, 0), 12)
  | 4, 4, 4 => ((0, 1, 0), 12)
  | 4, 5, 3 => ((0, 0, 4), 10)
  | 4, 5, 6 => ((1, 2, 2), 2)
  | 4, 6, 1 => ((1, 0, 0), 1)
  | 4, 6, 2 => ((0, 0, 1), 12)
  | 4, 6, 3 => ((0, 0, 1), 13)
  | 4, 6, 4 => ((1, 0, 1), 6)
  | 4, 7, 0 => ((9, 4, 1), 2)
  | 4, 7, 1 => ((0, 0, 3), 10)
  | 5, 2, 3 => ((0, 0, 3), 9)
  | 5, 5, 3 => ((0, 0, 3), 8)
  | 6, 0, 1 => ((0, 0, 0), 14)
  | 6, 1, 5 => ((0, 0, 0), 15)
  | 6, 2, 3 => ((0, 0, 0), 16)
  | 6, 3, 3 => ((0, 0, 0), 17)
  | 6, 3, 6 => ((5, 6, 1), 3)
  | 6, 4, 2 => ((0, 0, 1), 15)
  | 6, 5, 4 => ((0, 0, 0), 18)
  | 6, 6, 4 => ((9, 4, 1), 10)
  | 6, 6, 7 => ((0, 1, 2), 17)
  | 6, 7, 2 => ((0, 0, 1), 18)
  | 7, 1, 4 => ((0, 0, 2), 9)
  | 7, 6, 5 => ((0, 0, 2), 8)
  | 8, 0, 5 => ((0, 0, 2), 15)
  | 8, 1, 1 => ((0, 0, 2), 14)
  | 8, 2, 7 => ((0, 0, 5), 15)
  | 8, 3, 4 => ((0, 0, 5), 18)
  | 8, 4, 0 => ((0, 0, 2), 16)
  | 8, 5, 3 => ((0, 1, 0), 17)
  | 8, 5, 6 => ((5, 6, 1), 10)
  | 8, 6, 6 => ((0, 0, 2), 18)
  | 8, 7, 0 => ((9, 4, 1), 3)
  | 8, 7, 1 => ((0, 0, 2), 17)
  | 9, 0, 4 => ((0, 0, 4), 9)
  | 9, 7, 4 => ((0, 0, 4), 8)
  | 10, 0, 4 => ((0, 0, 4), 16)
  | 10, 1, 7 => ((0, 0, 4), 15)
  | 10, 2, 2 => ((0, 0, 4), 14)
  | 10, 3, 0 => ((3, 0, 0), 10)
  | 10, 3, 2 => ((0, 4, 7), 17)
  | 10, 4, 3 => ((0, 0, 6), 15)
  | 10, 5, 1 => ((0, 0, 4), 18)
  | 10, 6, 1 => ((1, 0, 0), 3)
  | 10, 6, 5 => ((0, 0, 4), 17)
  | 10, 7, 3 => ((0, 0, 6), 18)
  | 11, 0, 3 => ((0, 0, 3), 18)
  | 11, 1, 4 => ((0, 0, 3), 17)
  | 11, 1, 6 => ((3, 0, 0), 3)
  | 11, 2, 1 => ((0, 0, 7), 18)
  | 11, 3, 5 => ((0, 0, 7), 15)
  | 11, 4, 4 => ((1, 0, 0), 10)
  | 11, 4, 6 => ((0, 4, 4), 17)
  | 11, 5, 2 => ((0, 0, 3), 16)
  | 11, 6, 2 => ((0, 0, 3), 15)
  | 11, 7, 4 => ((0, 0, 3), 14)
  | 12, 1, 7 => ((0, 0, 5), 9)
  | 12, 6, 2 => ((0, 0, 5), 8)
  | 13, 0, 7 => ((0, 0, 7), 9)
  | 13, 7, 7 => ((0, 0, 7), 8)
  | 14, 0, 0 => ((3, 0, 0), 4)
  | 14, 0, 5 => ((3, 0, 1), 1)
  | 14, 0, 6 => ((1, 0, 0), 13)
  | 14, 0, 7 => ((0, 0, 0), 19)
  | 14, 1, 3 => ((3, 0, 0), 15)
  | 14, 2, 0 => ((3, 0, 0), 7)
  | 14, 2, 5 => ((0, 4, 0), 19)
  | 14, 2, 6 => ((8, 2, 6), 1)
  | 14, 2, 7 => ((5, 0, 1), 12)
  | 14, 3, 2 => ((5, 6, 1), 15)
  | 14, 4, 7 => ((7, 5, 0), 15)
  | 14, 5, 0 => ((1, 0, 0), 0)
  | 14, 5, 5 => ((0, 0, 0), 20)
  | 14, 5, 6 => ((3, 0, 0), 12)
  | 14, 5, 7 => ((5, 0, 1), 4)
  | 14, 6, 5 => ((9, 4, 1), 15)
  | 14, 7, 0 => ((5, 0, 0), 1)
  | 14, 7, 5 => ((6, 0, 1), 1)
  | 14, 7, 6 => ((2, 0, 1), 0)
  | 14, 7, 7 => ((0, 0, 0), 21)
  | 15, 0, 3 => ((12, 5, 0), 15)
  | 15, 1, 0 => ((5, 0, 0), 12)
  | 15, 1, 5 => ((8, 0, 1), 1)
  | 15, 1, 6 => ((1, 0, 0), 7)
  | 15, 1, 7 => ((0, 1, 0), 19)
  | 15, 2, 1 => ((1, 0, 0), 15)
  | 15, 3, 0 => ((1, 0, 1), 0)
  | 15, 3, 5 => ((0, 0, 1), 20)
  | 15, 3, 6 => ((5, 0, 0), 4)
  | 15, 3, 7 => ((3, 0, 1), 12)
  | 15, 4, 1 => ((3, 0, 0), 1)
  | 15, 4, 2 => ((3, 0, 1), 4)
  | 15, 4, 3 => ((0, 0, 1), 19)
  | 15, 4, 4 => ((3, 0, 0), 13)
  | 15, 5, 2 => ((13, 4, 1), 15)
  | 15, 6, 1 => ((2, 0, 0), 0)
  | 15, 6, 2 => ((0, 0, 1), 21)
  | 15, 6, 3 => ((5, 0, 1), 1)
  | 15, 6, 4 => ((6, 0, 0), 1)
  | 15, 7, 4 => ((2, 6, 1), 15)
  | _, _, _ => ((0, 0, 0), 0)

def PositiveTest (i : Index) : Prop :=
  0 < weight i → i = identityIndex ∨
    (Conjugates i (transport i).1 (representatives (transport i).2) ∧
      weight i = bounds (transport i).2)

instance (i : Index) : Decidable (PositiveTest i) := inferInstanceAs (Decidable (_ → _))

private theorem positiveTest0 : ∀ b c, PositiveTest (0, b, c) := by decide +kernel
private theorem positiveTest1 : ∀ b c, PositiveTest (1, b, c) := by decide +kernel
private theorem positiveTest2 : ∀ b c, PositiveTest (2, b, c) := by decide +kernel
private theorem positiveTest3 : ∀ b c, PositiveTest (3, b, c) := by decide +kernel
private theorem positiveTest4 : ∀ b c, PositiveTest (4, b, c) := by decide +kernel
private theorem positiveTest5 : ∀ b c, PositiveTest (5, b, c) := by decide +kernel
private theorem positiveTest6 : ∀ b c, PositiveTest (6, b, c) := by decide +kernel
private theorem positiveTest7 : ∀ b c, PositiveTest (7, b, c) := by decide +kernel
private theorem positiveTest8 : ∀ b c, PositiveTest (8, b, c) := by decide +kernel
private theorem positiveTest9 : ∀ b c, PositiveTest (9, b, c) := by decide +kernel
private theorem positiveTest10 : ∀ b c, PositiveTest (10, b, c) := by decide +kernel
private theorem positiveTest11 : ∀ b c, PositiveTest (11, b, c) := by decide +kernel
private theorem positiveTest12 : ∀ b c, PositiveTest (12, b, c) := by decide +kernel
private theorem positiveTest13 : ∀ b c, PositiveTest (13, b, c) := by decide +kernel
private theorem positiveTest14 : ∀ b c, PositiveTest (14, b, c) := by decide +kernel
private theorem positiveTest15 : ∀ b c, PositiveTest (15, b, c) := by decide +kernel

theorem positiveTest : ∀ i, PositiveTest i := by
  rintro ⟨a, b, c⟩
  fin_cases a
  · exact positiveTest0 b c
  · exact positiveTest1 b c
  · exact positiveTest2 b c
  · exact positiveTest3 b c
  · exact positiveTest4 b c
  · exact positiveTest5 b c
  · exact positiveTest6 b c
  · exact positiveTest7 b c
  · exact positiveTest8 b c
  · exact positiveTest9 b c
  · exact positiveTest10 b c
  · exact positiveTest11 b c
  · exact positiveTest12 b c
  · exact positiveTest13 b c
  · exact positiveTest14 b c
  · exact positiveTest15 b c

end Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
