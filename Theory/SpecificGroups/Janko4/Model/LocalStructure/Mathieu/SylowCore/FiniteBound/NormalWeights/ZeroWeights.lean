module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.NormalWeights.Core
import Mathlib.Tactic.FinCases

/-!
# Excluding the zero-weight elements

An elementary two-subgroup contains only square-one elements. For each
remaining zero-weight involution, the table supplies a conjugate that fails
to commute with it. Normality puts that conjugate in the same subgroup,
contradicting commutativity. Three permutation points suffice for these
witnesses; full conjugacy is checked on all 24 points.

The witnesses are discovered from the literal ATLAS-derived `SylowData`
permutations and independently checked below. See `source/` for regeneration.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
open Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions

def badConjugate (i : Index) : Index × Index :=
  match i.1.val, i.2.1.val, i.2.2.val with
  | 0, 0, 1 => ((1, 0, 3), (11, 5, 0))
  | 0, 0, 2 => ((1, 0, 3), (6, 0, 0))
  | 0, 2, 3 => ((1, 0, 3), (10, 2, 0))
  | 0, 2, 4 => ((1, 0, 3), (8, 4, 1))
  | 1, 0, 0 => ((0, 0, 3), (9, 4, 6))
  | 1, 1, 6 => ((0, 0, 1), (3, 1, 3))
  | 1, 6, 1 => ((0, 0, 1), (3, 6, 0))
  | 1, 7, 0 => ((0, 0, 3), (9, 3, 2))
  | 2, 0, 6 => ((0, 0, 1), (5, 0, 3))
  | 2, 1, 0 => ((0, 0, 3), (7, 2, 2))
  | 2, 6, 4 => ((0, 0, 3), (7, 5, 2))
  | 2, 7, 6 => ((0, 0, 1), (5, 7, 3))
  | 3, 0, 1 => ((0, 0, 3), (2, 6, 4))
  | 3, 1, 3 => ((0, 0, 1), (1, 1, 6))
  | 3, 6, 0 => ((0, 0, 1), (1, 6, 1))
  | 3, 7, 1 => ((0, 0, 3), (2, 1, 0))
  | 4, 1, 1 => ((1, 0, 3), (10, 0, 6))
  | 4, 1, 2 => ((1, 0, 3), (8, 1, 0))
  | 4, 4, 0 => ((1, 0, 3), (11, 7, 6))
  | 4, 4, 5 => ((1, 0, 3), (6, 2, 6))
  | 5, 0, 3 => ((0, 0, 1), (2, 0, 6))
  | 5, 1, 1 => ((0, 0, 3), (1, 7, 0))
  | 5, 6, 7 => ((0, 0, 3), (1, 0, 0))
  | 5, 7, 3 => ((0, 0, 1), (2, 7, 6))
  | 6, 0, 0 => ((1, 0, 3), (0, 2, 4))
  | 6, 2, 6 => ((1, 0, 3), (4, 1, 2))
  | 7, 2, 2 => ((0, 0, 3), (13, 3, 5))
  | 7, 3, 4 => ((0, 0, 1), (12, 3, 7))
  | 7, 4, 5 => ((0, 0, 1), (12, 4, 2))
  | 7, 5, 2 => ((0, 0, 3), (13, 4, 3))
  | 8, 1, 0 => ((1, 0, 3), (4, 4, 5))
  | 8, 4, 1 => ((1, 0, 3), (0, 0, 2))
  | 9, 2, 4 => ((0, 0, 1), (13, 2, 7))
  | 9, 3, 2 => ((0, 0, 3), (12, 2, 5))
  | 9, 4, 6 => ((0, 0, 3), (12, 5, 5))
  | 9, 5, 4 => ((0, 0, 1), (13, 5, 7))
  | 10, 0, 6 => ((1, 0, 3), (0, 2, 3))
  | 10, 2, 0 => ((1, 0, 3), (4, 1, 1))
  | 11, 5, 0 => ((1, 0, 3), (4, 4, 0))
  | 11, 7, 6 => ((1, 0, 3), (0, 0, 1))
  | 12, 2, 5 => ((0, 0, 3), (5, 1, 1))
  | 12, 3, 7 => ((0, 0, 1), (7, 3, 4))
  | 12, 4, 2 => ((0, 0, 1), (7, 4, 5))
  | 12, 5, 5 => ((0, 0, 3), (5, 6, 7))
  | 13, 2, 7 => ((0, 0, 1), (9, 2, 4))
  | 13, 3, 5 => ((0, 0, 3), (3, 7, 1))
  | 13, 4, 3 => ((0, 0, 3), (3, 0, 1))
  | 13, 5, 7 => ((0, 0, 1), (9, 5, 4))
  | _, _, _ => ((0, 0, 0), (0, 0, 0))

def SquareTest (i : Index) : Prop :=
  ∀ p : Fin 3, perm i (perm i (p.castLE (by decide))) = p.castLE (by decide)

instance (i : Index) : Decidable (SquareTest i) := inferInstanceAs (Decidable (∀ _p : Fin 3, _))

def ZeroTest (i : Index) : Prop :=
  weight i = 0 → ¬SquareTest i ∨
    (Conjugates i (badConjugate i).1 (badConjugate i).2 ∧
      ∃ p : Fin 3, perm i (perm (badConjugate i).2 (p.castLE (by decide))) ≠
        perm (badConjugate i).2 (perm i (p.castLE (by decide))))

instance (i : Index) : Decidable (ZeroTest i) := inferInstanceAs (Decidable (_ → _))

private theorem zeroTest0 : ∀ b c, ZeroTest (0, b, c) := by decide +kernel
private theorem zeroTest1 : ∀ b c, ZeroTest (1, b, c) := by decide +kernel
private theorem zeroTest2 : ∀ b c, ZeroTest (2, b, c) := by decide +kernel
private theorem zeroTest3 : ∀ b c, ZeroTest (3, b, c) := by decide +kernel
private theorem zeroTest4 : ∀ b c, ZeroTest (4, b, c) := by decide +kernel
private theorem zeroTest5 : ∀ b c, ZeroTest (5, b, c) := by decide +kernel
private theorem zeroTest6 : ∀ b c, ZeroTest (6, b, c) := by decide +kernel
private theorem zeroTest7 : ∀ b c, ZeroTest (7, b, c) := by decide +kernel
private theorem zeroTest8 : ∀ b c, ZeroTest (8, b, c) := by decide +kernel
private theorem zeroTest9 : ∀ b c, ZeroTest (9, b, c) := by decide +kernel
private theorem zeroTest10 : ∀ b c, ZeroTest (10, b, c) := by decide +kernel
private theorem zeroTest11 : ∀ b c, ZeroTest (11, b, c) := by decide +kernel
private theorem zeroTest12 : ∀ b c, ZeroTest (12, b, c) := by decide +kernel
private theorem zeroTest13 : ∀ b c, ZeroTest (13, b, c) := by decide +kernel
private theorem zeroTest14 : ∀ b c, ZeroTest (14, b, c) := by decide +kernel
private theorem zeroTest15 : ∀ b c, ZeroTest (15, b, c) := by decide +kernel

theorem zeroTest : ∀ i, ZeroTest i := by
  rintro ⟨a, b, c⟩
  fin_cases a
  · exact zeroTest0 b c
  · exact zeroTest1 b c
  · exact zeroTest2 b c
  · exact zeroTest3 b c
  · exact zeroTest4 b c
  · exact zeroTest5 b c
  · exact zeroTest6 b c
  · exact zeroTest7 b c
  · exact zeroTest8 b c
  · exact zeroTest9 b c
  · exact zeroTest10 b c
  · exact zeroTest11 b c
  · exact zeroTest12 b c
  · exact zeroTest13 b c
  · exact zeroTest14 b c
  · exact zeroTest15 b c

theorem weight_pos_of_mem (B : Subgroup sylowCandidate) (hn : B.Normal)
    [IsElementaryAbelian 2 B] (i : Index) (hi : element i ∈ B) : 0 < weight i := by
  by_contra h
  have hz : weight i = 0 := Nat.eq_zero_of_not_pos h
  rcases zeroTest i hz with hs | ⟨hc, p, hp⟩
  · exact hs (fun p => square_point B i hi (p.castLE (by decide)))
  · exact hp (commute_point B i (badConjugate i).2 hi
      (mem_of_conjugates B hn i _ _ hi hc) (p.castLE (by decide)))

end Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
