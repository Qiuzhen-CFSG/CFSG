module

public import CFSG.Quasithin.ChapterA.Section02.OddLie
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.HigherClassical.OddSource

/-!
# Ternary degree-four center reductions in A.2.17

After O₃(L)=1 has been proved in the source argument, the actual PSL₄(3)
central quotient forces L to be simple. The unitary alternative currently
reduces to a five-primary center. The quotient model, oddness and core
hypothesis are exactly those of the degree-four step on printed p.39.

These are applications of the proved individual I.1 source deductions.
The full all-odd-prime step, including elimination of the remaining unitary
five-part, and the final A.2.17 assembly remain unfinished.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterA.Section02.HigherClassicalCenters

open CFSG.Quasithin.ChapterI.LieMultipliers.HigherClassical.OddSource

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

/-- The linear ternary branch of the source's assertion that G is simple. -/
theorem isSimpleGroup_of_isPSL_four_three
    (hodd : Odd (Nat.card (center L))) (hcore : pCore 3 L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 4 3) : IsSimpleGroup L := by
  have hz := center_eq_bot_of_isPSL_four_three hodd hcore hmodel
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans
    (QuotientGroup.quotientBot : L ⧸ (⊥ : Subgroup L) ≃* L)).symm.isSimpleGroup

/-- At p=3 only the five-part in the actual unitary alternative remains. -/
theorem ternary_degree_four_reduction
    (hodd : Odd (Nat.card (center L))) (hcore : pCore 3 L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 4 3 ∨
      ClassicalGroup.IsPSU (L ⧸ center L) 4 3) :
    IsSimpleGroup L ∨
      (ClassicalGroup.IsPSU (L ⧸ center L) 4 3 ∧ IsPGroup 5 (center L)) := by
  rcases hmodel with hlinear | hunitary
  · exact Or.inl (isSimpleGroup_of_isPSL_four_three hodd hcore hlinear)
  · exact Or.inr ⟨hunitary, center_isFiveGroup_of_isPSU_four_three hodd hcore hunitary⟩

end CFSG.Quasithin.ChapterA.Section02.HigherClassicalCenters
