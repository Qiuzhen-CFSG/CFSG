module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Data
import Mathlib.Tactic.FinCases

/-! Exhaustive square-one coverage in the existing 16 × 8 × 8 Sylow enumeration. -/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open LocalStructure.SylowCore.FiniteBoundCertificate
private def SquareCoverage (a : Fin 16) : Prop :=
  ∀ (b c : Fin 8),
    (∀ p : Fin 3, perm (a,b,c) (perm (a,b,c) (p.castLE (by decide))) =
      p.castLE (by decide)) → vertex (code (a,b,c)) = (a,b,c)
private instance (a : Fin 16) : Decidable (SquareCoverage a) :=
  inferInstanceAs (Decidable (∀ (_b _c : Fin 8), _))
private theorem squareCoverage0 : SquareCoverage 0 := by decide +kernel
private theorem squareCoverage1 : SquareCoverage 1 := by decide +kernel
private theorem squareCoverage2 : SquareCoverage 2 := by decide +kernel
private theorem squareCoverage3 : SquareCoverage 3 := by decide +kernel
private theorem squareCoverage4 : SquareCoverage 4 := by decide +kernel
private theorem squareCoverage5 : SquareCoverage 5 := by decide +kernel
private theorem squareCoverage6 : SquareCoverage 6 := by decide +kernel
private theorem squareCoverage7 : SquareCoverage 7 := by decide +kernel
private theorem squareCoverage8 : SquareCoverage 8 := by decide +kernel
private theorem squareCoverage9 : SquareCoverage 9 := by decide +kernel
private theorem squareCoverage10 : SquareCoverage 10 := by decide +kernel
private theorem squareCoverage11 : SquareCoverage 11 := by decide +kernel
private theorem squareCoverage12 : SquareCoverage 12 := by decide +kernel
private theorem squareCoverage13 : SquareCoverage 13 := by decide +kernel
private theorem squareCoverage14 : SquareCoverage 14 := by decide +kernel
private theorem squareCoverage15 : SquareCoverage 15 := by decide +kernel

theorem square_coverage (i : Index)
    (h : ∀ p : Fin 3, perm i (perm i (p.castLE (by decide))) = p.castLE (by decide)) :
    vertex (code i) = i := by
  obtain ⟨a, b, c⟩ := i
  have hc : SquareCoverage a := by
    fin_cases a
    · exact squareCoverage0
    · exact squareCoverage1
    · exact squareCoverage2
    · exact squareCoverage3
    · exact squareCoverage4
    · exact squareCoverage5
    · exact squareCoverage6
    · exact squareCoverage7
    · exact squareCoverage8
    · exact squareCoverage9
    · exact squareCoverage10
    · exact squareCoverage11
    · exact squareCoverage12
    · exact squareCoverage13
    · exact squareCoverage14
    · exact squareCoverage15
  exact hc b c h

end Janko4.TwoRank.Finite
