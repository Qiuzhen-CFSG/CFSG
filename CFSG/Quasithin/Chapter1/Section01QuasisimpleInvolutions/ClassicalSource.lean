module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BenderSource
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.BinaryFour
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.AvailableCovers
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd

/-!
# Closing the alternating and odd-family overlaps in 1.1.5

The proved Bender branch supplies the genuine A5/PSL2(4) overlap and the
binary four-dimensional source theorem supplies A8. The marked A6 comparison
closes PSL2(9). Thus each entire alternating, odd-characteristic and higher
binary-linear Theorem C family now implies the six-constructor conclusion
on the original group and involution, without forwarded alternatives.

Source: Aschbacher--Smith 1.1.5(3), printed pp.501--503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- The full higher binary linear family, including its central-cover exclusion. -/
theorem MarkedInvolution.binary_source (d : MarkedInvolution α P) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (h : ClassicalGroup.IsPSL (L ⧸ center L) n 2) :
    ModelAction115 L α := by
  rcases hn with rfl | rfl
  · exact d.binaryFour_modelAction h
  · exact d.binaryFive_modelAction h

/-- All original alternating degrees, with the A5 and A8 overlaps discharged. -/
theorem MarkedInvolution.alternating_source (d : MarkedInvolution α P) {n : ℕ}
    (hn : n ≤ 8) (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    ModelAction115 L α := by
  rcases Alternating.small_quotient_modelAction d hn e with h | h | h
  · exact h
  · exact d.bender_source (.linear 2 (by decide) h)
  · exact d.binaryFour_modelAction h

/-- All odd-characteristic source families, including the genuine PSL2(9) overlap. -/
theorem MarkedInvolution.odd_source (d : MarkedInvolution α P)
    (h : ChapterA.Section02.IsTheoremCOddModel (L ⧸ center L)) : ModelAction115 L α := by
  rcases d.odd h with hc | hn
  · exact hc
  · exact Alternating.psl_nine d hn

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
