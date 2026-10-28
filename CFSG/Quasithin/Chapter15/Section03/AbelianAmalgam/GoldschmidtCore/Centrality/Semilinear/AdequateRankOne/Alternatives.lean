module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.RankComparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ExhaustiveSource

/-!
# Corrected adequate alternatives at three-rank one

The actual alternating-six subgroup excludes the outer A₆–C₃ shape.
A triple alternating cover is excluded by its actual central quotient:
rank one gives cyclic Sylow three-subgroups, and cyclicity descends under
that quotient. All remaining group and action clauses are retained verbatim.
Thus a particular rank-one action has the full old alternative without
asserting either disputed module clause or a universal classifier conversion.

Source: Aschbacher–Smith, B.5.1/B.5.6 and the repaired 15.3.68 comparison,
printed pp.99–105 and 1154–1155; the projective-line convention is K.1.3.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.AdequateRankOne
open Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

private theorem irreducible_of_rank_one (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) {L H : Subgroup D}
    (h : ProjectiveLine.IrreducibleActionCase ρ L H) :
    IrreducibleActionCase ρ L H := by
  cases h with
  | linearTwo F hg e ho hq => exact .linearTwo F hg e ho hq
  | linearThree F hg e hq => exact .linearThree F hg e hq
  | symplectic F hl hg e hq => exact .symplectic F hl hg e hq
  | symplecticTwo e hq => exact .symplecticTwo e hq
  | g2 F hl hg e ho hq => exact .g2 F hl hg e ho hq
  | g2Two e ho hq => exact .g2Two e ho hq
  | symmetric n hn e ho hq => exact .symmetric n hn e ho hq
  | alternatingSix hg e ho hq => exact .alternatingSix hg e ho hq
  | alternatingSeven hg ht e hd ho hq => exact .alternatingSeven hg ht e hd ho hq
  | tripleSix hg c hq =>
    have hu := three_rank_section hr L (QuotientGroup.mk' (center L))
      (QuotientGroup.mk'_surjective (center L))
    rw [primeRank_equiv 3 c.quotientEquiv] at hu
    have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
    omega
  | binaryLinear d hd hg e hq => exact .binaryLinear d hd hg e hq
  | orthogonalSix hg ht e ho hq => exact .orthogonalSix hg ht e ho hq
  | symmetricEight ht e hq => exact .symmetricEight ht e hq
  | exteriorFive hg ht e hd ho hq => exact .exteriorFive hg ht e hd ho hq

private theorem quasisimple_case_of_rank_one (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) {L : Subgroup D} {s : MovedSection ρ L}
    (h : ProjectiveLine.QuasisimpleActionCase ρ L s) : QuasisimpleActionCase ρ L s := by
  cases h with
  | irreducible hi hf hir hc he =>
    exact .irreducible hi hf hir (irreducible_of_rank_one _ hr hc) he
  | doubleThree F ht e ho hq => exact .doubleThree F ht e ho hq
  | naturalDual d hd ht hn => exact .naturalDual d hd ht hn
  | repeatedNatural d r hd hp hb ht hn => exact .repeatedNatural d r hd hp hb ht hn

private def quasisimple_conclusion_of_rank_one (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) {L : Subgroup D}
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L) : QuasisimpleSourceConclusion ρ L :=
  { sectionData := c.sectionData
    fitting_eq := c.fitting_eq
    clause_one := quasisimple_case_of_rank_one ρ hr c.clause_one
    nonsplitting_iff := c.nonsplitting_iff
    clause_two := c.clause_two
    clause_three := c.clause_three
    clause_four := c.clause_four
    clause_five := c.clause_five
    clause_six := c.clause_six }

/-- On the original rank-one actor, the two corrected alternatives are
excluded by actual subgroup/section rank. Every other source clause survives. -/
theorem sourceAlternative_of_adequate_rank_one (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (h : ProjectiveLine.AdequateSourceAlternative ρ) :
    SourceAlternative ρ := by
  cases h with
  | trivial h => exact .trivial h
  | quasisimple hq c => exact .quasisimple hq (quasisimple_conclusion_of_rank_one ρ hr c)
  | symmetricThree c => exact .symmetricThree c
  | twoFactors c => exact .twoFactors c
  | outerSixThree c =>
    have hu := (primeRank_le_of_injective 3 c.first.subtype c.first.subtype_injective).trans hr
    rw [primeRank_equiv 3 c.firstEquiv] at hu
    have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
    omega
  | hyperplane c => exact .hyperplane c

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.AdequateRankOne
