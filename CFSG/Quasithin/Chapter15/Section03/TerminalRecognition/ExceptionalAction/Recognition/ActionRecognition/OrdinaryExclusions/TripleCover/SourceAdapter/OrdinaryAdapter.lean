module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceClassifications
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate

/-!
# Preserve the ordinary FF cases after excluding a cubic cover by order

The projective-line correction changes just the triple-six branch. When 1080
does not divide the actual actor order, that branch is impossible. All other
clauses therefore transport literally to the existing ordinary exclusions.
The separate outer A6--C3 group shape also contains a subgroup of order 1080.
No legacy triple-six offender assertion or fixed-space splitting is inferred.

Source: B.5.1/B.5.6 and the ordinary full quotients in the final proof of
15.3.1, printed pp.99,105,1155. The ordinary actor is a subgroup of the
full S6, S7 or G2(2) quotient, whose order is not divisible by 1080.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W}

/-- Both cubic-cover invariants refer to the actual subgroup L. -/
theorem projectiveLine_tripleSix_card {L : Subgroup D}
    (a : ProjectiveLine.TripleSixAction ρ L) : Nat.card L = 1080 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L),
    Nat.card_congr a.quotientEquiv.toEquiv, Nat.card_congr a.centerEquiv.toEquiv,
    nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The order obstruction removes only the corrected triple-six constructor. -/
theorem irreducible_of_not1080 (hD : ¬ 1080 ∣ Nat.card D) {L I : Subgroup D}
    (h : ProjectiveLine.IrreducibleActionCase ρ L I) :
    IrreducibleActionCase ρ L I := by
  cases h with
  | linearTwo F hg e ho hr => exact .linearTwo F hg e ho hr
  | linearThree F hg e hr => exact .linearThree F hg e hr
  | symplectic F hl hg e hr => exact .symplectic F hl hg e hr
  | symplecticTwo e hr => exact .symplecticTwo e hr
  | g2 F hl hg e ho hr => exact .g2 F hl hg e ho hr
  | g2Two e ho hr => exact .g2Two e ho hr
  | symmetric n hn e ho hr => exact .symmetric n hn e ho hr
  | alternatingSix hg e ho hr => exact .alternatingSix hg e ho hr
  | alternatingSeven hg ht e hd ho hr => exact .alternatingSeven hg ht e hd ho hr
  | tripleSix hg a hr =>
      exfalso
      apply hD
      have hd := L.card_subgroup_dvd_card
      rwa [projectiveLine_tripleSix_card a] at hd
  | binaryLinear n hn hg e hr => exact .binaryLinear n hn hg e hr
  | orthogonalSix hg ht e ho hr => exact .orthogonalSix hg ht e ho hr
  | symmetricEight ht e hr => exact .symmetricEight ht e hr
  | exteriorFive hg ht e hd ho hr => exact .exteriorFive hg ht e hd ho hr

/-- All six source clauses survive unchanged, on the identical moved section. -/
noncomputable def quasisimple_of_not1080 (hD : ¬ 1080 ∣ Nat.card D)
    {L : Subgroup D} (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L) :
    QuasisimpleSourceConclusion ρ L where
  sectionData := c.sectionData
  fitting_eq := c.fitting_eq
  clause_one := by
    cases c.clause_one with
    | irreducible hp hf hi hs he =>
        exact .irreducible hp hf hi (irreducible_of_not1080 hD hs) he
    | doubleThree F ht e ho hr => exact .doubleThree F ht e ho hr
    | naturalDual n hn ht h => exact .naturalDual n hn ht h
    | repeatedNatural n r hn hr hb ht h => exact .repeatedNatural n r hn hr hb ht h
  nonsplitting_iff := c.nonsplitting_iff
  clause_two := c.clause_two
  clause_three := c.clause_three
  clause_four := c.clause_four
  clause_five := c.clause_five
  clause_six := c.clause_six

/-- The source outer group has an actual A6 times C3 subgroup of order 1080. -/
theorem outerShape_dvd (c : ChapterB.OuterSixThreeShape D) : 1080 ∣ Nat.card D := by
  have hP : Nat.card (c.first ⊔ c.second : Subgroup D) = 1080 := by
    rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
      Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd := (c.first ⊔ c.second).card_subgroup_dvd_card
  rwa [hP] at hd

/-- Branch-specific transport. It proves no unrestricted legacy classification. -/
theorem alternative_of_not1080 (hD : ¬ 1080 ∣ Nat.card D)
    (h : Intersection.SourceFFAlternative ρ) : SourceAlternative ρ := by
  rcases h with h | ho
  · cases h with
    | trivial ht => exact .trivial ht
    | quasisimple hq c => exact .quasisimple hq (quasisimple_of_not1080 hD c)
    | symmetricThree c => exact .symmetricThree c
    | twoFactors c => exact .twoFactors c
    | outerSixThree c => exact .outerSixThree c
    | hyperplane c => exact .hyperplane c
  · obtain ⟨c⟩ := ho
    exact (hD (outerShape_dvd c)).elim

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter
