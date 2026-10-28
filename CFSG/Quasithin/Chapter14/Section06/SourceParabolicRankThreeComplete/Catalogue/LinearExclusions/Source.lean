module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.Preparation
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.LinearExclusions.Rows

/-!
# The two higher linear exclusions under the original parabolic hypotheses

Preparation compares the central quotient of the literal C.2.7 star image
with that of the image of the same residual in the prime-to-three quotient.
That image is the whole generalized Fitting subgroup and satisfies one of
the full F.6.18 alternatives, with either local orientation. Its central
quotient cannot have order 20,160, excluding both SL₃(4) and SL₄(2) markings.

No preferred-centralizer, minimal-choice, block or extra classification
hypothesis is required. The catalogue assembly retains the independent
seven-letter recovery and subsequent module arguments.
Source: Aschbacher--Smith original 14.6.10(5), p.1029, C.2.7(3),
pp.145--147, and F.6.18, pp.309--310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterB.QuasisimpleSource LinearExclusions
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Exclude both higher linear star markings on every original generated
parabolic. This discharges the `hlinear` contract of the catalogue assembly. -/
theorem linear_exclusion_input :
    LinearExclusionInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI
  obtain ⟨S, _, halt, hfit, _, a, _⟩ :=
    compared hG T hempty hM hunique hmany hcard e hab H hH d I hI
  have hne : Nat.card (star T M Mc I d.H2 ⧸ center (star T M Mc I d.H2)) ≠ 20160 := by
    intro hc
    have he := (Nat.card_congr a.toEquiv).symm.trans hc
    rw [hfit] at he
    exact halt.elim (fun h => source_not_central_card_20160 h he)
      (fun h => source_not_central_card_20160 h he)
  constructor
  · intro F hF hb
    obtain ⟨b⟩ := hb
    apply hne
    exact linearThree_central_card b (by rw [F.card_eq,hF]; norm_num)
  · intro hb
    obtain ⟨b⟩ := hb
    apply hne
    exact linearFour_central_card b (by simp)

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue
