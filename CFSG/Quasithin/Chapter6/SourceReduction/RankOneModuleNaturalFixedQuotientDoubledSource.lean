module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDoubledOriginal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDoubledSelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDoubledExclusion

/-!
# Excluding the actual doubled-natural row in source 6.1.4

The full original doubled-natural model supplies a Sylow-invariant natural
summand and a complementary natural summand. Its actual centralizer quotient
has no near-offenders, so J₁(T) centralizes the moved layer. The original
rank-one theorem then contradicts the doubled-natural hyperplane bound.
No summand, TI, E.6.1 or Thompson-centralization premise remains.

This excludes the doubled row once the earlier source classifier produces
that actual model; the whole-module classification and orthogonal row remain.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The original small-generation hypotheses exclude the full doubled-natural
model without any additional invariant-summand or action premise. -/
theorem not_doubled_natural
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (F : BinaryField) (hF : F.degree = n) :
    ¬ IsConjugationModel L (layer L V) (repeated (linearNatural F 2) 2) := by
  intro hm
  obtain ⟨B₁,B₂,h₁,h₂,hjoin,_,hTB₁⟩ :=
    RankOneRecognition.original_doubled_natural_summands h F hF hm
  exact RankOneRecognition.original_natural_pair_false_of_thompson_centralizes
    h hout h₁ h₂ hjoin hTB₁
    ((h.rankOneInput hout).commutator_input.thompson_one_centralizes_of_doubled_natural
      F hF hm)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
