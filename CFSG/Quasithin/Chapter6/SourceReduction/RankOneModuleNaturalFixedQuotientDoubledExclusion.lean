module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDoubled
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientRank

/-!
# The doubled-natural contradiction on the original moved layer

The original generation-one hypothesis and higher Thompson centralization
force global rank one, without TI. Two actual natural summands, the first
Sylow-invariant, force global rank greater than one. These incompatible
bounds exclude the doubled case with its original ambient witnesses.

The module decomposition and the higher Thompson centralization are the
remaining preceding steps of 6.1.4; they are not assumed consequences of
the whole source hypotheses here.

Source: Aschbacher–Smith, 6.1.3–4, printed pp.664–665.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

theorem original_natural_pair_false_of_thompson_centralizes
    {T : Sylow 2 G} {L M V B₁ B₂ : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (h₁ : IsNaturalModule L B₁ n) (h₂ : IsNaturalModule L B₂ n)
    (hjoin : layer L V = B₁ ⊔ B₂)
    (hTB₁ : (T : Subgroup G) ≤ normalizer (B₁ : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ centralizer (layer L V : Set G)) :
    False := by
  have hgt := original_natural_pair_one_lt_globalR h h₁ h₂ hjoin hTB₁
  rw [original_layer_rank_one_of_thompson_centralizes h hout hJ] at hgt
  exact (lt_irrefl (1 : ℕ∞)) hgt

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
