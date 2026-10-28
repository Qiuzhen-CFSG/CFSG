module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNatural

/-!
# The source natural reduction on the original Chapter 12 reduced layer

The Chapter 6 assembly is applied to the literal whole reduced subgroup
R₂(LT), with M = N_G(L). Its marked escaping quotient, natural action and
weak closures are preserved. Three earlier source inputs remain explicit:
6.1.6, the contained case of 6.1.15, and the escaping geometry 6.1.17--25.
Their independent producers must discharge these inputs before the
unconditional `source_natural_reduction_of_many` can be exported.

Source: Aschbacher--Smith, 6.1.27 and its application in 12.2.2(3d),
printed pp.679 and 795.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}

/-- Conditional assembly on [R₂(LT),L]. The earlier source inputs here
are the remaining obligations of the natural-reduction assembly owner. -/
theorem source_natural_reduction_of_source_branches
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hcontained :
      centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      Chapter6.Source.RankOneRecognition.ContainedAlternative (T : Subgroup G) L
        (normalizer (L : Set G)) (wholeReduced T L) n)
    (hescape : letI := h611.ZS_normal_in_escape_U
      ¬ centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      Chapter6.Source.RankOneRecognition.EscapingAlternative
        (T : Subgroup G) L (wholeReduced T L) n) :
    Chapter6.Source.Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n :=
  Chapter6.Source.RankOneRecognition.conclusion6127_of_source_branches
    h611 hnatural hCT hcontained hescape

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
