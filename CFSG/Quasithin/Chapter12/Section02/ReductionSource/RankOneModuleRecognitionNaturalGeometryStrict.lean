module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryStrict
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryMultiplicity

/-!
# Strictness of the escaping natural section on the Chapter 12 layer

The original E.6.1 setup, central-line normalizer bound and natural-layer
rank discharge the local premises of 6.1.22. Thus, once the earlier
nonabelianness is supplied, the literal intersection E is properly contained
in R = O₂(L₁). In field four this also makes the common natural multiplicity
strictly positive, as required before the component argument in 6.1.24–25.

The initial natural action, escaping nonabelianness, reduction to field four
and marked PSL₂ component remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.22–25, printed pp.676–678.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Source 6.1.22 on the original whole reduced layer. -/
theorem source_escape_intersection_lt_core
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    Escape.E (T : Subgroup G) L (wholeReduced T L) l <
      Escape.R (T : Subgroup G) L (wholeReduced T L) l :=
  natural_escape_intersection_lt_core h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hnon hI hl hlout

/-- The source nonzero multiplicity on the literal field-four section,
with both quotient indices and the same U order formula. -/
theorem source_escape_four_positive_multiplicity
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    ∃ s : ℕ, 0 < s ∧
      (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
        (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) =
          2 ^ (2 * s) ∧
      (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
        (Escape.R (T : Subgroup G) L (wholeReduced T L) l) = 2 ^ (4 * s) ∧
      Nat.card (Escape.U (T : Subgroup G) L (wholeReduced T L)) =
        2 ^ (2 * (s + 3)) * (commutatorLayer T L).relIndex
          (Escape.E (T : Subgroup G) L (wholeReduced T L) l) :=
  natural_escape_four_positive_multiplicity h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hnon hI hl hlout

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
