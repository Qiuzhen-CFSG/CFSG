module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometrySection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryG2

/-!
# The Chapter 12 reduction from the actual escaping natural section

The literal R/E section supplies n = 2, nonabelianness, a moving pair and
the index four. Thus the size bound and conditional 6.1.27 assembly need
only that section and the marked prime component in the escaping branch,
besides the original initial natural action and C_T(L) = 1.

The source section and prime component, as well as the initial 6.1.4–5
inputs, are still obligations of qt-d-1222-rankone-recognition-natural.
This does not assert the unconditional source_natural_reduction_of_many.
Source: Aschbacher–Smith, 6.1.21 and 6.1.25–27, printed pp.675–679.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Apply the exact core-index square identity on the original reduced layer. -/
theorem source_escape_core_index_square
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    ((Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G))) ^ 2 =
      (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
        (Escape.R (T : Subgroup G) L (wholeReduced T L) l) :=
  natural_escape_core_index_square h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) hnon hl hlout

/-- The actual section supplies every extra geometric and numerical premise. -/
theorem source_escape_geometry_of_natural_section
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hsection : Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L (wholeReduced T L) l)
      (Escape.R (T : Subgroup G) L (wholeReduced T L) l) (Escape.E (T : Subgroup G) L (wholeReduced T L) l)) :
    n = 2 ∧ Nonempty (NaturalEscape.Geometry (T : Subgroup G) L (wholeReduced T L)) :=
  natural_escape_geometry_of_natural_section h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hl hlout hsection

/-- The literal U/Z_S has order at most 256; no separate n=2, moving-pair or index-four input is required. -/
theorem source_escape_small_quotient_of_natural_section
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hsection : Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L (wholeReduced T L) l)
      (Escape.R (T : Subgroup G) L (wholeReduced T L) l) (Escape.E (T : Subgroup G) L (wholeReduced T L) l)) :
    letI := h611.ZS_normal_in_escape_U
    Nat.card (NaturalEscape.Quotient (T : Subgroup G) L (wholeReduced T L)) ≤ 256 := by
  let := h611.ZS_normal_in_escape_U
  obtain ⟨hn,⟨d⟩⟩ := source_escape_geometry_of_natural_section D h h611 hnatural hl hlout hsection
  exact d.quotient_card_le (hn ▸ hnatural) hCT

/-- Conditional 6.1.27 assembly with the numerical and geometric inputs discharged from the section. The section and prime-component source proofs remain with this task. -/
theorem source_natural_reduction_of_natural_sections
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hsections : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G) →
      ∃ l ∈ L, l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L) ∧
        Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L (wholeReduced T L) l)
          (Escape.R (T : Subgroup G) L (wholeReduced T L) l)
          (Escape.E (T : Subgroup G) L (wholeReduced T L) l))
    (hprime : letI := h611.ZS_normal_in_escape_U
      ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G) →
        NaturalEscape.PrimeComponent (T : Subgroup G) L (wholeReduced T L)) :
    Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n := by
  apply source_natural_reduction_of_natural_and_escape_order D h h611 hnatural hCT hout ?_ hprime
  intro hI
  obtain ⟨l,hl,hlout,hsection⟩ := hsections hI
  exact source_escape_small_quotient_of_natural_section D h h611 hnatural hCT hl hlout hsection

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
