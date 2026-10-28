module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryMultiplicity
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometrySection

/-!
# The natural escaping section from its marked index

The proved field-four projective recognition theorem constructs the natural
R/E action once the source parameter, nonabelianness and index four are
known. The E.6.1 and central-line normalizer hypotheses are discharged on
the original Chapter 12 reduced layer. The resulting literal section feeds
the order bound for U/Z_S and the conditional 6.1.27 assembly.

The initial natural action, the escaping numerical conclusions and the
PSL₂ prime component remain with qt-d-1222-rankone-recognition-natural.
No field-four parameter, nonabelianness or index bound is asserted from
the escaping hypothesis alone in this module.
Source: Aschbacher–Smith, 6.1.21, 6.1.25–27, pp.675–679, using G.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The common multiplicity and both quotient orders on the original layer. -/
theorem source_escape_four_multiplicity
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    ∃ s : ℕ,
      (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
        (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) =
          2 ^ (2 * s) ∧
      (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
        (Escape.R (T : Subgroup G) L (wholeReduced T L) l) = 2 ^ (4 * s) ∧
      Nat.card (Escape.U (T : Subgroup G) L (wholeReduced T L)) =
        2 ^ (2 * (s + 3)) * (commutatorLayer T L).relIndex
          (Escape.E (T : Subgroup G) L (wholeReduced T L) l) :=
  natural_escape_four_multiplicity h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) hnon hl hlout

/-- Construct the original natural section from its source numerical inputs. -/
theorem source_escape_section_of_index_four
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hindex : (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) = 4) :
    Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L (wholeReduced T L) l)
      (Escape.R (T : Subgroup G) L (wholeReduced T L) l)
      (Escape.E (T : Subgroup G) L (wholeReduced T L) l) :=
  natural_escape_section_of_index_four h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) hnon hl hlout hindex

/-- The order bound consumes the constructed action on the literal R/E. -/
theorem source_escape_small_quotient_of_index_four
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hindex : (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) = 4) :
    letI := h611.ZS_normal_in_escape_U
    Nat.card (NaturalEscape.Quotient (T : Subgroup G) L (wholeReduced T L)) ≤ 256 :=
  source_escape_small_quotient_of_natural_section D h h611 hnatural hCT hl hlout
    (source_escape_section_of_index_four D h h611 hnatural hnon hl hlout hindex)

/-- Conditional 6.1.27 using numerical escape data; no section model or
projective-recognition premise remains. Their source inputs stay with this owner. -/
theorem source_natural_reduction_of_escape_indices
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ}
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hindices : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G) →
      n = 2 ∧
      (¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
        centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) ∧
      ∃ l ∈ L, l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L) ∧
        (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
          (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓ centralizer (commutatorLayer T L : Set G)) = 4)
    (hprime : letI := h611.ZS_normal_in_escape_U
      ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G) →
        NaturalEscape.PrimeComponent (T : Subgroup G) L (wholeReduced T L)) :
    Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n := by
  apply source_natural_reduction_of_natural_and_escape_order D h h611 hnatural hCT hout ?_ hprime
  intro hI
  obtain ⟨hn,hnon,l,hl,hlout,hindex⟩ := hindices hI
  subst n
  exact source_escape_small_quotient_of_index_four D h h611 hnatural hCT hnon hl hlout hindex

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
