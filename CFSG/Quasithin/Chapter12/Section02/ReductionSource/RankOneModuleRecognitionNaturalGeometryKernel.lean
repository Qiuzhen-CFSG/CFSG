module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryCoreAction

/-!
# Exact core kernels on the original Chapter 12 layer

The actual action of R on U/Z_S has kernel C_U(V_L), and its image has
order |C_U(V_L):E|. The original chosen-module hypotheses discharge the
E.6.1 and central-line normalizer inputs. In field four, the source bound
|R*| ≤ 4 therefore yields the marked index four, the natural R/E section,
and the terminal order bound on the literal U/Z_S.

The final conditional application replaces the unexplained marked index
by the bound on the original core-action image. Initial naturalness,
escaping nonabelianness, n = 2, that image bound, and the PSL₂ prime
component remain obligations of qt-d-1222-rankone-recognition-natural.
This module does not assert the unconditional 6.1.27 conclusion.
Source: Aschbacher–Smith, 6.1.24(1–2), 6.1.25(3), 6.1.26–27, pp.676–679.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Source 6.1.24(1) on the original commutator layer and quotient action. -/
theorem source_escape_core_action_kernel
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    letI := h611.ZS_normal_in_escape_U
    (Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
      (Escape.I (T : Subgroup G) L (wholeReduced T L)) ⊓
        (NaturalEscape.action (T : Subgroup G) L (wholeReduced T L)).ker =
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓
        centralizer (commutatorLayer T L : Set G)).subgroupOf
          (Escape.I (T : Subgroup G) L (wholeReduced T L)) :=
  natural_escape_core_action_kernel h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) hnon hl hlout

/-- The actual core-image order equals the marked index on the same layer. -/
theorem source_escape_core_action_card
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    letI := h611.ZS_normal_in_escape_U
    Nat.card (((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
      (Escape.I (T : Subgroup G) L (wholeReduced T L))).map
        (NaturalEscape.action (T : Subgroup G) L (wholeReduced T L))) =
      (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
        (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓
          centralizer (commutatorLayer T L : Set G)) :=
  natural_escape_core_action_card h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) hnon hl hlout

/-- A core image of order at most four forces the source marked index. -/
theorem source_escape_index_four_of_small_core_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hsmall : letI := h611.ZS_normal_in_escape_U
      Nat.card (((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
        (Escape.I (T : Subgroup G) L (wholeReduced T L))).map
          (NaturalEscape.action (T : Subgroup G) L (wholeReduced T L))) ≤ 4) :
    (Escape.E (T : Subgroup G) L (wholeReduced T L) l).relIndex
      (Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓
        centralizer (commutatorLayer T L : Set G)) = 4 :=
  natural_escape_index_four_of_small_core_action h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hnon hI hl hlout hsmall

/-- Apply the constructed natural section to the terminal quotient order bound. -/
theorem source_escape_small_quotient_of_small_core_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) 2)
    (hnatural : IsNaturalModule L (commutatorLayer T L) 2)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hsmall : letI := h611.ZS_normal_in_escape_U
      Nat.card (((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
        (Escape.I (T : Subgroup G) L (wholeReduced T L))).map
          (NaturalEscape.action (T : Subgroup G) L (wholeReduced T L))) ≤ 4) :
    letI := h611.ZS_normal_in_escape_U
    Nat.card (NaturalEscape.Quotient (T : Subgroup G) L (wholeReduced T L)) ≤ 256 :=
  source_escape_small_quotient_of_index_four D h h611 hnatural hCT hnon hl hlout
    (source_escape_index_four_of_small_core_action D h h611 hnatural hnon hI hl hlout hsmall)

/-- Conditional 6.1.27 from the core-image bound, with the marked index
and natural-section premises discharged on the original quotient. -/
theorem source_natural_reduction_of_small_core_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hsmall : letI := h611.ZS_normal_in_escape_U
      ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G) →
      n = 2 ∧
      (¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
        centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) ∧
      ∃ l ∈ L, l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L) ∧
        Nat.card (((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
          (Escape.I (T : Subgroup G) L (wholeReduced T L))).map
            (NaturalEscape.action (T : Subgroup G) L (wholeReduced T L))) ≤ 4)
    (hprime : letI := h611.ZS_normal_in_escape_U
      ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G) →
        NaturalEscape.PrimeComponent (T : Subgroup G) L (wholeReduced T L)) :
    Conclusion6127 (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n := by
  let := h611.ZS_normal_in_escape_U
  apply source_natural_reduction_of_escape_indices D h h611 hnatural hCT hout ?_ hprime
  intro hI
  obtain ⟨hn,hnon,l,hl,hlout,hbound⟩ := hsmall hI
  subst n
  exact ⟨rfl,hnon,l,hl,hlout,
    source_escape_index_four_of_small_core_action D h h611 hnatural hnon hI hl hlout hbound⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
