module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCoreAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryStrict

/-!
# Entry to the escaping component argument on the original Chapter 12 layer

The E.6.1 setup, natural-layer rank and central-line normalizer bound
supply the nontrivial elementary core image on the literal U/Z_S. The final
theorem selects the conjugator and retains E < R, the trivial two-core of
the actual I-action image, and its proper local subgroup. These are the
inputs preceding the component selection on printed p.677.

Initial naturalness, escaping nonabelianness and the subsequent component
selection and classification remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.22–25, printed pp.676–678.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original escaping two-core has nontrivial image on U/Z_S. -/
theorem source_escape_core_action_nontrivial
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    letI := h611.ZS_normal_in_escape_U
    ((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
      (Escape.I (T : Subgroup G) L (wholeReduced T L))).map
      (NaturalEscape.action (T : Subgroup G) L (wholeReduced T L)) ≠ ⊥ :=
  natural_escape_core_action_nontrivial h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hnon hI hl hlout

/-- The elementary action of the escaping core, on the original quotient. -/
theorem source_escape_core_action_elementary
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    letI := h611.ZS_normal_in_escape_U
    IsElementaryAbelian 2
      (((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
        (Escape.I (T : Subgroup G) L (wholeReduced T L))).map
        (NaturalEscape.action (T : Subgroup G) L (wholeReduced T L))) :=
  natural_escape_core_action_elementary h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) hnon hl hlout

/-- Select an actual conjugator and the nontrivial elementary core image
inside the reduced I-action. These are the entry data for source 6.1.24's
component argument; no component or numerical reduction is assumed. -/
theorem source_escape_core_action_setup
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G)) :
    letI := h611.ZS_normal_in_escape_U
    let a := NaturalEscape.action (T : Subgroup G) L (wholeReduced T L)
    pCore 2 a.range = ⊥ ∧
      ((normalizer (L : Set G)).subgroupOf
        (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a < a.range ∧
      ∃ l ∈ L, l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L) ∧
        Escape.E (T : Subgroup G) L (wholeReduced T L) l <
          Escape.R (T : Subgroup G) L (wholeReduced T L) l ∧
        IsElementaryAbelian 2
          (((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
            (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a) ∧
        ((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
          (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a ≠ ⊥ := by
  let := h611.ZS_normal_in_escape_U
  obtain ⟨l,hl,hlout⟩ := natural_escape_exists_line_mover h611 hnatural
  refine ⟨natural_escape_action_twoCore_eq_bot h611 hnatural,
    natural_escape_action_image_proper h611
      (source_natural_layer_hypothesisE61 D h h611 hnatural) hI,
    l,hl,hlout,source_escape_intersection_lt_core D h h611 hnatural hnon hI hl hlout,
    source_escape_core_action_elementary D h h611 hnatural hnon hl hlout,
    source_escape_core_action_nontrivial D h h611 hnatural hnon hI hl hlout⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
