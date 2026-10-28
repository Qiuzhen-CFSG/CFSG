module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFaithful
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryKernel

/-!
# Faithful escaping actions and component lifts on the Chapter 12 layer

The original chosen module supplies the E.6.1 and central-line normalizer
hypotheses, so the literal action of I on U/Z_S has kernel O₂(I).
The full natural-layer normalizer also preserves the escaping two-core R.
Consequently a component moved by R* cannot lie in M or in its action image.

The component-selection application uses the source Fitting-centralization
assertion explicitly. Its proof, the initial natural action, escaping
nonabelianness and the subsequent PSL₂ recognition remain with the final
assembly owner qt-d-1222-rankone-recognition-natural. No unconditional
6.1.27 conclusion is asserted here.

Source: Aschbacher–Smith, 6.1.21(5), 6.1.24 and the paragraph preceding
6.1.25, printed pp.675–677.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The escaping action factors faithfully through the actual two-core quotient. -/
theorem source_escape_action_kernel_eq_twoCore
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G)) :
    letI := h611.ZS_normal_in_escape_U
    (NaturalEscape.action (T : Subgroup G) L (wholeReduced T L)).ker =
      pCore 2 (Escape.I (T : Subgroup G) L (wholeReduced T L)) :=
  natural_escape_action_kernel_eq_twoCore h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) hI

/-- The original natural-layer normalizer preserves the escaping two-core. -/
theorem source_escape_layer_normalizer_normalizes_core
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L)) :
    normalizer (commutatorLayer T L : Set G) ≤
      normalizer (Escape.R (T : Subgroup G) L (wholeReduced T L) l : Set G) :=
  natural_escape_layer_normalizer_normalizes_core h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611) hnon hl hlout

/-- Select and lift an actual moved component, discharging the kernel,
nontrivial-action, quasisimplicity and local-escape inputs. Source 6.1.24(3)
remains the displayed premise of this conditional application. -/
theorem source_escape_moved_component_of_fitting_centralization
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hnon : ¬ Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L (wholeReduced T L))
    (hF : letI := h611.ZS_normal_in_escape_U
      let a := NaturalEscape.action (T : Subgroup G) L (wholeReduced T L)
      let A := ((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
        (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a
      A.subgroupOf a.range ≤ centralizer (fittingSubgroup a.range : Set a.range)) :
    letI := h611.ZS_normal_in_escape_U
    let a := NaturalEscape.action (T : Subgroup G) L (wholeReduced T L)
    let A := ((Escape.R (T : Subgroup G) L (wholeReduced T L) l).subgroupOf
      (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a
    ∃ K : Subgroup (Escape.I (T : Subgroup G) L (wholeReduced T L)),
      K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        IsComponent a.range (K.map a.rangeRestrict) ∧
          ⁅K.map a.rangeRestrict, A.subgroupOf a.range⁆ ≠ ⊥ ∧
            (¬ K.map (Escape.I (T : Subgroup G) L (wholeReduced T L)).subtype ≤
              normalizer (L : Set G)) ∧
            (¬ K.map a.rangeRestrict ≤ ((normalizer (L : Set G)).subgroupOf
              (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a.rangeRestrict) := by
  let := h611.ZS_normal_in_escape_U
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  have hNS := source_central_line_S_normalizer_le D h h611
  obtain ⟨K,hK,hq,hJ,hm⟩ := natural_escape_moved_component_of_fitting_centralization
    h611 hnatural hE (source_natural_layer_rank_bounds D h h611 hnatural).2.2
      hNS hnon hI hl hlout hF
  exact ⟨K,hK,hq,hJ,hm,
    natural_escape_moved_component_not_le h611 hnatural hE hNS hnon hl hlout K hJ hm,
    natural_escape_moved_component_image_not_le h611 hnatural hE hNS hnon hl hlout K hJ hm⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
