module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryCore

/-!
# The actual Chapter 12 escaping action image

On the original whole reduced layer, the I-action on U/Z_S has trivial
two-core, and the image of M ∩ I is proper when I escapes M. The source
E.6.1 normalizer bound is discharged using the chosen-module construction.
These are the faithful-action facts used before component selection in
6.1.25; they neither select that component nor prove its PSL₂ model.

The initial natural action and component selection remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.24(4) and the following paragraph,
printed pp.676–677.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The reducedness and proper local image of the literal quotient action. -/
theorem source_escape_reduced_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G)) :
    letI := h611.ZS_normal_in_escape_U
    let a := NaturalEscape.action (T : Subgroup G) L (wholeReduced T L)
    pCore 2 a.range = ⊥ ∧
      ((normalizer (L : Set G)).subgroupOf
        (Escape.I (T : Subgroup G) L (wholeReduced T L))).map a < a.range :=
  ⟨natural_escape_action_twoCore_eq_bot h611 hnatural,
    natural_escape_action_image_proper h611
      (source_natural_layer_hypothesisE61 D h h611 hnatural) hI⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
