module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.EightGeometry

/-!
# Fusion at the original ambient group and Sylow subgroup: Complete

These are ambient-local versions of the existing source fusion proofs. Only
the structural premise changes: each use is at the original G,T,L,V. The
literal module actions, quotient maps, point Sylow subgroups and conjugators
are preserved. The universal APIs remain available in their original modules.

Source: Aschbacher–Smith, 12.2.16, printed pp.799–800; the reducible
normalizer argument uses 3.3.1 and B.5.1 as in the original proofs.
-/

/- Adapted from FusionComplete. -/
section
public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

public theorem reducible_of_module_alternatives_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D) (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V) := by
  have hNT := FusionReducibleNormalizer.sylow_normalizer_le_of_module_alternatives_at
    h D structural hnone hne rows
  exact reducible_of_geometric_rows_at h D structural hnone rows hne
    (alternating_of_sylow_normalizer_at h D structural hnone hne hNT)
    (globalTI_of_g2_row_at h D structural hnone hNT hne)

public theorem globalTI_of_module_alternatives_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D) : IsTISubgroup V :=
  globalTI_of_row_reductions_of_eight_geometry_at h D structural hnone
    (globalTI_of_fixedFree_module_alternatives_at h D structural hnone rows)
    (reducible_of_module_alternatives_at h D structural hnone rows)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end
