module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.Paths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.ContradictionGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.ContradictionIndices

/-!
# The paired critical-commutator calculation at the end of MS93 (5.11)

The actual overlapping critical paths give the paired commutators R₄ and R₆.
Both centralize V_(alpha'-4), using exact endpoint distances. The literal
radius-index factorization then gives the two alternatives of the final
paragraph, once its >16 radius bound is proved by the earlier part of (5.11).
This module proves this calculation, not that radius bound or b=4.

Source: MS93 (5.11), printed p924. We use the paired critical endpoints of
p922 explicitly. The fixed endpoint printed in p924's R-definition does
not justify the critical-distance containments used in the argument.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

/-- The two actual paired critical commutators centralize the original
radius at the twice-shifted endpoint. -/
theorem paired_critical_commutators_centralize_radius
    (hb : 4 < geometry.b R)
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1))) :
    ⁅⁅Z R (s 2).first,Z R (s 2).last⁆ ⊔
      ⁅Z R (s 3).first,Z R (s 3).last⁆,V R (s 2).last⁆ = ⊥ := by
  apply two_critical_commutators_centralize_radius geometry hb
    (s 2).path (s 3).path (s 2).path.end_color (by simp)
  exact (shifted_last_distance Chosen s hs 2 1 (by omega)).le

variable [Finite M]

/-- The literal final-paragraph split is compatible with those same
commutators and the same radius group. The large radius bound remains explicit. -/
theorem radius_split_on_chosen_paths
    (hb : 4 < geometry.b R)
    (Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ n, BackwardLink geometry Chosen (s n) (s (n+1)))
    (hlarge : 16 < (Q R (s 2).first).relIndex (V R (s 2).last)) :
    (4 < (Q R (s 1).first).relIndex (V R (s 2).last) ∨
      4 < (Q R (s 2).first).relIndex (V R (s 2).last ⊓ Q R (s 1).first)) ∧
    ⁅⁅Z R (s 2).first,Z R (s 2).last⁆ ⊔
      ⁅Z R (s 3).first,Z R (s 3).last⁆,V R (s 2).last⁆ = ⊥ :=
  ⟨radius_index_split geometry (by omega) (s 2).path.end_color hlarge,
    paired_critical_commutators_centralize_radius hb Chosen s hs⟩

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
