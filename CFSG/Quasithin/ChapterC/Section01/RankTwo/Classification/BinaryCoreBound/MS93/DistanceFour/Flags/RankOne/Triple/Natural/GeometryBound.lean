module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Assembly

/-!
# The fixed-space index bound and a conditional comparison

`GeometryBound.Assembly` proves that the literal residual fixed quotient
has order at most four under the exact contrary triple hypothesis. Its
displacement and symmetry arguments use the actual local coset incidence.
The result is re-exported here as `flagFixedPreimage_relIndex_le_four`.

The edge quotient index four gives the arithmetic comparison below for any
fixed preimage containing `V_beta ⊓ Q_alpha`. This is only a conditional
comparison: the proposed intersection is all of `V_beta`, since the latter
already lies in `Q_alpha`. Under the contrary triple hypothesis on p.905,
that containment in the fixed preimage is therefore impossible.

`GeometryBound.Incidence` proves this obstruction. The conditional
comparison below is preserved as an API; the proved bound above uses
midpoint displacement instead of its intersection premise.

Source: Meierfrankenfeld--Stellmacher (1993), claim (1) in the proof of
(4.6.8), printed p.905.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

universe u
variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}

/-- The literal edge layer lies in the adjacent M-kernel. -/
theorem edgeRadius_le_Q_beta (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) :
    V R (beta R) ≤ Q R (beta R) := by
  have hab : Adjacent R (alpha R) (beta R) := base_adjacent R
  exact (edgeRadius_le_radius (alpha R) (beta R) rfl hab).trans
    ((V_le_Q geometry common.large_distance (alpha R) rfl).trans
      (Q_le_adjacent_h R (show color R (beta R) = true by rfl) hab))

/-- Conditional index comparison. Its intersection premise is incompatible
with the contrary triple hypothesis used on p.905. -/
theorem flagFixedPreimage_relIndex_le_four_of_intersection
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool)
    (hfixed : V R (beta R) ⊓ Q R (alpha R) ≤ flagFixedPreimage source i) :
    (flagFixedPreimage source i).relIndex (V R (beta R)) ≤ 4 := by
  have hab : Adjacent R (alpha R) (beta R) := base_adjacent R
  have hVQ := edgeRadius_le_Q_beta source geometry common
  have hidx := early.edge_Q_index (alpha R) (beta R) rfl hab
  have hne : (V R (beta R) ⊓ Q R (alpha R)).relIndex (V R (beta R)) ≠ 0 := by
    let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
    let : Finite (V R (beta R)) := Finite.of_injective
      (inclusion (edgeRadius_le_stabilizer geometry common.large_distance))
      (inclusion_injective _)
    exact Subgroup.index_ne_zero_of_finite
  have hle := relIndex_le_of_le_left hfixed hne
  rw [inf_relIndex_left] at hle
  exact (hle.trans (relIndex_le_of_le_right hVQ (by rw [hidx]; decide))).trans_eq hidx

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
