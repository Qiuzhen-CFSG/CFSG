module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Reductions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient

/-!
# The literal X quotient and its naturality reduction

The early radius square and commutator bounds make X/Z_alpha elementary.
Its full actor normalizes both subgroups, while the local kernel fixes the
quotient because X lies in U. Conjugation transports both residual
conventions through the actual inclusion of the local actor.

The final theorem constructs the two surjective maps, coordinate kernel,
exact actor kernel and ambient action equation once the source order bound
and nonzero residual action are supplied. Those two premises remain
obligations of the source naturality assembly; they are not asserted here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), printed p.907; the early radius facts are on pp.897--905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] {L R : Subgroup M}

namespace CoreNaturality

/-- Conjugating the original full actor preserves its prime-to-two residual. -/
theorem actor_primeToResidual [Finite M] (source : LocalSource L R) (j : Bool) (d : M) :
    primeToResidual 2 (localFlagActor source j d) = ⊤ := by
  let e : flagParabolic source j ≃* localFlagActor source j d :=
    (MulAut.conj (embedM R d)).subgroupMap (flagParabolic source j)
  rw [← map_primeToResidual (p := 2) e, flagParabolic_primeToResidual source j,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]

/-- The tilded subgroup is the image of the actual two-residual of the full
conjugated actor, retaining the original ambient inclusion. -/
theorem residual_eq [Finite M] (source : LocalSource L R) (j : Bool) (d : M) :
    localFlagResidual source j d =
      (pResidual 2 (localFlagActor source j d)).map (localFlagActor source j d).subtype := by
  let e : flagParabolic source j ≃* localFlagActor source j d :=
    (MulAut.conj (embedM R d)).subgroupMap (flagParabolic source j)
  rw [← map_pResidual 2 e, Subgroup.map_map]
  unfold localFlagResidual localConjugate
  rw [flagResidual_eq, Subgroup.map_map]
  rfl

/-- The already constructed U-layer makes Q act trivially on the literal X quotient. -/
theorem X_kernel_commutator_le (source : LocalSource L R) [Finite M] (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d : M) :
    ⁅X source i d, localFlagKernel source (!i) d⁆ ≤ Z R (alpha R) :=
  (commutator_mono (X_le_second source geometry hlarge i d) le_rfl).trans
    (Incident.secondFlagLayer_commutator_le_Z source geometry hlarge i d)

/-- Normality is relative to X, not to the free amalgam. -/
theorem denominator_normal [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d : M) :
    ((Z R (alpha R)).subgroupOf (X source i d)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (((X_le_D source geometry hlarge i d).trans (D_le_Y source i d)).trans
      ((Y_le_radius source i d).trans
        ((geometry.V_local _ rfl hlarge).trans (Z_normalized R _))))

/-- The literal X/Z_alpha is elementary already from the early radius facts.
No naturality, dimension, or residual nonvanishing is assumed. -/
theorem quotient_elementary [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (d : M) :
    letI := denominator_normal source geometry common.large_distance i d
    IsElementaryAbelian 2 (X source i d ⧸ (Z R (alpha R)).subgroupOf (X source i d)) := by
  let := denominator_normal source geometry common.large_distance i d
  let H := X source i d
  let N := (Z R (alpha R)).subgroupOf H
  have hH : H ≤ V R (alpha R) :=
    ((X_le_D source geometry common.large_distance i d).trans (D_le_Y source i d)).trans
      (Y_le_radius source i d)
  have hderived : _root_.commutator H ≤ N := by
    intro x hx
    have hh := mem_map_of_mem H.subtype hx
    rw [map_subtype_commutator] at hh
    exact ((commutator_mono hH (hH.trans (V_le_Q geometry common.large_distance _ rfl))).trans
      (early.commutator_le_Z _ rfl)) hh
  let : IsMulCommutative (H ⧸ N) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hderived
  refine { exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Propagation.radius_square_mem_Z common early ⟨y, hH y.property⟩

end CoreNaturality

/-- Construct both onto natural-factor maps and the exact full-actor kernel
from the two remaining source calculations: size and residual movement.
This is a conditional assembly lemma, not the completed p.907 assertion. -/
theorem coreNaturality_of_index_and_movement [Finite M]
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (d : M) (moving : MovingFactor source i d)
    (hcard : (Z R (alpha R)).relIndex (X source i d) ≤ 4)
    (hmove : ¬ ⁅X source i d, localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    Nonempty (XFactor source i d) := by
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let P := localFlagActor source (!i) d
  let H := X source i d
  let : Finite P := Finite.of_injective
    (inclusion (localFlagActor_le_stabilizer source (!i) d)) (inclusion_injective _)
  have hH : H ≤ stabilizer R (alpha R) :=
    (((X_le_D source geometry common.large_distance i d).trans (D_le_Y source i d)).trans
      (Y_le_radius source i d)).trans (geometry.V_local _ rfl common.large_distance)
  let : Finite H := Finite.of_injective (inclusion hH) (inclusion_injective _)
  have hm : ¬ ⁅H, (pResidual 2 P).map P.subtype⁆ ≤ Z R (alpha R) := by
    rwa [← CoreNaturality.residual_eq source (!i) d]
  exact CoreNaturality.markedFactor_of_elementary_quotient P H (Z R (alpha R))
    (localFlagKernel source (!i) d)
    (X_normalized source geometry common.large_distance i d)
    ((localFlagActor_le_stabilizer source (!i) d).trans (Z_normalized R _))
    (CoreNaturality.denominator_normal source geometry common.large_distance i d)
    (CoreNaturality.quotient_elementary source geometry common early i d)
    (CoreNaturality.actor_primeToResidual source (!i) d) hm hcard
    (CoreNaturality.X_kernel_commutator_le source geometry common.large_distance i d)
    moving.val.projection moving.val.surjective moving.property

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
