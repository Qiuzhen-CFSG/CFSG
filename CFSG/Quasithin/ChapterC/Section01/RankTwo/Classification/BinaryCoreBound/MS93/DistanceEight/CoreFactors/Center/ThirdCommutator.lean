module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.DerivedFirst
/-!
# The intrinsic third commutator of the distance-eight core

The source four-group H is exactly [[K,K],K] for the original commutator
core K. The first hat layer contains [K,K] and lies in [K,K]Z; commuting
with K kills Z and gives H by the established first-layer pairing.
Consequently H is characteristic in K, and every ambient normalizer of K
normalizes H. This supplies intrinsic invariance without identifying the
entire component-fixed part of the core center.

Source: Meierfrankenfeld--Stellmacher (1993), consequences of (4.5),
printed pp.895, 898--900, with the literal marked layers of CommonFacts.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open Higher
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The original four-group is the third commutator subgroup of the core. -/
theorem core_third_commutator_eq_H (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    ⁅⁅core R (alpha R),core R (alpha R)⁆,core R (alpha R)⁆ = H R (alpha R) := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  have hKA := Early.Orbit.Source.Complete.core_le_third_hat common earlier p
  have hD : ⁅core R (alpha R),core R (alpha R)⁆ ≤
      hatV R (alpha R) (p.walk.getVert 6) :=
    (commutator_mono hKA hKA).trans
      (le_sup_left.trans (OrbitGeometry.Source.commutator_layers common earlier p).2.le)
  have hfirst := first_le_core_derived_sup_Z common earlier p
  have hrow := first_core_commutator common earlier p
  have hsum := commutator_eq_of_centralizing_sup
    (sup_comm (Z R (alpha R)) ⁅core R (alpha R),core R (alpha R)⁆)
    (Quotients.FirstDirect.Z_centralizes_core common earlier)
    ((commutator_le_self (core R (alpha R))).trans (core R (alpha R)).le_normalizer)
  rw [commutator_comm] at hrow
  apply le_antisymm ((commutator_mono hD le_rfl).trans_eq hrow)
  rw [← hrow, commutator_comm _ (core R (alpha R))]
  exact (commutator_mono le_rfl hfirst).trans_eq (hsum.symm.trans (commutator_comm _ _))

/-- The source four-group is the third lower-central term of the intrinsic core. -/
theorem H_subgroupOf_core_eq_third_commutator (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    (H R (alpha R)).subgroupOf (core R (alpha R)) =
      ⁅_root_.commutator (core R (alpha R)), (⊤ : Subgroup (core R (alpha R)))⁆ := by
  have hH : H R (alpha R) ≤ core R (alpha R) := by
    rw [← core_third_commutator_eq_H common earlier]
    exact (commutator_mono (commutator_le_self _) le_rfl).trans (commutator_le_self _)
  apply map_injective (core R (alpha R)).subtype_injective
  rw [map_subgroupOf_eq_of_le hH, map_commutator, map_subtype_commutator,
    ← MonoidHom.range_eq_map, range_subtype, core_third_commutator_eq_H common earlier]

/-- Every automorphism of the core preserves the source four-group. -/
theorem H_characteristic_core (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    ((H R (alpha R)).subgroupOf (core R (alpha R))).Characteristic := by
  rw [H_subgroupOf_core_eq_third_commutator common earlier]
  infer_instance

/-- Any ambient element normalizing the core preserves the source four-group. -/
theorem normalizer_core_le_normalizer_H (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) :
    normalizer (core R (alpha R) : Set (FreeAmalgam R)) ≤
      normalizer (H R (alpha R) : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [← core_third_commutator_eq_H common earlier, map_commutator, map_commutator, hg]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
