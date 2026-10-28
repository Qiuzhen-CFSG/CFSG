module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.ParabolicGeometry.Reduction

/-!
# The edge star and fixed elements of the full starred quotient

The actual edge star lies in the elementary radius layer at beta, so the
supplied triple bound makes it fixed by the selected residual modulo Z.
Its stabilizer span is VStar. The identity VStar intersection B = Z says
that VStar/Z has no component-fixed elements, and the noncentral derived
subgroup forces the original edge star to be nonzero modulo Z.

These are group-level inputs to the remaining fixed-element transfer into
core/U; that transfer is not asserted by this module.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.10)--(4.6.11), pp.908--909.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

omit [Finite M] in
/-- The source edge star is a subgroup of the actual holomorph radius layer. -/
theorem edgeStar_le_edgeRadius :
    edgeStar R geometry (alpha R) (beta R) ≤ V R (beta R) := by
  rw [Flags.RankOne.V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact le_iSup_of_le t (le_iSup_of_le ht.2 le_rfl)

include common radius in
/-- The selected rank-one residual fixes the edge star modulo Z. -/
theorem edgeStar_commutator_le_Z_of_flag (i : Bool)
    (htriple : ⁅⁅V R (beta R), Flags.RankOne.flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    ⁅edgeStar R geometry (alpha R) (beta R), Flags.RankOne.flagResidual source i⁆ ≤
      Z R (alpha R) :=
  (commutator_mono (edgeStar_le_edgeRadius geometry) le_rfl).trans
    (edge_commutator_le_Z_of_flag source geometry common radius i htriple)

include common radius in
/-- The full starred quotient has no nonzero component-fixed elements. -/
theorem star_fixed_preimage_eq_Z :
    commutatorPreimage (VStar R geometry (alpha R) (beta R)) (Ltilde R (alpha R))
      (Z R (alpha R)) = Z R (alpha R) := by
  have hV := geometry.V_local (alpha R) rfl common.large_distance
  have hstar := Flags.star_le_radius geometry (alpha R) (beta R)
  apply le_antisymm
  · intro x hx
    have hxs := commutatorPreimage_le _ _ _ hx
    have hc := commutator_commutatorPreimage_le
      (VStar R geometry (alpha R) (beta R)) (Ltilde R (alpha R)) (Z R (alpha R))
      (hstar.trans (hV.trans (Z_normalized R (alpha R))))
    have hxB : x ∈ B R (alpha R) (geometry.Z_normal (alpha R)) := by
      apply (mem_B_iff R (alpha R) (geometry.Z_normal _) hV x).mpr
      refine ⟨hstar hxs, ?_⟩
      intro l hl
      rw [commutator_comm] at hc
      exact hc (commutator_mem_commutator hl hx)
    exact (radius.star_intersection (alpha R) (beta R) rfl (base_adjacent R)).le ⟨hxs, hxB⟩
  · exact le_commutatorPreimage
      (Flags.Z_le_star geometry radius.toEarlyFacts common.large_distance
        (alpha R) (beta R) rfl (base_adjacent R))
      (le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans (Z_normalized R _)))

include common radius in
/-- The edge star is nonzero modulo Z, since otherwise the radius group is abelian. -/
theorem edgeStar_not_le_Z : ¬ edgeStar R geometry (alpha R) (beta R) ≤ Z R (alpha R) := by
  intro he
  have hs : VStar R geometry (alpha R) (beta R) ≤ Z R (alpha R) :=
    iSup_conjugates_le_of_le_normalizer _ _ _ he (Z_normalized R (alpha R))
  have hV := geometry.V_local (alpha R) rfl common.large_distance
  have hb : V R (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)) := by
    rw [Flags.radius_eq_B_sup_star geometry radius.toEarlyFacts common.large_distance
      (alpha R) (beta R) rfl (base_adjacent R)]
    exact sup_eq_left.mpr (hs.trans (Flags.Z_le_B geometry (alpha R) hV))
  have hc : V R (alpha R) ≤ centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
    conv_lhs => rw [hb, radius.B_eq_center (alpha R) rfl]
    rintro x ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)
  apply radius.derived_noncentral (alpha R) rfl
  rw [commutator_eq_bot_iff_le_centralizer.mpr hc]
  exact bot_le

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
