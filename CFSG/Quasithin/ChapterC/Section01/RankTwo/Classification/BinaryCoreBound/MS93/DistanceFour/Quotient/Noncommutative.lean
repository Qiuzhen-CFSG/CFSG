module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Source

/-!
# Noncommutativity of the actual distance-four core

An abelian core would commute with the radius group: normalization transfer
places their commutator in the fixed core, while the radius-derived identity
places it in the disjoint natural summand. The three-subgroups lemma then
makes the radius-derived group centralize the component, contradicting the
nontrivial fully moving natural U_alpha.

This supplies the noncommutativity needed on MS93 (1993), printed p.909,
without imposing a radius-generation equality. All local conclusions remain
conditional on the published CommonFacts and RadiusFacts.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  (source : LocalSource L R) (geometry : Geometry R)
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include source common radius in
theorem core_not_commutative : ¬ IsMulCommutative (core R (alpha R)) := by
  intro hc
  have hn : ((core R (alpha R)).subgroupOf (stabilizer R (alpha R))).Normal :=
    normal_subgroupOf_of_le_normalizer (by
      rw [alpha, stabilizer_m_base]
      exact core_normalized (R := R))
  have hm : ⁅Vcirc R (alpha R), core R (alpha R)⁆ ≤ fixedCore R (alpha R) := by
    rw [← radius.core_eq_moving (alpha R) rfl, commutator_self_eq_bot_iff.mpr hc]
    exact bot_le
  have ht := common.normalization_transfer (alpha R) rfl (core R (alpha R))
    (core_le_Q source) hn hm
  have hu : ⁅V R (alpha R), core R (alpha R)⁆ ≤ U R (alpha R) := by
    rw [← radius.radius_derived (alpha R) rfl]
    exact commutator_mono le_rfl (radius.core_le_radius (alpha R) rfl)
  have hz : U R (alpha R) ≤ Z R (alpha R) := by
    rw [common.decomposition]
    exact le_sup_left
  have hzero : ⁅V R (alpha R), core R (alpha R)⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (le_inf hu (le_inf (hu.trans hz) (ht.trans inf_le_right))).trans
      common.disjoint.eq_bot.le
  have hrot : ⁅⁅V R (alpha R), Ltilde R (alpha R)⁆, V R (alpha R)⁆ = ⊥ := by
    rw [← Vcirc, ← radius.core_eq_moving (alpha R) rfl, commutator_comm]
    exact hzero
  have hd : ⁅⁅V R (alpha R), V R (alpha R)⁆, Ltilde R (alpha R)⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hrot (by
      rwa [commutator_comm (Ltilde R (alpha R)) (V R (alpha R))])
  rw [radius.radius_derived (alpha R) rfl, common.full_commutation] at hd
  exact U_ne_bot source geometry common hd

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
