module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup

/-!
# The known central natural layer of the actual MS93 core

The local comparison through embedM puts [Q_alpha,Ltilde_alpha] inside
Q_alpha. The common natural summand U_alpha lies both in that commutator
and in Z_alpha, which centralizes Q_alpha. Hence U_alpha lies in the
intrinsic center of the actual core. Its given natural marking supplies
order eight and square one. No upper bound on the core's center is asserted.

Source: MS93 (1993), 2.1(iv), 4.1 and the definitions preceding 4.6.
The normalization proof uses the actual amalgam conjugation action.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
variable {M : Type*} [Group M] {L R : Subgroup M}
  (source : LocalSource L R) (geometry : Geometry R)
  (common : CommonFacts R source geometry)

include source in
theorem core_le_Q [Finite M] : core R (alpha R) ≤ Q R (alpha R) := by
  rw [core_alpha R source.two_group source.core_le source.residual,
    Q_alpha R source.two_group source.core_le]
  exact map_mono (commutator_le_left _ _)

include common in
theorem U_le_core : U R (alpha R) ≤ core R (alpha R) := by
  apply commutator_mono _ le_rfl
  rw [← common.X_eq_Z (alpha R) rfl]
  exact omegaCenter_le _

include common in
theorem U_le_center_core [Finite M] : U R (alpha R) ≤
    (center (core R (alpha R))).map (core R (alpha R)).subtype := by
  intro x hx
  have hxC := U_le_core source geometry common hx
  refine ⟨⟨x, hxC⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hz : x ∈ Z R (alpha R) := by
    rw [common.decomposition]
    exact mem_sup_left hx
  exact (commutator_eq_bot_iff_le_centralizer.mp
    (geometry.centralizes (alpha R) rfl)) hz y (core_le_Q source y.property)

include common in
theorem U_card : Nat.card (U R (alpha R)) = 8 := by
  rw [Nat.card_congr common.natural.equiv.toEquiv, Nat.card_eq_fintype_card]
  decide

include common in
theorem U_square (x : U R (alpha R)) : x ^ 2 = 1 := by
  apply common.natural.equiv.injective
  rw [map_pow, map_one, pow_two]
  change Multiplicative.ofAdd ((common.natural.equiv x).toAdd +
    (common.natural.equiv x).toAdd) = Multiplicative.ofAdd 0
  congr 1
  ext i
  exact CharTwo.add_self_eq_zero _

include common in
theorem U_ne_bot : U R (alpha R) ≠ ⊥ := by
  intro h
  have he := U_card source geometry common
  rw [h, Subgroup.card_bot] at he
  norm_num at he

theorem core_normalized : Mbar R ≤ normalizer (core R (alpha R)) := by
  rw [← stabilizer_m_base R]
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (core R (alpha R)).map (MulAut.conj g).toMonoidHom = _
  have hh := core_act R g⁻¹ (alpha R)
  have hga : act R g⁻¹ (alpha R) = alpha R :=
    (stabilizer R (alpha R)).inv_mem hg
  simpa only [hga, inv_inv] using hh.symm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
