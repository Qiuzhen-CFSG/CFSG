module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalPaired
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightGeometry
public import Theory.SpecificGroups.Alternating.FiveCoreHallBound

/-!
# The prescribed right Hall subgroup in the A₅ residual branch

The residual is normal in H and its full Sylow is the original
intersection with T. The proper overlap with N_G(L) maps into the
order-twelve normalizer in its actual A₅ two-core quotient. Thus the
prescribed odd Hall subgroup has order at most three. The original
E.2.2 Hall witness has a nontrivial cyclic subgroup, so Hall conjugacy
in cardinal form gives order exactly three. Neither field degree two
nor coordinates on the selected module are assumed.

Source: Aschbacher–Smith 5.1.10 and 5.1.13, printed pp.634,636–637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem maximal_eq_overlap {T : Sylow 2 G} {M H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    minimalParabolicMax (T.subtype hH.1.1.2) hP = M.subgroupOf H := by
  let J := minimalParabolicMax (T.subtype hH.1.1.2) hP
  have hJ := minimalParabolicMax_spec (T.subtype hH.1.1.2) hP
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hJ.2
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hJM : J ≤ M.subgroupOf H := map_le_iff_le_comap.mp
    (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
  have hn : M.subgroupOf H ≠ ⊤ := fun he => hH.1.2 (subgroupOf_eq_top.mp he)
  exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm

/-- The original right Hall subgroup is cubic when the literal residual quotient is A₅. -/
theorem right_hall_card_three_of_residual_A5
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (he : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5))) :
    Nat.card B = 3 := by
  let M := normalizer (L : Set G)
  have hBH : B ≤ H := c.right_le.trans inf_le_right
  have hBK : B ≤ residual H := Global.right_cartan_le_residual c
  have hTK : (T : Subgroup G) ≤ normalizer (residual H : Set G) :=
    hH.1.1.2.trans (le_normalizer_residual H)
  obtain ⟨P,hP⟩ := exists_sylow_component hTK
  have hP' : (P : Subgroup (residual H)) = (T : Subgroup G).subgroupOf (residual H) := by
    apply map_injective (residual H).subtype_injective
    rw [hP, subgroupOf_map_subtype]
  have hbound : Nat.card B ≤ 3 := by
    have ho : Odd (Nat.card (B.subgroupOf (residual H))) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv,
        ← Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
      exact OddHall.odd_hall_odd c.right_hall
    have hb := Theory.SpecificGroups.Alternating.FiveSylowMaximal.odd_subgroup_card_le_three_of_core_quotient
      he.some P (M.subgroupOf (residual H)) (B.subgroupOf (residual H))
      (by rw [hP']; exact comap_mono h.sylow_normalizes)
      (fun ht => residual_not_le T H M hH.1.1.2 h.sylow_normalizes hH.1.2
        (subgroupOf_eq_top.mp ht)) (comap_mono (c.right_le.trans inf_le_left)) ho
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv] at hb
  let S := T.subtype hH.1.1.2
  have hmin := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hgen
  obtain ⟨f,_,hf,d,_⟩ := MarkedModels.Inverted.source_intrinsic_escape_knownSimple
    (Chapter3.sqtk_of_mem_H h.qtke hH.1.1.1) S hmin hgen
  let N := M.subgroupOf H
  let e : minimalParabolicMax S hmin ≃* (M ⊓ H : Subgroup G) :=
    (MulEquiv.subgroupCongr (maximal_eq_overlap hH hmin)).trans
      ((N.equivMapOfInjective H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr (subgroupOf_map_subtype M H)))
  let B' := (B.subgroupOf (M ⊓ H)).map e.symm.toMonoidHom
  have hb' : IsHallSubgroup OddHall.oddPrimes B' :=
    ⟨fun p hp => c.right_hall.p_in_pi_of_p_dvd_card p
      (hp.trans (card_map_dvd _ e.symm.toMonoidHom)),
    fun p hp => c.right_hall.p_in_pi_of_p_dvd_index p
      (hp.trans (index_map_dvd _ e.symm.surjective))⟩
  have hbc : Nat.card B' = Nat.card B := by
    change Nat.card ((B.subgroupOf (M ⊓ H)).map e.symm.toMonoidHom) = _
    rw [card_map_of_injective e.symm.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv
  have hc : Nat.card d.witness.abelianGroup = Nat.card B :=
    (Nat.card_congr (subgroupOfEquivOfLe d.hall_le).toEquiv).symm.trans
      ((d.hall.card_eq hb').trans hbc)
  have hl := Nat.le_of_dvd (Nat.card_pos (α := d.witness.abelianGroup))
    (card_dvd_of_le d.witness.cyclic_le)
  rw [d.witness.card,hc] at hl
  have hf2 : 2 ≤ f := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf2
  norm_num at hp
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
