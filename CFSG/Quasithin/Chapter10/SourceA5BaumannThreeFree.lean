module
public import CFSG.Quasithin.Chapter10.SourceA5ModuleKernel
public import CFSG.Quasithin.Chapter10.SourceA5PairedBaumann
public import CFSG.Quasithin.Chapter10.SourceCubicResidual
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveNormalizer

/-!
# The original Baumann normalizer has no cubic factor

The paired E.2.3 action has a two-group Baumann normalizer in the residual
image. Its actual local-module kernel is a two-group, so the intersection
with the original orbit L₀ is a two-group. The cubic-residual theorem then
shows that N_M(Baum(T)) has order prime to three. These are the original
subgroups and the same marked quotient; no fixed-center assumption is used.

Source: Aschbacher–Smith, 10.2.1, printed p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original orbit contributes only a two-group to the Baumann normalizer. -/
theorem source_a5_orbit_baumann_normalizer_isTwoGroup
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    IsPGroup 2 (localOrbit T L ⊓ normalizer (baumann (T : Subgroup G) : Set G) : Subgroup G) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact source_a5_module_centralizer_isTwoGroup D e hn hout
  obtain ⟨d,t,ht1,ht2,⟨c⟩⟩ := source_a5_paired_five_action D e hn hout
  have hp := paired_residual_baumann_normalizer_isTwoGroup S
    (source_a5_minimal_parabolic D e hn) U hU
    (source_local_thompson_not_centralizes D hout) q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hk d c ⟨t,ht1,ht2⟩
  have hBH : baumann (T : Subgroup G) ≤ H := inf_le_left.trans le_sup_right
  have hB : baumann (S : Subgroup H) = (baumann (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (baumann (S : Subgroup H)).map H.subtype =
      baumann ((S : Subgroup H).map H.subtype) at he
    have hs : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le le_sup_right
    rw [hs] at he
    exact he.trans (map_subgroupOf_eq_of_le hBH).symm
  have hR : pResidual 2 H = (localOrbit T L).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [source_join_residual D,map_subgroupOf_eq_of_le le_sup_left]
  rw [hR,hB,←subgroupOf_normalizer_eq hBH] at hp
  have he : (localOrbit T L).subgroupOf H ⊓
      (normalizer (baumann (T : Subgroup G) : Set G)).subgroupOf H =
      (localOrbit T L ⊓ normalizer (baumann (T : Subgroup G) : Set G)).subgroupOf H := rfl
  rw [he] at hp
  have hm := hp.map H.subtype
  rw [map_subgroupOf_eq_of_le (inf_le_left.trans (show localOrbit T L ≤ H from le_sup_left))] at hm
  exact hm

/-- The local-orbit normalizer has order prime to three. -/
theorem source_a5_orbit_baumann_normalizer_three_free
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    Nat.Coprime 3 (Nat.card
      (localOrbit T L ⊓ normalizer (baumann (T : Subgroup G) : Set G) : Subgroup G)) := by
  obtain ⟨n,hncard⟩ := (source_a5_orbit_baumann_normalizer_isTwoGroup D e hn hout).exists_card_eq
  rw [hncard]
  exact (by decide : Nat.Coprime 3 2).pow_right n

/-- The exact N_M(Baum(T)) exclusion used in the positive-center branch of 10.2.1. -/
theorem source_a5_maximal_baumann_normalizer_three_free
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    Nat.Coprime 3 (Nat.card
      (D.maximalLocal ⊓ normalizer (baumann (T : Subgroup G) : Set G) : Subgroup G)) := by
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact source_nonnormal_normalizer_three_free D hn hd _
    (source_a5_orbit_baumann_normalizer_three_free D e hn hout)

end CFSG.Quasithin.Chapter10
