module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.OmegaCenterCentralizer
public import Stellmacher.ElementaryAbelianMaxJMap
public import Theory.GroupTheory.PResidual.SylowSupplement
/-!
# Transporting alpha and residual centralizers to a Sylow overgroup

An ambient Sylow subgroup and its intrinsic copy have the same alpha order.
If its omega-center has no fixed point under the overgroup, its intrinsic
Sylow has trivial residual centralizer: the residual and Sylow generate the
whole overgroup, and a nontrivial Sylow centralizer meets the omega-center.

Source: the transport and center-detection step in Aschbacher--Smith
E.2.3 and 10.2.3(4), printed p.746.
-/
public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {H : Subgroup G}
set_option backward.isDefEq.respectTransparency false in
theorem sylow_subtype_residual_centralizer_eq_bot_of_omega
    (hTH : (T : Subgroup G) ≤ H)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥) :
    (T.subtype hTH : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H) = ⊥ := by
  let S := T.subtype hTH
  apply inf_centralizer_eq_bot_of_omega_center _ _ S.isPGroup'
    (by rw [normalizer_eq_top]; exact le_top)
  apply bot_unique
  rintro z ⟨hz,hzc⟩
  have hzG : (z:G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    have hm := omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    rw [show (S : Subgroup H).map H.subtype = (T : Subgroup G) from
      map_subgroupOf_eq_of_le hTH] at hm
    exact hm.symm ▸ mem_map.mpr ⟨z,hz,rfl⟩
  have hR : pResidual 2 H ≤ centralizer ({z} : Set H) := by
    intro r hr x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact (hzc r hr).symm
  have hS : (S : Subgroup H) ≤ centralizer ({z} : Set H) := by
    intro t ht x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have htop : (⊤ : Subgroup H) ≤ centralizer ({z} : Set H) := by
    rw [←pResidual_sup_sylow_eq_top S]
    exact sup_le hR hS
  have hzC : (z:G) ∈ centralizer (H : Set G) := by
    intro x hx
    exact congrArg H.subtype ((htop (mem_top (⟨x,hx⟩ : H)) z (Set.mem_singleton _)).symm)
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hzH ▸ (show (z:G) ∈
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) from ⟨hzG,hzC⟩))))

omit [Finite G] in
theorem alpha_card_subtype (hTH : (T : Subgroup G) ≤ H) :
    Nat.card (thompsonAlpha (T.subtype hTH : Subgroup H)) =
      Nat.card (thompsonAlpha (T : Subgroup G)) := by
  let S := T.subtype hTH
  have hα : (thompsonAlpha (S : Subgroup H)).map H.subtype = thompsonAlpha (T : Subgroup G) := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      show (S : Subgroup H).map H.subtype = (T : Subgroup G) from map_subgroupOf_eq_of_le hTH]
  have hm := card_map_of_injective (K := thompsonAlpha (S : Subgroup H)) H.subtype_injective
  rw [hα] at hm
  exact hm.symm
end CFSG.Quasithin.ChapterB.RankOneBaumann
