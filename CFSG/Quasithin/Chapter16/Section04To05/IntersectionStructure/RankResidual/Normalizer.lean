module

public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.RankResidual.Local

/-!
# A two-local group mapping onto H*

The nontrivial Sylow two-subgroup T_C of K is centralized by L. Tight
embedding gives N_G(T_C) ≤ H. Frattini's argument inside H gives
H = N_G(T_C) K, so N_G(T_C)* is all of the fixed H/K. Quasithinness
and proper-K make this normalizer an SQTK-group. These provide the
second ambient group for A.3.18 in the final H* clause of 16.4.5.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Notation 16.4.1 and Lemma 16.4.5, pp.1183–1184; Frattini's argument.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

/-- The central involution makes T_C nontrivial. -/
theorem StandardSetup.commutingSylow_ne_bot (h : StandardSetup T z L) : commutingSylow T L ≠ ⊥ := by
  intro he
  have hz : z = 1 := by simpa only [he, mem_bot] using h.z_mem_commutingSylow
  have := h.involution
  simp [hz] at this

/-- Tight embedding places the full normalizer of T_C in H. -/
theorem StandardSetup.commutingSylow_normalizer_le (h : StandardSetup T z L) :
    normalizer (commutingSylow T L : Set G) ≤ normalizer (L : Set G) := by
  rw [← h.normalizers_eq]
  exact h.tight.normalizer_le h.commutingSylow_sylow.isPGroup (h.commutingSylow_ne_bot) inf_le_right

omit [Finite G] in
/-- The component centralizes T_C, hence normalizes it. -/
theorem component_le_commutingSylow_normalizer :
    L ≤ normalizer (commutingSylow T L : Set G) :=
  (le_centralizer_iff.mp (show commutingSylow T L ≤ centralizer (L : Set G) from
    inf_le_right)).trans (centralizer_le_normalizer _)

/-- The normalizer of T_C is a genuine two-local subgroup. -/
theorem StandardSetup.commutingSylow_normalizer_twoLocal (h : StandardSetup T z L) :
    IsTwoLocal (normalizer (commutingSylow T L : Set G)) :=
  ⟨commutingSylow T L, h.commutingSylow_ne_bot, h.commutingSylow_sylow.isPGroup, rfl⟩

/-- The two-local normalizer satisfies the SQTK hypothesis of A.3.18. -/
theorem StandardSetup.commutingSylow_normalizer_sqtk {κ : GroupClass} (hG : Hypothesis1611 κ G) (h : StandardSetup T z L) :
    IsSQTK κ (normalizer (commutingSylow T L : Set G)) := by
  let := hG.simple
  have hlocal := h.commutingSylow_normalizer_twoLocal
  exact ⟨isQuasithin_iff_twoLocal.mp hG.quasithin _ hlocal,
    hG.properK _ (twoLocal_ne_top_of_nonabelian_simple hG.nonabelian hlocal)⟩

/-- Frattini supplementation is an equality of actual ambient subgroups. -/
theorem StandardSetup.commutingSylow_normalizer_sup_centralizer (h : StandardSetup T z L) :
    normalizer (commutingSylow T L : Set G) ⊔ centralizer (L : Set G) =
      normalizer (L : Set G) := by
  let H := normalizer (L : Set G)
  let K := centralizer (L : Set G)
  have hKH : K ≤ H := centralizer_le_normalizer _
  have hSH : commutingSylow T L ≤ H := inf_le_right.trans hKH
  obtain ⟨P, hP⟩ := h.commutingSylow_sylow
  let e := (subgroupOfEquivOfLe hKH).symm
  let P' : Sylow 2 (K.subgroupOf H) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPe : ((P' : Subgroup (K.subgroupOf H)).map (K.subgroupOf H).subtype) =
      (commutingSylow T L).subgroupOf H := by
    apply (map_injective H.subtype_injective)
    rw [map_subgroupOf_eq_of_le hSH, ← hP]
    change (((P : Subgroup K).map e.toMonoidHom).map (K.subgroupOf H).subtype).map
      H.subtype = (P : Subgroup K).map K.subtype
    rw [map_map, map_map]
    rfl
  have hh := P'.normalizer_sup_eq_top
  change normalizer
    (((P' : Subgroup (K.subgroupOf H)).map (K.subgroupOf H).subtype) : Set H) ⊔
      K.subgroupOf H = ⊤ at hh
  rw [hPe, ← subgroupOf_normalizer_eq hSH] at hh
  have hm := congrArg (Subgroup.map H.subtype) hh
  have hNH : normalizer (commutingSylow T L : Set G) ≤ H := h.commutingSylow_normalizer_le
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNH,
    map_subgroupOf_eq_of_le hKH, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

/-- The star image of N_G(T_C) is all of H*, with the fixed kernel K. -/
theorem StandardSetup.commutingSylow_normalizer_star_eq_top (h : StandardSetup T z L) :
    starImage L (normalizer (commutingSylow T L : Set G)) (h.commutingSylow_normalizer_le) = ⊤ := by
  let H := normalizer (L : Set G)
  let K := (centralizer (L : Set G)).subgroupOf H
  let N := (normalizer (commutingSylow T L : Set G)).subgroupOf H
  have hs : N ⊔ K = ⊤ := by
    apply (map_injective H.subtype_injective)
    rw [Subgroup.map_sup]
    have hNH : normalizer (commutingSylow T L : Set G) ≤ H := h.commutingSylow_normalizer_le
    have hKH : centralizer (L : Set G) ≤ H := centralizer_le_normalizer _
    rw [show N.map H.subtype = normalizer (commutingSylow T L : Set G) from
      map_subgroupOf_eq_of_le hNH,
      show K.map H.subtype = centralizer (L : Set G) from
        map_subgroupOf_eq_of_le hKH,
      ← MonoidHom.range_eq_map, range_subtype]
    exact h.commutingSylow_normalizer_sup_centralizer
  have hm := congrArg (Subgroup.map (componentActionQuotientMap L)) hs
  change (N ⊔ K).map (QuotientGroup.mk' K) = (⊤ : Subgroup H).map (QuotientGroup.mk' K) at hm
  have hk : K.map (QuotientGroup.mk' K) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [Subgroup.map_sup, hk, sup_bot_eq,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] at hm
  exact hm

end CFSG.Quasithin.Chapter16.Intersections
