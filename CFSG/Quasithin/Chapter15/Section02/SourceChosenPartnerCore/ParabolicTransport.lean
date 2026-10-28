module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore
public import Theory.Representation.SmallDisplacementParabolics.Models

/-!
# Lifting the moving parabolic in the actual partner-core quotient

A quotient whose marked Sylow preimage is the original T preserves the
needed minimality. Proper preimages normalize T and hence lie in M by
the already proved Baumann control. Surjectivity maps the literal embedded
two-residual onto the model parabolic's residual, preserving movement of
an equivariant image of the distinguished plane.

The final application fixes L = KcT, Kc = the Mc-orbit span of O²(H),
and q = L → L/O₂(L). It constructs the quotient Sylow and its preimage
and invokes the source parabolic contradiction. The moving parabolic
and its marked action remain explicit outputs of the unfinished
recognition and model calculations, not earlier-source hypotheses.

Source: Aschbacher--Smith, 15.2.27(2), printed p.1119.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry
open Representation.SmallDisplacementParabolics
variable {G D W : Type*} [Group G] [Finite G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Transport the concrete parabolic through the actual quotient map.
The compatibility premise is satisfied by any equivariant projection of a
plane element to the marked chief vector. -/
theorem source_chosen_lift_moving_parabolic
    {T : Sylow 2 G} {M Mc V ZS L : Subgroup G}
    (h : ChosenSmallSource T M Mc V)
    (hTL : (T : Subgroup G) ≤ L) (hLMc : L ≤ Mc)
    (q : L →* D) (hq : Function.Surjective q) (S : Sylow 2 D)
    (hS : (S : Subgroup D).comap q = (T : Subgroup G).subgroupOf L)
    (ρ : Representation (ZMod 2) D W) (w : W)
    (hfix : ∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → ρ (q g) w = w)
    (d : MovingParabolic ρ S w) : ∃ P, ChosenMovingParabolic T M Mc ZS P := by
  let P₀ := d.subgroup.comap q
  let P := P₀.map L.subtype
  have hPL : P ≤ L := map_subtype_le _
  have hTP₀ : (T : Subgroup G).subgroupOf L ≤ P₀ := by
    rw [← hS]
    exact comap_mono d.sylow_le
  have hTP : (T : Subgroup G) ≤ P := by
    have hh := map_mono (f := L.subtype) hTP₀
    rwa [map_subgroupOf_eq_of_le hTL] at hh
  have hPq : P₀.map q = d.subgroup := map_comap_eq_self_of_surjective hq _
  have hNT : normalizer (T : Set G) ≤ M :=
    (source_centralizing_baumann_control h.ambient T h.maximal h.centralizing).2.2.2.2.2.2
  refine ⟨P, hTP, hPL.trans hLMc, ?_, ?_⟩
  · intro Y hTY hYP
    have hYL := hYP.le.trans hPL
    have hYP₀ : Y.subgroupOf L ≤ P₀ := by
      intro y hy
      obtain ⟨x, hx, he⟩ := hYP.le hy
      exact (Subtype.ext he : x = y) ▸ hx
    have hSY : (S : Subgroup D) ≤ (Y.subgroupOf L).map q := by
      rw [← map_comap_eq_self_of_surjective hq (S : Subgroup D), hS]
      exact map_mono (comap_mono hTY)
    have hlt : (Y.subgroupOf L).map q < d.subgroup := by
      apply lt_of_le_not_ge (hPq ▸ map_mono hYP₀)
      intro hh
      have hker : q.ker ≤ Y.subgroupOf L := by
        have hk : q.ker ≤ (S : Subgroup D).comap q := ker_le_comap _ _
        rw [hS] at hk
        exact hk.trans (comap_mono hTY)
      have hp : P₀ ≤ Y.subgroupOf L := by
        have hc := comap_mono (f := q) hh
        rw [comap_map_eq, sup_eq_left.mpr hker] at hc
        exact hc
      have hm := map_mono (f := L.subtype) hp
      rw [map_subgroupOf_eq_of_le hYL] at hm
      exact hYP.not_ge hm
    have hnorm : Y.subgroupOf L ≤ normalizer ((T : Subgroup G).subgroupOf L : Set L) := by
      have hh := map_le_iff_le_comap.mp (d.proper _ hSY hlt)
      have he := ((S : Subgroup D).le_normalizer_comap q)
      rw [hS] at he
      exact hh.trans he
    have hh := (map_mono (f := L.subtype) hnorm).trans
      (((T : Subgroup G).subgroupOf L).le_normalizer_map L.subtype)
    rw [map_subgroupOf_eq_of_le hYL, map_subgroupOf_eq_of_le hTL] at hh
    exact hh.trans hNT
  · intro hc
    obtain ⟨g, hg, hmove⟩ := d.moves
    have he := map_embedded_pResidual 2 P₀ q
    rw [hPq] at he
    obtain ⟨x, hx, rfl⟩ := he.symm ▸ hg
    apply hmove
    apply hfix x
    have hm := map_embedded_pResidual 2 P₀ L.subtype
    apply hc
    change (x : G) ∈ (pResidual 2 P).map P.subtype
    rw [← hm]
    exact mem_map_of_mem L.subtype hx

/-- The model parabolic gives the literal source contradiction after quotient
transport. Its existence remains an obligation of the model calculation. -/
theorem source_chosen_false_of_moving_quotient
    {T : Sylow 2 G} {M Mc V H ZS L : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G))
    (hTL : (T : Subgroup G) ≤ L) (hLMc : L ≤ Mc)
    (q : L →* D) (hq : Function.Surjective q) (S : Sylow 2 D)
    (hS : (S : Subgroup D).comap q = (T : Subgroup G).subgroupOf L)
    (ρ : Representation (ZMod 2) D W) (w : W)
    (hfix : ∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → ρ (q g) w = w)
    (d : MovingParabolic ρ S w) : False := by
  obtain ⟨P, hp⟩ := source_chosen_lift_moving_parabolic h hTL hLMc q hq S hS ρ w hfix d
  exact source_chosen_moving_parabolic_false h hg hMc hplane hp

/-- The literal source application uses Kc = the Mc-span of embedded O²(H),
L = KcT and its quotient by O₂(L). Its quotient Sylow and preimage are
constructed, and all parabolic movement is transported through this map. -/
theorem source_chosen_false_of_partner_core_quotient
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    let S := (T.subtype (show (T : Subgroup G) ≤ L from le_sup_right)).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 L))
    ∀ (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W) (w : W),
      (∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → ρ (q g) w = w) →
      MovingParabolic ρ S w → False := by
  dsimp only
  intro ρ w hfix d
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let S₀ : Sylow 2 L := T.subtype le_sup_right
  let S := S₀.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hS : (S : Subgroup (L ⧸ pCore 2 L)).comap q =
      (T : Subgroup G).subgroupOf L := by
    change ((S₀ : Subgroup L).map q).comap q = _
    rw [comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal S₀)]
    rfl
  have hL : L ≤ Mc := sup_le
    (conjugateSpanBy_le_self ((map_subtype_le (pResidual 2 H)).trans hg.in_partner))
    (hg.outside.1.1.2.trans hg.in_partner)
  exact source_chosen_false_of_moving_quotient h hg hMc hplane le_sup_right hL q
    (QuotientGroup.mk'_surjective _) S hS ρ w hfix d

end CFSG.Quasithin.Chapter15.Section02
