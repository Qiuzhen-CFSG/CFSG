module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement
public import Theory.GroupTheory.PResidual.SubnormalCoreAction


/-!
# The moving seed module inside the relative block

A nonzero commutator [W,K] with a two-group normalized by a block K lies in
its intrinsic U(K). Coprime commutator idempotence makes it a full commutator
subgroup. Irreducibility of U(K)/C_U(K) then makes it all of U(K), including
the central layer.

The actual source applications take place inside KTᵥ. They identify both
[W_K,K] and [⟨z^K⟩,K] with the embedded U(K). Thus the A₅-block module can
be compared with the exact seed module excluded by 13.6.15. The earlier
containment W_K ≤ Tᵥ remains explicit; block subnormality is relative to KTᵥ.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
C.1.7–8, printed p.123; 13.6.15 and 13.6.18, pp.930–931.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MovingBlock

open Subgroup CFSG.Quasithin.ChapterC
open scoped commutatorElement

private theorem short_module_full {H : Type*} [Group H] (h : IsShort H) :
    ⁅blockU H, (⊤ : Subgroup H)⁆ = blockU H := by
  let := h.finite
  exact commutator_isPPerfect_idempotent ⊤ (pCore 2 H)
    (h.twoPerfect.of_surjective (topEquiv (G := H)).symm.toMonoidHom
      (topEquiv (G := H)).symm.surjective) pCore_isPGroup le_normalizer_of_normal

private theorem short_full_normal_eq {H : Type*} [Group H] (h : IsShort H)
    (N : Subgroup H) [N.Normal] (hle : N ≤ blockU H)
    (hfull : ⁅N, (⊤ : Subgroup H)⁆ = N) (hne : N ≠ ⊥) : N = blockU H := by
  let C := blockU H ⊓ center H
  have hNC : N ⊔ C = blockU H := by
    rcases h.irreducible.2 (N ⊔ C) inferInstance le_sup_right
      (sup_le hle inf_le_left) with he | he
    · have hc : N ≤ center H := le_sup_left.trans (he.le.trans inf_le_right)
      exact (hne (hfull.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr hc))).elim
    · exact he
  apply le_antisymm hle
  rw [← short_module_full h, ← hNC]
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨n, hn, c, hc, rfl⟩ := mem_sup_of_normal_right.mp hx
  have hcy : Commute c y := (mem_center_iff.mp hc.2 y).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hcy.commutator_eq]
  simpa using (commutator_le_left N (⊤ : Subgroup H))
    (commutator_mem_commutator hn hy)

/-- A moving two-subgroup generates the entire intrinsic block layer. -/
theorem block_moving_eq {H : Type*} [Group H] [Finite H]
    (K W : Subgroup H) (hK : IsBlock K) (hW : IsPGroup 2 W)
    (hn : K ≤ normalizer (W : Set H)) (hne : ⁅W, K⁆ ≠ ⊥) :
    ⁅W, K⁆ = (blockU K).map K.subtype := by
  have hle := commutator_le_core_commutator_of_isSubnormal K W hK.subnormal
    hK.short.twoPerfect hW hn
  have hDK : ⁅W, K⁆ ≤ K := hle.trans (map_subtype_le _)
  let N := (⁅W, K⁆).subgroupOf K
  have hmap : N.map K.subtype = ⁅W, K⁆ := map_subgroupOf_eq_of_le hDK
  let : N.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right W K)
  have hNU : N ≤ blockU K := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rwa [hmap]
  have hfull : ⁅N, (⊤ : Subgroup K)⁆ = N := by
    apply map_injective K.subtype_injective
    rw [map_commutator, hmap, ← MonoidHom.range_eq_map, range_subtype]
    exact commutator_isPPerfect_idempotent K W hK.short.twoPerfect hW hn
  have hNne : N ≠ ⊥ := by
    intro he
    exact hne (by rw [← hmap, he, Subgroup.map_bot])
  rw [← hmap, short_full_normal_eq hK.short N hNU hfull hNne]

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open ComponentSelection

/-- Apply block rigidity inside KTᵥ to any K-invariant two-subgroup
containing the original moving seed. No ambient-G subnormality is used. -/
theorem source_subgroup_moving_eq_blockU {G : Type*} [Group G] [Finite G]
    (K L T W : Subgroup G) (z v : G)
    (hzW : z ∈ W) (hKW : K ≤ normalizer (W : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : W ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v))) :
    ⁅W, K⁆ = (blockU K).map K.subtype := by
  let H := K ⊔ Tv T v
  let K₁ := K.subgroupOf H
  let W₁ := W.subgroupOf H
  have hKH : K ≤ H := le_sup_left
  have hWH : W ≤ H := hW.trans le_sup_right
  have hkmap : K₁.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hwmap : W₁.map H.subtype = W := map_subgroupOf_eq_of_le hWH
  have hKW₁ : K₁ ≤ normalizer (W₁ : Set H) := by
    rw [← subgroupOf_normalizer_eq hWH]
    exact comap_mono hKW
  have hne : ⁅W, K⁆ ≠ ⊥ := by
    intro hc
    have hfix : K ≤ centralizer ({z} : Set G) :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
        (centralizer_le (Set.singleton_subset_iff.mpr hzW))
    exact (invariant_component_consequences K L T z v hK hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr hfix)
  have hne₁ : ⁅W₁, K₁⁆ ≠ ⊥ := by
    intro hc
    apply hne
    have he := congrArg (Subgroup.map H.subtype) hc
    simpa only [map_commutator, hwmap, hkmap, Subgroup.map_bot] using he
  have hp : IsPGroup 2 W₁ :=
    ((CFSG.Quasithin.Chapter1.isSylowIn_iff.mp hK.1.2.2.1).1.to_le hW).comap_subtype
  have he := congrArg (Subgroup.map H.subtype) (block_moving_eq K₁ W₁ hb hp hKW₁ hne₁)
  rw [map_commutator, hwmap, hkmap] at he
  refine he.trans ?_
  let e : K₁ ≃* K := subgroupOfEquivOfLe hKH
  have hf : H.subtype.comp K₁.subtype = K.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [map_map, hf, ← map_map, blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective _ e.surjective]
  rfl

/-- The U_K used by the plus representation equals the embedded U(K). -/
theorem source_moving_eq_blockU {G : Type*} [Group G] [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v))) :
    ⁅WK K L T z v, K⁆ = (blockU K).map K.subtype :=
  source_subgroup_moving_eq_blockU K L T (WK K L T z v) z v
    (le_conjugateSpanBy _ _ (mem_zpowers z))
    ((K_le_plusActor K L T v).trans (plusActor_normalizes_WK K L T z v hL hz))
    hK hn hW hb

/-- The same block layer is already generated inside ⟨z^K⟩, the module
appearing in the exact 13.6.15 exclusion. -/
theorem seed_moving_eq_blockU {G : Type*} [Group G] [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v))) :
    ⁅conjugateSpanBy (zpowers z) K, K⁆ = (blockU K).map K.subtype := by
  have hQW : conjugateSpanBy (zpowers z) K ≤ WK K L T z v :=
    conjugateSpanBy_mono le_rfl ((le_conjugateSpanBy K (Tv T v)).trans le_sup_left)
  exact source_subgroup_moving_eq_blockU K L T _ z v
    (le_conjugateSpanBy _ _ (mem_zpowers z)) (le_normalizer_conjugateSpanBy _ _)
    hK hn (hQW.trans hW) hb

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MovingBlock

end
