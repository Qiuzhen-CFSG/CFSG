module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RadicalNormalizers
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MaximalPairBase
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.GroupTheory.ComponentLocalCore

/-!
# The escaping-normalizer branch of component selection

A characteristic-two local subgroup of a component, invariant under its
stabilizer in U, gives a characteristic-two group after adjoining U.
When this local subgroup escapes M, the resulting group realizes the
original base U inside the component-Sylow join. The original nontrivial
two-core lies in that join, so the source selection theorem preserves
both starred families, including the globally largest-base condition.

Source: Aschbacher--Smith 2.5.3(4), printed p.553, the case in which the
component radical normalizer is not contained in M. The local seed and
its characteristic-two property are constructed by the model normalizer
producer; they are not assumed in the final source theorem.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- An escaping genuine component-local seed supplies the original base
inside the component-Sylow join and preserves both source stars. -/
theorem component_join_preserves_stars_of_escaping_seed
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (D : Subgroup H) (hD : IsComponent H D)
    (N : Subgroup G) (hND : N ≤ D.map H.subtype)
    (hinv : U ⊓ normalizer (D.map H.subtype : Set G) ≤ normalizer (N : Set G))
    (hNe : N ∈ Chapter1.He G) (hNc : twoCore N ≠ ⊥) (hout : ¬ N ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
  have hUH : U ≤ H := hUS.trans (map_subtype_le _)
  have hD' : IsComponent H ((D.map H.subtype).subgroupOf H) := by
    change IsComponent H ((D.map H.subtype).comap H.subtype)
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hY : N ⊔ U ∈ Chapter1.He G :=
    hD'.relative_local_adjoin_centralizer (map_subtype_le D) hND hUH
      hpair.1.1.1.2 hinv hNe
  have hYc : twoCore (N ⊔ U) ≠ ⊥ := by
    intro hb
    exact hNc (bot_unique (hb ▸
      hD'.pCoreIn_le_local_adjoin_in 2 (map_subtype_le D) hUH hND hinv))
  have hpairX : (U, N ⊔ U) ∈ localPairsIn (Chapter1.He G) M X :=
    ⟨⟨hpair.1.1, hY, hYc, le_sup_right,
      fun hm => hout (le_sup_left.trans hm)⟩,
      sup_le (hND.trans le_sup_left) (hUS.trans le_sup_right)⟩
  have hXH : X ≤ H := sup_le (map_subtype_le _) (map_subtype_le _)
  have hcore : twoCore H ≤ twoCore X :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
      ((pCoreIn_le_sylow H S).trans le_sup_right)
      (hXH.trans (le_normalizer_twoCore H))
  have hXc : twoCore X ≠ ⊥ := by
    intro hb
    have hHc := (hH.elim (fun h => h.1.1) (fun h => h.1)).1
    exact hHc (bot_unique (hb ▸ hcore))
  have ht := lemma_2_3_7_3 hH hpair S hUS
    (show X ∈ gamma (Chapter1.He G) M from ⟨hXc, (U, N ⊔ U), hpairX⟩)
    le_sup_right (fun h => ⟨hbig h, N ⊔ U, hpairX⟩)
  exact ⟨ht.1, ht.2.2.2.1, ht.2.2.2.2⟩


/-- The actual PSL3(3)/M11 radical normalizer escaping M selects the
component-Sylow join with both original starred conditions. Nontriviality
of the intersection is the preceding inner-projection conclusion. -/
theorem small_component_join_preserves_stars_of_escaping_normalizer
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11))
    (hne : D ⊓ (twoCore HU).subgroupOf H ≠ ⊥)
    (hout : ¬ (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  let Q := (twoCore HU).subgroupOf H
  let R := D ⊓ Q
  let N := D ⊓ normalizer (R : Set H)
  have hRD : R ≤ D := inf_le_left
  have hRp : IsPGroup 2 R := (isPGroup_pCoreIn 2 HU).comap_subtype.to_le inf_le_right
  have hneD : R.subgroupOf D ≠ ⊥ := by
    intro hb
    apply hne
    change R = ⊥
    rw [← map_subgroupOf_eq_of_le hRD, hb, Subgroup.map_bot]
  have hnormmap : (normalizer (R.subgroupOf D : Set D)).map D.subtype = N := by
    rw [← subgroupOf_normalizer_eq hRD, subgroupOf_map_subtype, inf_comm]
  have hNe : N.map H.subtype ∈ Chapter1.He G := by
    have hc := small_component_normalizer_mem_He D hm (R.subgroupOf D) hRp.comap_subtype hneD
    rwa [hnormmap] at hc
  have hNR : N.pCoreIn 2 = R := saturated_component_radical hpair hsat D hD
  have hNc : twoCore (N.map H.subtype) ≠ ⊥ := by
    intro hb
    have he : R.map H.subtype = ⊥ := by
      rw [← hNR, map_pCoreIn_of_injective 2 N H.subtype H.subtype_injective]
      exact hb
    exact hne ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he)
  have hAQ : U.subgroupOf H ≤ normalizer (Q : Set H) := by
    intro a ha x
    exact le_normalizer_twoCore HU (hpair.1.2.2.2.1 ha) (x : G)
  have hAR : U.subgroupOf H ⊓ normalizer (D : Set H) ≤ normalizer (R : Set H) :=
    (le_inf inf_le_right (inf_le_left.trans hAQ)).trans inf_normalizer_le_normalizer_inf
  have hAN : U.subgroupOf H ⊓ normalizer (D : Set H) ≤ normalizer (N : Set H) :=
    (le_inf inf_le_right (hAR.trans (normalizer (R : Set H)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hinv : U ⊓ normalizer (D.map H.subtype : Set G) ≤
      normalizer (N.map H.subtype : Set G) := by
    rintro a ⟨ha, hd⟩
    let aH : H := ⟨a, (hUS.trans (map_subtype_le _)) ha⟩
    have hdH : aH ∈ normalizer (D : Set H) := by
      have he := subgroupOf_normalizer_eq (map_subtype_le D)
      rw [show (D.map H.subtype).subgroupOf H = D from
        comap_map_eq_self_of_injective H.subtype_injective D] at he
      rw [← he]
      exact hd
    exact N.le_normalizer_map H.subtype ⟨aH, hAN ⟨ha, hdH⟩, rfl⟩
  exact component_join_preserves_stars_of_escaping_seed hH hpair hbig S hUS D hD
    (N.map H.subtype) (map_mono inf_le_left) hinv hNe hNc hout

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
