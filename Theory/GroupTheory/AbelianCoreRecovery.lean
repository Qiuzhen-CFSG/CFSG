module

public import Theory.Quasithin
public import Theory.PGroupCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Recovering an abelian local core

For a Sylow overgroup `H ≤ M`, the core of `M` lies in the core of `H`.
If the latter lies in the core of a subgroup `L` normalized by `M`, the
three cores coincide. For a maximal two-local `M` with self-centralizing
two-core, a nontrivial abelian core obtained this way is self-centralizing
in the ambient group and its normalizer is `M`.

This is the core-sandwich and centralizer argument in Aschbacher--Smith,
*The Classification of Quasithin Groups*, Lemma 3.2.11, p. 584
(combined manuscript, 1 March 2004).
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Core recovery along a Sylow overgroup and a normalized subgroup. All
cores are embedded in the ambient group via their literal subtype maps. -/
public theorem mapped_pCore_eq_of_normalized_subgroup_sandwich
    [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    (L H M : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hHM : H ≤ M)
    (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hcore : (pCore p H).map H.subtype ≤ (pCore p L).map L.subtype) :
    (pCore p M).map M.subtype = (pCore p H).map H.subtype := by
  let R := (pCore p M).map M.subtype
  let Q := (pCore p L).map L.subtype
  have hRT : R ≤ (T : Subgroup G) := by
    rintro x ⟨r, hr, rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype (hTH.trans hHM)) hr
  have hRH : R ≤ H := hRT.trans hTH
  have hMR : M ≤ normalizer (R : Set G) := by
    have hn := (pCore p M).le_normalizer_map M.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
  have hMQ : M ≤ normalizer (Q : Set G) :=
    hML.trans (normalizer_le_normalizer_characteristic_image L (pCore p L))
  have hQM : Q ≤ M := (map_subtype_le _).trans hLM
  have hQR : Q ≤ R := by
    let : (Q.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMQ
    have hQp : IsPGroup p Q := pCore_isPGroup.map L.subtype
    rw [← map_subgroupOf_eq_of_le hQM]
    exact map_mono (show Q.subgroupOf M ≤ pCore p M from
      le_sSup ⟨inferInstance, hQp.comap_subtype⟩)
  refine le_antisymm ?_ (hcore.trans hQR)
  let : (R.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer (hHM.trans hMR)
  have hRp : IsPGroup p R := pCore_isPGroup.map M.subtype
  change R ≤ (pCore p H).map H.subtype
  rw [← map_subgroupOf_eq_of_le hRH]
  exact map_mono (show R.subgroupOf H ≤ pCore p H from
    le_sSup ⟨inferInstance, hRp.comap_subtype⟩)

/-- A nontrivial abelian two-core of a maximal two-local with characteristic
two is self-centralizing in the whole group. -/
public theorem normalizer_and_centralizer_eq_of_abelian_twoCore
    (M V : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hV : V = (pCore 2 M).map M.subtype) (hne : V ≠ ⊥)
    [IsMulCommutative V]
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    normalizer (V : Set G) = M ∧ centralizer (V : Set G) = V := by
  have hp : IsPGroup 2 V := hV ▸ pCore_isPGroup.map M.subtype
  have hn : M ≤ normalizer (V : Set G) := by
    rw [hV]
    have h := (pCore 2 M).le_normalizer_map M.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  have heq : normalizer (V : Set G) = M :=
    le_antisymm (hM.2 ⟨V, hne, hp, rfl⟩ hn) hn
  refine ⟨heq, le_antisymm ?_ V.le_centralizer⟩
  intro x hx
  have hxM : x ∈ M := heq ▸ centralizer_le_normalizer (V : Set G) hx
  have hxC : (⟨x, hxM⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
    intro y hy
    apply Subtype.ext
    exact hx y (hV ▸ mem_map_of_mem M.subtype hy)
  rw [hV]
  exact mem_map_of_mem M.subtype (hchar hxC)

/-- Equal conjugation images identify subgroups that contain the action
kernel. This is the last step of Lemma 3.2.11. -/
public theorem eq_of_normalizer_action_image_eq
    (V H M : Subgroup G)
    (hHN : H ≤ normalizer (V : Set G)) (hMN : M ≤ normalizer (V : Set G))
    (hCH : centralizer (V : Set G) ≤ H) (hCM : centralizer (V : Set G) ≤ M)
    (himage : (H.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom =
      (M.subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom) : H = M := by
  have hkH : V.normalizerMonoidHom.ker ≤ H.subgroupOf (normalizer (V : Set G)) := by
    rw [normalizerMonoidHom_ker]
    exact comap_mono hCH
  have hkM : V.normalizerMonoidHom.ker ≤ M.subgroupOf (normalizer (V : Set G)) := by
    rw [normalizerMonoidHom_ker]
    exact comap_mono hCM
  have heq := congrArg (Subgroup.comap V.normalizerMonoidHom) himage
  rw [comap_map_eq_self hkH, comap_map_eq_self hkM] at heq
  have hmap := congrArg (Subgroup.map (normalizer (V : Set G)).subtype) heq
  simpa only [map_subgroupOf_eq_of_le hHN, map_subgroupOf_eq_of_le hMN] using hmap

end Subgroup
