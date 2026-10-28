module
public import Theory.GroupTheory.GeneralizedFitting.ComponentOvergroup
public import Theory.GroupTheory.GeneralizedFitting.CoreCommutatorImage
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
/-!
# Lifting a normalized component from a contained generalized Fitting preimage

The image of the original perfect subgroup is quasisimple once its core
commutator is killed by the ambient two-core. Its local normality makes it
an ordinary component in an overgroup of the generalized Fitting subgroup,
so it is an ambient component. Pulling back subnormality and using the
original normalizer containment lifts the same subgroup to a C-component.

Source: Aschbacher–Smith C.2.13, p.148, for normalized block input.
-/
public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- The original subgroup becomes an ambient C-component through its literal two-core image. -/
theorem isCComponent_of_contained_generalizedFitting
    (L M : Subgroup G) [Group.IsPerfect L] [IsQuasisimple (L ⧸ pCore 2 L)]
    (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hQ : pCore 2 G ≤ M)
    (hU : (⁅pCore 2 L,(⊤ : Subgroup L)⁆).map L.subtype ≤ pCore 2 G)
    (hF : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ M) : L.IsCComponent := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := q.comp L.subtype
  have hfk : f.ker = (pCore 2 G).comap L.subtype := by
    change (q.comp L.subtype).ker = _
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  have hk : IsPGroup 2 f.ker := by
    rw [hfk]
    exact pCore_isPGroup.comap_subtype
  have hc : ⁅pCore 2 L,(⊤ : Subgroup L)⁆ ≤ f.ker := by
    rw [hfk]
    exact map_le_iff_le_comap.mp hU
  let := f.quasisimple_range_of_core_commutator_killed hk hc
  have he : f.range = L.map q := by rw [MonoidHom.range_comp,range_subtype]
  let : IsQuasisimple (L.map q) := he ▸ inferInstanceAs (IsQuasisimple f.range)
  have hLMq : L.map q ≤ M.map q := map_mono hLM
  have hMLq : M.map q ≤ normalizer (L.map q : Set (G ⧸ pCore 2 G)) :=
    (map_mono hML).trans (L.le_normalizer_map q)
  let : ((L.map q).subgroupOf (M.map q)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLMq).mpr hMLq
  have hBc : IsComponent (M.map q) ((L.map q).subgroupOf (M.map q)) :=
    ⟨(inferInstance : ((L.map q).subgroupOf (M.map q)).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLMq).symm⟩
  have hFq : generalizedFitting (G ⧸ pCore 2 G) ≤ M.map q := by
    have hh := map_mono (f := q) hF
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _] at hh
  have hb := hBc.of_generalizedFitting_overgroup hLMq hFq
  have hsup : (L ⊔ pCore 2 G).IsSubnormal := by
    have hh := hb.1.comap q
    rwa [comap_map_eq,QuotientGroup.ker_mk'] at hh
  have hLN : L ⊔ pCore 2 G ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer (hQ.trans hML)
  let : (L.subgroupOf (L ⊔ pCore 2 G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hLN
  have hsub : L.IsSubnormal := IsSubnormal.trans le_sup_left
    (inferInstance : (L.subgroupOf (L ⊔ pCore 2 G)).Normal).isSubnormal hsup
  have hp : IsPPerfect 2 L := by
    intro N hN hp
    let := hN
    have hs : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hsub hp
end Subgroup
