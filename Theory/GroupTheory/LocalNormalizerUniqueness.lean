module

public import Theory.Quasithin
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Preorder.Finite

/-!
# Uniqueness of maximal two-local overgroups

A characteristic nontrivial two-subgroup of `X` puts its normalizer in a
2-local subgroup. In a finite group, if every maximal 2-local overgroup of
`X ⊔ T` normalizes `X`, enlarging this local subgroup shows that the unique
maximal 2-local overgroup is exactly `N_G(X)`.

This is the elementary maximality step in Aschbacher--Smith, *The
Classification of Quasithin Groups*, combined manuscript (1 March 2004),
Theorem 1.3.7, printed p. 512. Maximality is among 2-local subgroups,
not among all proper subgroups. No simplicity assumption is needed here.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- Normalizing a group also normalizes the ambient image of a characteristic subgroup. -/
public theorem normalizer_le_normalizer_characteristic_image (X : Subgroup G) (Q : Subgroup X)
    [Q.Characteristic] : normalizer (X : Set G) ≤ normalizer (Q.map X.subtype : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  let a := X.normalizerMonoidHom ⟨g, hg⟩
  have hfixed : Q.comap a.toMonoidHom = Q :=
    (inferInstance : Q.Characteristic).fixed a
  have hay : a y ∈ Q := by
    change y ∈ Q.comap a.toMonoidHom
    rw [hfixed]
    exact hy
  exact Subgroup.mem_map.mpr ⟨a y, hay, rfl⟩

/-- A nontrivial characteristic two-subgroup puts the normalizer in a two-local. -/
public theorem exists_twoLocal_overgroup_normalizer (X : Subgroup G) (Q : Subgroup X)
    [Q.Characteristic] (hne : Q ≠ ⊥) (hQ : IsPGroup 2 Q) :
    ∃ L : Subgroup G, IsTwoLocal L ∧ normalizer (X : Set G) ≤ L := by
  refine ⟨normalizer (Q.map X.subtype : Set G), ?_, normalizer_le_normalizer_characteristic_image X Q⟩
  exact ⟨Q.map X.subtype,
    fun h => hne ((Q.map_eq_bot_iff_of_injective X.subtype_injective).mp h),
    hQ.map X.subtype, rfl⟩

/-- Normality in all maximal two-local overgroups identifies their unique member,
provided the normalizer has a two-local overgroup. -/
public theorem unique_maximalTwoLocal_overgroup_of_normal [Finite G] (X T : Subgroup G)
    (hT : T ≤ normalizer (X : Set G))
    (hlocal : ∃ L : Subgroup G, IsTwoLocal L ∧ normalizer (X : Set G) ≤ L)
    (hnormal : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ T ≤ M →
      (X.subgroupOf M).Normal) :
    IsMaximalTwoLocal (normalizer (X : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ T ≤ M} =
        {normalizer (X : Set G)} := by
  have hXT : X ⊔ T ≤ normalizer (X : Set G) := sup_le X.le_normalizer hT
  obtain ⟨L, hL, hXL⟩ := hlocal
  obtain ⟨M, hLM, hM⟩ := Finite.exists_le_maximal hL
  have hXTM : X ⊔ T ≤ M := hXT.trans (hXL.trans hLM)
  have hMN : M ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hXTM)).mp (hnormal M hM hXTM)
  have hMeq : M = normalizer (X : Set G) := le_antisymm hMN (hXL.trans hLM)
  have hN : IsMaximalTwoLocal (normalizer (X : Set G)) := hMeq ▸ hM
  refine ⟨hN, ?_⟩
  ext K
  constructor
  · rintro ⟨hK, hXTK⟩
    have hKN : K ≤ normalizer (X : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hXTK)).mp
        (hnormal K hK hXTK)
    exact Set.mem_singleton_iff.mpr (hK.eq_of_le hN.1 hKN)
  · intro hK
    have heq := Set.mem_singleton_iff.mp hK
    subst K
    exact ⟨hN, hXT⟩
end Subgroup
