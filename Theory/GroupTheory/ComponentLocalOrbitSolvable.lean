module

public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.GroupTheory.SolvableRadical

/-!
# Solvable local subgroups in component orbits

A family of mutually normalizing solvable subgroups generates a solvable
subgroup in a finite group: each factor is normal in the join and lies in
its solvable radical. For a subgroup K of a component L, its conjugates by
A mutually normalize when N_A(L) normalizes K. Their join is normal in
K ⊔ A, with p-group quotient when A is a p-group. Thus K ⊔ A is solvable.
The relative version works inside a specified ambient subgroup and allows
A to permute components, including components with nontrivial centers.

Source: the component-orbit argument used in Aschbacher–Smith 2.3.9(7),
printed pp.525–526, and the solvable Borel construction in E.6.8, p.248.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem isSolvable_iSup_of_normalizes {ι : Type*} (K : ι → Subgroup G)
    (hs : ∀ i, Group.IsSolvable (K i))
    (hn : ∀ i j, K i ≤ normalizer (K j : Set G)) :
    Group.IsSolvable (⨆ i, K i : Subgroup G) := by
  let D := ⨆ i, K i
  have hr : D ≤ (solvableRadical D).map D.subtype := by
    apply iSup_le
    intro i
    have hKi : K i ≤ D := le_iSup K i
    have hnormal : ((K i).subgroupOf D).Normal :=
      (normal_subgroupOf_iff_le_normalizer hKi).mpr (iSup_le fun j => hn j i)
    let := hs i
    have hsolv : Group.IsSolvable ((K i).subgroupOf D) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hKi).toMonoidHom) (subgroupOfEquivOfLe hKi).injective
    have hle := map_mono (f := D.subtype)
      (le_solvableRadical ((K i).subgroupOf D) hnormal hsolv)
    rwa [map_subgroupOf_eq_of_le hKi] at hle
  have ht : solvableRadical D = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨y,hy,he⟩ := hr x.property
    exact D.subtype_injective he ▸ hy
  let : Group.IsSolvable (⊤ : Subgroup D) := ht ▸ inferInstanceAs (Group.IsSolvable (solvableRadical D))
  exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := D)).toMonoidHom) Subgroup.topEquiv.surjective

theorem IsComponent.local_adjoin_isSolvable {p : ℕ} [Fact p.Prime]
    {L K A : Subgroup G} (hL : IsComponent G L) (hKL : K ≤ L)
    (hA : IsPGroup p A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hK : Group.IsSolvable K) : Group.IsSolvable (K ⊔ A : Subgroup G) := by
  have hD : Group.IsSolvable (componentOrbit K A) := by
    apply isSolvable_iSup_of_normalizes
    · intro a
      let := hK
      exact Group.isSolvable_of_surjective
        ((MulAut.conj (a : G)).toMonoidHom.subgroupMap_surjective K)
    · intro a b
      exact hL.local_conjugates_normalize hKL hinv b a
  let D := (componentOrbit K A).subgroupOf (K ⊔ A)
  let : D.Normal := componentOrbit_normal_subgroupOf_sup K A
  let : Group.IsSolvable D := by
    let := hD
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (componentOrbit_le_sup K A)).toMonoidHom)
      (subgroupOfEquivOfLe (componentOrbit_le_sup K A)).injective
  let := (local_orbit_quotient_isPGroup K A hA).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient D).mpr ⟨inferInstance,inferInstance⟩

theorem IsComponent.relative_local_adjoin_isSolvable {p : ℕ} [Fact p.Prime]
    {H L K A : Subgroup G} (hL : IsComponent H (L.subgroupOf H))
    (hLH : L ≤ H) (hKL : K ≤ L) (hAH : A ≤ H) (hA : IsPGroup p A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hK : Group.IsSolvable K) : Group.IsSolvable (K ⊔ A : Subgroup G) := by
  let F := K.subgroupOf H
  let B := A.subgroupOf H
  have hKH : K ≤ H := hKL.trans hLH
  have hinvH : B ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv hx
  have hF : Group.IsSolvable F := by
    let := hK
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).injective
  let : Group.IsSolvable (F ⊔ B : Subgroup H) := hL.local_adjoin_isSolvable (subgroupOf_mono H hKL) hA.comap_subtype hinvH hF
  have hm : (F ⊔ B).map H.subtype = K ⊔ A := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hAH]
  rw [← hm]
  exact Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective (F ⊔ B))
end Theory.GroupTheory
