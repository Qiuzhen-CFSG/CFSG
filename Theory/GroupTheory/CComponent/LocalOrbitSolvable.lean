module
public import Theory.GroupTheory.ComponentLocalOrbitSolvable
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SolvableMutualCommutator

/-!
# Solvable subgroups in C-component orbits

Pass to the solvable-radical quotient, where the C-component is an ordinary
component. Its solvable local subgroup and its conjugates commute whenever
their components differ. Normalizer lifting preserves the exact stabilizer
condition; solvability then lifts back through the radical.

The relative version retains the specified ambient overgroup. This is the
solvable-parabolic orbit argument of Aschbacher--Smith 14.6.20, printed p.1037.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem IsCComponent.local_adjoin_isSolvable {p : ℕ} [Fact p.Prime]
    {L K A : Subgroup G} (hL : L.IsCComponent) (hKL : K ≤ L)
    (hA : IsPGroup p A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hK : Group.IsSolvable K) : Group.IsSolvable (K ⊔ A : Subgroup G) := by
  let R := solvableRadical G
  let q := QuotientGroup.mk' R
  have hLq : IsComponent (G ⧸ R) (L.map q) := map_cComponent_isComponent_of_solvableRadical hL
  have hn : A.map q ⊓ normalizer (L.map q : Set (G ⧸ R)) ≤ normalizer (K.map q : Set (G ⧸ R)) := by
    rintro x ⟨⟨a,ha,rfl⟩,hx⟩
    have haN : a ∈ normalizer (L : Set G) := by
      have hh : a ∈ (normalizer (L.map q : Set (G ⧸ R))).comap q := hx
      rwa [normalizer_cComponent_quotient hL R] at hh
    exact K.le_normalizer_map q (mem_map_of_mem q (hinv ⟨ha,haN⟩))
  let := hK
  have hs : Group.IsSolvable (K.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective K)
  have hsQ := hLq.local_adjoin_isSolvable (map_mono hKL) (hA.map q) hn hs
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  apply (Group.isSolvable_map_iff_of_solvable_ker q _).mp
  rwa [map_sup]

theorem IsCComponent.relative_local_adjoin_isSolvable {p : ℕ} [Fact p.Prime]
    {H L K A : Subgroup G} (hL : (L.subgroupOf H).IsCComponent)
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
  let : Group.IsSolvable (F ⊔ B : Subgroup H) :=
    hL.local_adjoin_isSolvable (subgroupOf_mono H hKL) hA.comap_subtype hinvH hF
  have hm : (F ⊔ B).map H.subtype = K ⊔ A := by
    rw [map_sup, map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hAH]
  rw [← hm]
  exact Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective (F ⊔ B))
end Subgroup
