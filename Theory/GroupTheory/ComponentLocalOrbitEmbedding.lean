module

public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Characteristic p for local orbits in an ambient embedding

If L is a component of H, K ≤ L has characteristic p, and the stabilizer of L
in a p-subgroup A ≤ H normalizes K, then ⟨K,A⟩ has characteristic p. The
component-orbit theorem is applied inside H, where component subnormality
holds. Faithful embedding transports the resulting intrinsic core and
centralizer bound into the larger group G.

This is the relative-normality form used in Aschbacher–Smith 2.3.9(7),
printed p.526. Neither H nor L is assumed normal in G, and A may permute
the components of H. Nontrivial centers of components are allowed.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- Apply the component-orbit centralizer theorem inside H and embed its
conclusion in G. Only the stabilizer of L must normalize K. -/
theorem IsComponent.relative_local_adjoin_centralizer
    {H L K A : Subgroup G} (hL : IsComponent H (L.subgroupOf H))
    (hLH : L ≤ H) (hKL : K ≤ L) (hAH : A ≤ H) (hA : IsPGroup p A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (hself : K ⊓ centralizer (K.pCoreIn p : Set G) ≤ K.pCoreIn p) :
    (K ⊔ A) ⊓ centralizer ((K ⊔ A).pCoreIn p : Set G) ≤ (K ⊔ A).pCoreIn p := by
  let F := K.subgroupOf H
  let B := A.subgroupOf H
  have hKH : K ≤ H := hKL.trans hLH
  have hFL : F ≤ L.subgroupOf H := subgroupOf_mono H hKL
  have hmF : F.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hmB : B.map H.subtype = A := map_subgroupOf_eq_of_le hAH
  have hinvH : B ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq hLH, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv hx
  have hselfF : F ⊓ centralizer (F.pCoreIn p : Set H) ≤ F.pCoreIn p := by
    apply (inf_centralizer_map_le_iff F (F.pCoreIn p) H.subtype H.subtype_injective).mp
    rw [map_pCoreIn_of_injective p F H.subtype H.subtype_injective, hmF]
    exact hself
  have hc := hL.local_adjoin_centralizer hFL hA.comap_subtype hinvH hselfF
  have hmX : (F ⊔ B).map H.subtype = K ⊔ A := by rw [Subgroup.map_sup, hmF, hmB]
  have hmc : ((F ⊔ B).pCoreIn p).map H.subtype = (K ⊔ A).pCoreIn p := by
    rw [map_pCoreIn_of_injective p _ H.subtype H.subtype_injective, hmX]
  have hcG := (inf_centralizer_map_le_iff (F ⊔ B)
    ((F ⊔ B).pCoreIn p) H.subtype H.subtype_injective).mpr hc
  rwa [hmX, hmc] at hcG

end Theory.GroupTheory

end
