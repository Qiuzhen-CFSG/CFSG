module

public import Theory.GroupTheory.ComponentSaturatedRadical
public import Theory.GroupTheory.RadicalNormalizerControl

/-!
# Cores of overgroups of saturated component normalizers

The radical equation for L∩Q retains its meaning inside the actual carrier L.
If its full normalizer in L lies in K≤L, the core of K is normalized by that
normalizer. The radical-normalizer control theorem therefore puts O_p(K)
inside L∩Q. No normality of L in the ambient group or of R in K is needed.

Source: Aschbacher--Smith 2.5.3(4), printed p.553, the first step when the
component radical normalizer is contained in M, using C.2.1.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- Intrinsic radicality for the literal component intersection. -/
theorem IsComponent.intrinsic_radical_of_saturation
    {L A Q : Subgroup G} (hL : IsComponent G L)
    (hQ : IsPGroup p Q) (hAQ : A ≤ normalizer (Q : Set G))
    (hsat : ∀ P : Subgroup G, IsPGroup p P → A ≤ normalizer (P : Set G) → P ≤ Q) :
    (normalizer (Q.subgroupOf L : Set L)).pCoreIn p = Q.subgroupOf L := by
  let R := L ⊓ Q
  have he : R.subgroupOf L = Q.subgroupOf L := by ext x; simp [R]
  have hmap : (normalizer (Q.subgroupOf L : Set L)).map L.subtype =
      L ⊓ normalizer (R : Set G) := by
    rw [← he, ← subgroupOf_normalizer_eq (show R ≤ L from inf_le_left),
      subgroupOf_map_subtype, inf_comm]
  apply map_injective L.subtype_injective
  rw [map_pCoreIn_of_injective p _ L.subtype L.subtype_injective, hmap,
    hL.pCoreIn_normalizer_intersection_of_saturation hQ hAQ hsat,
    subgroupOf_map_subtype, inf_comm]

/-- A containing local group has its core inside the radical intersection. -/
theorem IsComponent.local_overgroup_core_le_intersection_of_saturation [Fact p.Prime]
    {L A Q : Subgroup G} (hL : IsComponent G L)
    (hQ : IsPGroup p Q) (hAQ : A ≤ normalizer (Q : Set G))
    (hsat : ∀ P : Subgroup G, IsPGroup p P → A ≤ normalizer (P : Set G) → P ≤ Q)
    (K : Subgroup L) (hNK : normalizer (Q.subgroupOf L : Set L) ≤ K) :
    K.pCoreIn p ≤ Q.subgroupOf L := by
  apply le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    (Q.subgroupOf L) (K.pCoreIn p) hQ.comap_subtype (isPGroup_pCoreIn p K)
    (hL.intrinsic_radical_of_saturation hQ hAQ hsat).le
  exact hNK.trans (K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (pCore p K)))

end Theory.GroupTheory
