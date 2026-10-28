module

public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Invariant intervals from irreducible subgroup images

Let q:U→Q have kernel Z and intertwine ambient conjugation by K with
an action on Q. If q(A) has no proper nontrivial invariant subgroup,
then there is no K-invariant subgroup strictly between Z and A.
Map such a subgroup through q and use injectivity of the subgroup
correspondence above the kernel. Surjectivity of q is unnecessary.

The orthogonal lift in Aschbacher–Smith, Lemma 14.4.9, printed p.1010,
uses this with the literal moved image in U/Z(U).
-/

public section
open Subgroup

namespace Subgroup
/-- Irreducibility of the literal image implies the invariant interval property upstairs. -/
theorem invariant_interval_of_image_irreducible
    {G Q : Type*} [Group G] [Group Q]
    (U A Z K : Subgroup G) (hZA : Z ≤ A) (hAU : A ≤ U)
    (hKU : K ≤ normalizer (U : Set G))
    (q : U →* Q) (hker : q.ker = Z.subgroupOf U)
    (ρ : K →* MulAut Q)
    (hρ : ∀ k : K, ∀ u : U, ρ k (q u) =
      q ⟨(k : G) * (u : G) * (k : G)⁻¹,
        (mem_normalizer_iff.mp (hKU k.property) u).mp u.property⟩)
    (hirr : ∀ F : Subgroup Q, F ≤ (A.subgroupOf U).map q →
      (∀ k : K, ∀ v ∈ F, ρ k v ∈ F) → F = ⊥ ∨ F = (A.subgroupOf U).map q) :
    ∀ E : Subgroup G, Z ≤ E → E ≤ A → K ≤ normalizer (E : Set G) →
      E = Z ∨ E = A := by
  intro E hZE hEA hKE
  have hEU := hEA.trans hAU
  have hkerE : q.ker ≤ E.subgroupOf U := by
    rw [hker]
    exact fun _ h => hZE h
  have hkerA : q.ker ≤ A.subgroupOf U := by
    rw [hker]
    exact fun _ h => hZA h
  have hFinv : ∀ k : K, ∀ v ∈ (E.subgroupOf U).map q,
      ρ k v ∈ (E.subgroupOf U).map q := by
    intro k v hv
    obtain ⟨u,hu,rfl⟩ := hv
    rw [hρ]
    exact mem_map_of_mem q ((mem_normalizer_iff.mp (hKE k.property) u).mp hu)
  rcases hirr ((E.subgroupOf U).map q) (map_mono (fun _ h => hEA h)) hFinv with h | h
  · left
    apply le_antisymm _ hZE
    intro e he
    have hh : q (⟨e,hEU he⟩ : U) ∈ (E.subgroupOf U).map q := mem_map_of_mem q he
    rw [h] at hh
    have hk : (⟨e,hEU he⟩ : U) ∈ q.ker := hh
    rw [hker] at hk
    exact hk
  · right
    have hh := map_injective_of_ker_le q hkerE hkerA h
    have hm := congrArg (Subgroup.map U.subtype) hh
    simpa only [map_subgroupOf_eq_of_le hEU, map_subgroupOf_eq_of_le hAU] using hm
end Subgroup

