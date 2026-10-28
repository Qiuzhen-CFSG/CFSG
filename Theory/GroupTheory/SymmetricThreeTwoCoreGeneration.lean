module

public import Theory.GroupTheory.PlaneCoreNormalClosure
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Two-subgroup generation over a symmetric-three core quotient

A nontrivial two-subgroup of S₃ has order two and normally generates S₃.
Lifting through the actual two-core proves that its intersection is a hyperplane
and its conjugate span, together with the core, fills the group. The ambient
form preserves the literal inclusion and quotient maps.

Source application: Aschbacher--Smith, final proof of 12.9.1, printed pp.863--864.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

private theorem permThree_twoSubgroup_card (A : Subgroup (Equiv.Perm (Fin 3)))
    (ht : IsPGroup 2 A) (hne : A ≠ ⊥) : Nat.card A = 2 := by
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd : Nat.card A ∣ 6 := hc ▸ A.card_subgroup_dvd_card
  obtain ⟨n, hn⟩ := ht.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) 3 := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card A ∣ 2 := hcop.dvd_mul_right.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
  · exact (hne (Subgroup.card_eq_one.mp h1)).elim
  · exact h2
/-- A two-subgroup escaping the core has a hyperplane in it and normally generates modulo it. -/
theorem two_subgroup_symmetricThree_core
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3))
    (A : Subgroup G) (hA : IsPGroup 2 A) (hne : ¬ A ≤ pCore 2 G) :
    (A ⊓ pCore 2 G).relIndex A = 2 ∧ conjugateSpanBy A ⊤ ⊔ pCore 2 G = ⊤ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hne' : A.map f ≠ ⊥ := by
    intro he
    exact hne (hk ▸ (map_eq_bot_iff _).mp he)
  have hcard := permThree_twoSubgroup_card (A.map f) (hA.map f) hne'
  constructor
  · rw [inf_relIndex_left, ← hk, relIndex_ker, hcard]
  · have he : (conjugateSpanBy A ⊤).map f = ⊤ := by
      rw [map_conjugateSpanBy, map_top_of_surjective _ hf]
      exact permThree_conjugateSpan_eq_top _ hcard
    have hh := congrArg (Subgroup.comap f) he
    simpa only [comap_map_eq, hk, comap_top] using hh

/-- The same assertions in the original ambient group, retaining the embedded core. -/
theorem core_hyperplane_and_generation
    (H A : Subgroup G) (hAH : A ≤ H) (hA : IsPGroup 2 A)
    (hAQ : ¬ A ≤ H.pCoreIn 2)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    (A ⊓ H.pCoreIn 2).relIndex A = 2 ∧ conjugateSpanBy A H ⊔ H.pCoreIn 2 = H := by
  have hpre : ¬ A.subgroupOf H ≤ pCore 2 H := by
    intro hh
    apply hAQ
    intro a ha
    exact mem_map_of_mem H.subtype (hh (show (⟨a,hAH ha⟩ : H) ∈ A.subgroupOf H from ha))
  obtain ⟨hi, hg⟩ := two_subgroup_symmetricThree_core e (A.subgroupOf H) hA.comap_subtype hpre
  have hmap : (A.subgroupOf H ⊓ pCore 2 H).map H.subtype = A ⊓ H.pCoreIn 2 := by
    rw [map_inf _ _ _ H.subtype_injective, map_subgroupOf_eq_of_le hAH]
    rfl
  constructor
  · have hh := relIndex_map_map_of_injective (f := H.subtype)
      (A.subgroupOf H ⊓ pCore 2 H) (A.subgroupOf H) H.subtype_injective
    rwa [hmap, map_subgroupOf_eq_of_le hAH, hi] at hh
  · have hh := congrArg (Subgroup.map H.subtype) hg
    simpa only [Subgroup.map_sup, map_conjugateSpanBy, map_subgroupOf_eq_of_le hAH,
      ← MonoidHom.range_eq_map, H.range_subtype, pCoreIn] using hh

end Subgroup
