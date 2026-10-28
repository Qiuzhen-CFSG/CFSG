module

public import Theory.GroupTheory.CComponent.MarkedProductQuotient
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The two quotient obstructions in the linear parabolic reduction

An actual S₃ × S₃ quotient of a solvable overgroup supplies an order-three
lift through the two-core. The theta identity and uniform 13.8.13 place
that lift in L₁, contradicting a marked L₁ image in only the first factor.

For a quotient with a simple perfect second factor, the C-component
correspondence constructs the component over that factor. Uniform
13.8.21(1) then rules out a marked L₁ image outside it. This construction
uses relative C-component membership and the given quotient map.

Source: Aschbacher–Smith 13.8.25, printed pp.959–960 (PDF pp.976–977),
combined manuscript of 1 March 2004. The source placement and construction
of the two overgroups are separate from these quotient deductions.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

variable {G A B : Type*} [Group G] [Group A] [Group B] [Finite G]

/-- Uniform 13.8.21(1) forbids a marked source subgroup outside a specified
simple factor of an actual two-core quotient. The C-component is constructed
by the solvable-kernel correspondence, not assumed. -/
theorem exclude_Hz_of_marked_product_quotient [IsSimpleGroup B] [Group.IsPerfect B]
    (L₁ T G₁ M H₂ : Subgroup G) (hH₂ : H₂ ∈ Source.Hz L₁ T G₁ M)
    (h21 : ∀ (Y D : Subgroup G), Y ∈ Source.Hz L₁ T G₁ M → D ≤ Y →
      (D.subgroupOf Y).IsCComponent → L₁ ≤ D)
    (e : (H₂ ⧸ pCore 2 H₂) ≃* A × B)
    (hmark : ¬ (L₁.subgroupOf H₂).map
      (e.toMonoidHom.comp (QuotientGroup.mk' _)) ≤ (⊥ : Subgroup A).prod ⊤) : False := by
  obtain ⟨D, hD, he⟩ := exists_cComponent_over_right_factor e
  have hsub : (D.map H₂.subtype).subgroupOf H₂ = D :=
    comap_map_eq_self_of_injective H₂.subtype_injective D
  have hLD := h21 H₂ (D.map H₂.subtype) hH₂ (map_subtype_le D) (hsub.symm ▸ hD)
  apply hmark
  rw [← he]
  apply map_mono
  rw [← hsub]
  exact subgroupOf_mono H₂ hLD

/-- The theta identity forces every cubic in a solvable local quotient into
the image of L₁. Hence a solvable S₃ × S₃ quotient cannot have the marked
L₁ image confined to its first factor. -/
theorem exclude_solvable_marked_product (L₁ T G₁ M H Y : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hY : Y ≤ H) (hbase : L₁ ⊔ T ≤ Y)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (hsol : Group.IsSolvable Y)
    (e : (Y ⧸ pCore 2 Y) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hmark : (L₁.subgroupOf Y).map
      (e.toMonoidHom.comp (QuotientGroup.mk' _)) ≤
      (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = pCore 2 Y :=
      (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
    rw [he]
    exact pCore_isPGroup
  let c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hc : orderOf c = 3 := orderOf_eq_prime (by decide) (by decide)
  have ho : orderOf ((1 : Equiv.Perm (Fin 3)), c) = 3 := by
    exact orderOf_eq_prime (by decide) (by decide)
  obtain ⟨x, hx, he⟩ := f.exists_pRegular_lift hf 2 Nat.prime_two (1, c)
    (by rw [ho]; decide)
  have hxo : orderOf x = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x
      (Nat.prime_two.coprime_iff_not_dvd.mpr hx)).symm.trans (he ▸ ho)
  have hYM := h13 Y hbase (hY.trans hH.2.1) hsol
  have hxL : (x : G) ∈ L₁ := by
    rw [htheta]
    exact subset_closure ⟨⟨hY x.property, hYM x.property⟩, (orderOf_coe x).trans hxo⟩
  have hm := hmark (mem_map.mpr ⟨x, hxL, he⟩)
  have hc1 : c = 1 := mem_bot.mp hm.2
  rw [hc1, orderOf_one] at hc
  omega


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
