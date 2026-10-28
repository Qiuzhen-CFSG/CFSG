module
public import Theory.SpecificGroups.SymplecticFour.CentralNaturalDerived
public import Mathlib.GroupTheory.GroupAction.ConjAct
/-!
# The natural-derived bound for actual subgroup conjugation

The actor, moved subgroup, centralizer kernel and coordinates retain their
original embeddings. A derived subgroup centralized by its containing actor
is central in the moved subgroup, so the natural Sp4 field-size bound applies
without a separate class-two or split-extension premise.
Source: MS93 (3.10)(i), printed p.880.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup.ClassTwo
open Theory.SpecificGroups.SymplecticFour
variable {G F : Type*} [Group G] [Field F] [CharP F 2] [Finite F]

/-- The field-size bound on the original embedded derived subgroup. -/
theorem card_derived_le_of_natural_centralizer_section
    (L V : Subgroup G) (hVL : V ≤ L) (hLV : L ≤ normalizer (V : Set G))
    (π : L →* Sp F) (hπ : Function.Surjective π)
    (f : V →* Multiplicative (Vector F)) (hf : Function.Surjective f)
    (hker : f.ker ≤ (centralizer (L : Set G)).comap V.subtype)
    (hequiv : ∀ (a : L) (v : V),
      (f ⟨(a : G) * v * (a : G)⁻¹,
        (mem_normalizer_iff.mp (hLV a.property) v).mp v.property⟩).toAdd =
          π a • (f v).toAdd)
    (hfix : ⁅V,V⁆ ≤ centralizer (L : Set G)) :
    Nat.card (⁅V,V⁆ : Subgroup G) ≤ Nat.card F := by
  let α : L →* MulAut V := V.normalizerMonoidHom.comp (inclusion hLV)
  have hmap : (_root_.commutator V).map V.subtype = ⁅V,V⁆ := by
    rw [map_commutator_eq,range_subtype]
  have hcent : _root_.commutator V ≤ center V := by
    intro c hc
    apply mem_center_iff.mpr
    intro v
    apply Subtype.ext
    exact hfix (hmap ▸ mem_map_of_mem V.subtype hc) v (hVL v.property)
  have hk : f.ker ≤ center V := by
    intro v hv
    apply mem_center_iff.mpr
    intro u
    apply Subtype.ext
    exact hker hv u (hVL u.property)
  have hfixed : ∀ a : L, ∀ c ∈ _root_.commutator V, α a c = c := by
    intro a c hc
    apply Subtype.ext
    change (a : G) * (c : G) * (a : G)⁻¹ = c
    have he := hfix (hmap ▸ mem_map_of_mem V.subtype hc) a a.property
    change (a : G) * (c : G) = (c : G) * a at he
    rw [he,mul_inv_cancel_right]
  rw [←hmap,card_map_of_injective V.subtype_injective]
  exact card_commutator_le_of_symplectic_section hcent α π hπ f hf hk hequiv hfixed
end Subgroup.ClassTwo
