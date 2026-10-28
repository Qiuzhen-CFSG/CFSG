module
public import Theory.GroupTheory.PCoreSurjective

/-!
# Surjections detected by a core quotient and a supplement

A surjection onto a group with trivial p-core kills the source p-core.
Consequently any subgroup mapping onto the source's p-core quotient also
maps onto that target. If a homomorphism kills one of two generating
subgroups, its restriction to the other remains surjective.

These observations identify the complementary factor in the normalizer
quotient of Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(2), printed p.964, without assuming the quotient's product type.
-/

public section
open Subgroup
namespace MonoidHom
variable {A B D R : Type*} [Group A] [Group B] [Group D] [Group R]

/-- Mapping onto a core quotient suffices to cover any core-free image. -/
theorem surjective_comp_of_core_quotient {p : ℕ}
    (f : A →* B) (hf : Function.Surjective f) (hb : pCore p B = ⊥)
    (ψ : A →* D) (hψ : ψ.ker = pCore p A)
    (j : R →* A) (hj : Function.Surjective (ψ.comp j)) :
    Function.Surjective (f.comp j) := by
  have hc : pCore p A ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    apply bot_unique
    rw [←hb]
    exact le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  intro b
  obtain ⟨a,rfl⟩ := hf b
  obtain ⟨r,hr⟩ := hj (ψ a)
  have hk : j r * a⁻¹ ∈ ψ.ker := by
    change ψ (j r * a⁻¹) = 1
    rw [map_mul,map_inv,show ψ (j r) = ψ a from hr,mul_inv_cancel]
  have hh := hc (hψ ▸ hk)
  change f (j r * a⁻¹) = 1 at hh
  rw [map_mul,map_inv,mul_inv_eq_one] at hh
  exact ⟨r,hh⟩

/-- A surjection killing one generating subgroup is onto on the other. -/
theorem surjective_on_supplement
    (I P : Subgroup A) (hIP : I ⊔ P = ⊤)
    (f : A →* B) (hf : Function.Surjective f) (hI : I ≤ f.ker) :
    Function.Surjective (f.comp P.subtype) := by
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp,range_subtype]
  have hh := congrArg (Subgroup.map f) hIP
  rwa [Subgroup.map_sup,(Subgroup.map_eq_bot_iff I).mpr hI,
    bot_sup_eq,map_top_of_surjective f hf] at hh

end MonoidHom
