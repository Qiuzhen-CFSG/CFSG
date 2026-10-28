module
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Movement inside the image of an equivariant injection

An equivariant injection embeds the displacement space into the ambient
operator's displacement restricted to any subspace containing its image.
That subspace need not be invariant. This retains passive natural-module
coordinates when bounding the original chief sections in the cubic count.
Source: Aschbacher--Smith, 3.1.9(6), printed p.578, refs/quasithin.pdf.
The original application is Chapter8/MathieuShadowRows/OriginalChiefMovement.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace MathieuCode.NormalizedShadowRows.CubicMovement
variable {G K V W : Type*} [Group G] [Group K]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- An equivariant injection with image in C compares displacement with the
restriction of the ambient displacement to C; C need not be invariant. -/
theorem fixedCodim_le_range_on_subspace
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) K W)
    (g : G) (b : K) (f : V →ₗ[ZMod 2] W) (hf : Function.Injective f)
    (he : ∀ v, f (ρ g v) = σ b (f v))
    (C : Submodule (ZMod 2) W) (hC : ∀ v, f v ∈ C) :
    fixedCodim ρ (zpowers g) ≤ Module.finrank (ZMod 2)
      (LinearMap.range ((σ b - LinearMap.id).domRestrict C)) := by
  let δ := (σ b - LinearMap.id).domRestrict C
  let j : LinearMap.range (ρ g - LinearMap.id) →ₗ[ZMod 2] LinearMap.range δ :=
    (f.comp (LinearMap.range (ρ g - LinearMap.id)).subtype).codRestrict _ (by
      rintro ⟨x,v,rfl⟩
      refine ⟨⟨f v,hC v⟩,?_⟩
      change σ b (f v) - f v = f (ρ g v - v)
      rw [map_sub,he])
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact LinearMap.finrank_le_finrank_of_injective hj

end MathieuCode.NormalizedShadowRows.CubicMovement
end
