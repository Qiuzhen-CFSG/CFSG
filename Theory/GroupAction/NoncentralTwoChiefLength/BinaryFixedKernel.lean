module
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Cubic fixed-index bounds for maps with fixed kernel

A binary equivariant map with fixed kernel preserves the cubic fixed
index when its codomain is restricted to its image. Inclusion of the
image then bounds that index by the index of the full target.

The centralizer quotient in Aschbacher--Smith 13.8.33, printed p.968,
uses this to retain the constant kernel while comparing with a dual cover.
-/

public section
namespace Representation.BinaryFixedPoints
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem fixedIndex_le_of_fixed_kernel [Finite W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (g : G) (hg : ∀ a, a ∈ Subgroup.zpowers g) (hc : g ^ 3 = 1)
    (f : V →ₗ[ZMod 2] W) (heq : ∀ a v, f (ρ a v) = σ a (f v))
    (hker : ∀ v, f v = 0 → ρ g v = v) : fixedIndex ρ ≤ fixedIndex σ := by
  let F := f.intertwiningMap_of_isIntertwiningMap ρ σ heq
  let τ := F.range.toRepresentation
  have he : fixedIndex ρ = fixedIndex τ :=
    fixedIndex_eq_of_surjective_trivial_kernel ρ τ g hg hc f.rangeRestrict
      f.surjective_rangeRestrict (fun a v => Subtype.ext (heq a v))
      (fun v hv => hker v (congrArg Subtype.val hv))
  rw [he]
  let _ := action τ
  let _ := action σ
  exact FixedPoints.index_le_of_injective
    F.range.toSubmodule.subtype.toAddMonoidHom.toMultiplicative
    (fun _ _ h => Subtype.ext h) (fun _ _ => rfl)

end Representation.BinaryFixedPoints
