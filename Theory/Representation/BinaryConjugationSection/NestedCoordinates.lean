module
public import Theory.Representation.BinaryConjugationSection
public import Mathlib.Algebra.Module.ZMod

/-!
# Maps between nested binary sections

For A ≤ C and B ≤ D, the literal coordinate maps on A/B and C/D
induce a linear map. It commutes with every pair of actors representing
the same ambient group element. Neither equal numerators nor equal
kernels are required, and the construction retains both coordinate maps.

The first tensor in Aschbacher--Smith, The Classification of Quasithin
Groups, 13.8.29(3),(5), printed p.964, uses this map from U₀/V₂ to V_H/U_H.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.BinaryConjugationSection
variable {G E W : Type*} [Group G]
  [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup W] [Module (ZMod 2) W]

/-- Nested numerator and denominator inclusions descend the original coordinate
maps. Equal ambient actors induce the same intertwining identity. -/
theorem exists_nested_coordinate_map
    {H K A B C D : Subgroup G}
    {ρ : Representation (ZMod 2) H E} {ξ : Representation (ZMod 2) K W}
    (c : BinaryConjugationSection H A B ρ)
    (d : BinaryConjugationSection K C D ξ) (hAC : A ≤ C) (hBD : B ≤ D) :
    ∃ F : E →ₗ[ZMod 2] W,
      (∀ a : A, F (c.coordinates a).toAdd = (d.coordinates (inclusion hAC a)).toAdd) ∧
      ∀ (h : H) (k : K), (h:G) = (k:G) → ∀ x, F (ρ h x) = ξ k (F x) := by
  let q := d.coordinates.comp (inclusion hAC)
  have hk : c.coordinates.ker ≤ q.ker := by
    intro a ha
    exact (d.coordinates_eq_one_iff _).mpr (hBD ((c.coordinates_eq_one_iff a).mp ha))
  let f : Multiplicative E →* Multiplicative W :=
    c.coordinates.liftOfSurjective c.onto ⟨q,hk⟩
  have hf (a : A) : f (c.coordinates a) = q a :=
    c.coordinates.liftOfRightInverse_comp_apply _ _ _ a
  let F : E →ₗ[ZMod 2] W := (AddMonoidHom.toMultiplicative.symm f).toZModLinearMap 2
  have hF (a : A) : F (c.coordinates a).toAdd =
      (d.coordinates (inclusion hAC a)).toAdd := hf a
  refine ⟨F,hF,?_⟩
  intro h k he x
  obtain ⟨a,ha⟩ := c.onto (Multiplicative.ofAdd x)
  have hx : (c.coordinates a).toAdd = x := congrArg Multiplicative.toAdd ha
  rw [←hx,←c.equivariant,hF,hF,←d.equivariant]
  congr 2
  exact Subtype.ext (by change (h:G) * a * (h:G)⁻¹ = (k:G) * a * (k:G)⁻¹; rw [he])
end Representation.BinaryConjugationSection
