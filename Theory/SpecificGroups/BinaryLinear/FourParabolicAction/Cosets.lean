module
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Parabolic cosets and their actual subspaces

For a surjective binary linear action, left cosets of the preimage of a
parabolic correspond to subspaces of the same dimension as its marked
subspace. The representative g maps to the image of that subspace under g.
Equality of images is proved equivalent to the literal left-coset relation,
and extension of subspace isomorphisms proves surjectivity. The resulting
bijection respects the action on subspaces.

The source consumer is the point residue of the Mathieu geometry in
Aschbacher, *Sporadic Groups* (1994), 41.1, pp.219–220.
-/

public noncomputable section
namespace BinaryLinear.FourParabolicAction
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]


theorem map_eq_map_iff (W : Submodule (ZMod 2) V) (a b : GL V) :
    W.map a.toLinearMap = W.map b.toLinearMap ↔ a⁻¹ * b ∈ parabolic W := by
  constructor
  · intro he v
    change a.symm (b v) ∈ W ↔ v ∈ W
    rw [← Submodule.mem_map_equiv, he, Submodule.mem_map_equiv]
    simp
  · intro h
    apply Submodule.ext
    intro v
    rw [Submodule.mem_map_equiv, Submodule.mem_map_equiv]
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply] using h (b.symm v)

variable {K : Type*} [Group K] (ρ : K →* GL V) (W : Submodule (ZMod 2) V)

/-- The Grassmannian containing the marked subspace. -/
abbrev SameDimension := {U : Submodule (ZMod 2) V //
  Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) W}

/-- Left cosets of the literal parabolic map to images of the marked subspace. -/
def cosetToSubspace : (K ⧸ (parabolic W).comap ρ) → SameDimension W :=
  Quotient.lift (fun a : K => ⟨W.map (ρ a).toLinearMap, (ρ a).finrank_map_eq W⟩)
    (by
      intro a b hab
      apply Subtype.ext
      apply (map_eq_map_iff W (ρ a) (ρ b)).mpr
      have hab := QuotientGroup.leftRel_apply.mp hab
      change ρ (a⁻¹ * b) ∈ parabolic W at hab
      simpa only [map_mul, map_inv] using hab)

@[simp] theorem cosetToSubspace_mk (g : K) :
    (cosetToSubspace ρ W (QuotientGroup.mk g)).val = W.map (ρ g).toLinearMap := by rfl

variable [FiniteDimensional (ZMod 2) V]

theorem cosetToSubspace_bijective (hρ : Function.Surjective ρ) :
    Function.Bijective (cosetToSubspace ρ W) := by
  constructor
  · intro q r
    induction q using QuotientGroup.induction_on with
    | H a =>
      induction r using QuotientGroup.induction_on with
      | H b =>
        intro he
        apply QuotientGroup.eq.mpr
        change ρ (a⁻¹ * b) ∈ parabolic W
        rw [map_mul, map_inv]
        exact (map_eq_map_iff W (ρ a) (ρ b)).mp (congrArg Subtype.val he)
  · intro U
    obtain ⟨g, hg⟩ := exists_linearEquiv_map_eq W U.val U.property.symm
    obtain ⟨a, rfl⟩ := hρ g
    exact ⟨QuotientGroup.mk a, Subtype.ext hg⟩

/-- The natural action identifies the parabolic cosets with the actual Grassmannian. -/
def cosetSubspaceEquiv (hρ : Function.Surjective ρ) :
    (K ⧸ (parabolic W).comap ρ) ≃ SameDimension W :=
  Equiv.ofBijective (cosetToSubspace ρ W) (cosetToSubspace_bijective ρ W hρ)

@[simp] theorem cosetSubspaceEquiv_mk (hρ : Function.Surjective ρ) (g : K) :
    (cosetSubspaceEquiv ρ W hρ (QuotientGroup.mk g)).val =
      W.map (ρ g).toLinearMap := by rfl

/-- The identification respects left multiplication and the natural linear action. -/
theorem cosetSubspaceEquiv_smul (hρ : Function.Surjective ρ) (g : K)
    (q : K ⧸ (parabolic W).comap ρ) :
    (cosetSubspaceEquiv ρ W hρ (g • q)).val =
      (cosetSubspaceEquiv ρ W hρ q).val.map (ρ g).toLinearMap := by
  induction q using QuotientGroup.induction_on with
  | H a =>
    change W.map (ρ (g * a)).toLinearMap =
      (W.map (ρ a).toLinearMap).map (ρ g).toLinearMap
    rw [map_mul, ← Submodule.map_comp]
    rfl

end BinaryLinear.FourParabolicAction
