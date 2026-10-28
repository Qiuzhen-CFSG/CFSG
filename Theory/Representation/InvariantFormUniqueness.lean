module
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Invariant bilinear forms on an absolutely irreducible module

A nondegenerate invariant form identifies the module with its dual. Any other
invariant form then defines an equivariant endomorphism, which is scalar by
absolute irreducibility. This is the change-of-form step used to recognize
finite classical-group modules without a rank-one element inside the actor.
-/

public noncomputable section
namespace Representation
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (ρ : Representation F G V) [ρ.IsIrreducible]
  [ρ.IsAbsolutelyIrreducible]

/-- A nondegenerate invariant bilinear form spans all invariant bilinear forms. -/
theorem invariant_form_scalar_of_absolutelyIrreducible
    (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (hBinv : ∀ a v w, B (ρ a v) (ρ a w) = B v w)
    (C : LinearMap.BilinForm F V)
    (hCinv : ∀ a v w, C (ρ a v) (ρ a w) = C v w) :
    ∃ c : F, C = c • B := by
  let T : Module.End F V := (B.toDual hB).symm.toLinearMap.comp C
  have hT (v w : V) : B (T v) w = C v w :=
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (C v) w
  let f : ρ.IntertwiningMap ρ := {
    toLinearMap := T
    isIntertwining' a := by
      apply LinearMap.ext
      intro v
      apply (B.toDual hB).injective
      apply LinearMap.ext
      intro w
      obtain ⟨w,rfl⟩ := (ρ.apply_bijective a).surjective w
      change B (T (ρ a v)) (ρ a w) = B (ρ a (T v)) (ρ a w)
      rw [hT,hCinv,hBinv,hT] }
  obtain ⟨c,hc⟩ := (isAbsolutelyIrreducible_iff_surjective ρ).mp inferInstance f
  have hc := hc.symm
  refine ⟨c,?_⟩
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  have hf : T v = c • v := congrArg (fun f : ρ.End => f v) hc
  change C v w = c • B v w
  rw [←hT,hf]
  simp only [map_smul,LinearMap.smul_apply]
end Representation
