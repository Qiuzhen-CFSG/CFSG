module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Displacement ranks in invariant subspaces

The literal inclusion W → U embeds the image of ρ_W(g) − 1 into that of
ρ_U(g) − 1. The injective linear map gives the corresponding finrank bound.
This elementary restriction argument is used in the exceptional tensor branch
of Aschbacher–Smith 13.8.20, printed p.954 (1 March 2004 manuscript).
-/

public section
namespace Subrepresentation
variable {k D U : Type*} [Field k] [Monoid D] [AddCommGroup U] [Module k U]
  {ρ : Representation k D U} (W : Subrepresentation ρ)

/-- Inclusion of an invariant subspace injects its displacement image into the
ambient displacement image. -/
def displacementRangeInclusion (g : D) :
    LinearMap.range (W.toRepresentation g - LinearMap.id) →ₗ[k]
      LinearMap.range (ρ g - LinearMap.id) :=
  ((W.toSubmodule.subtype).comp
    (LinearMap.range (W.toRepresentation g - LinearMap.id)).subtype).codRestrict _ (by
      rintro ⟨v, w, rfl⟩
      exact ⟨w.val, rfl⟩)

/-- The displacement inclusion has zero kernel. -/
theorem displacementRangeInclusion_injective (g : D) :
    Function.Injective (W.displacementRangeInclusion g) := by
  intro v w h
  exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h))

/-- Restriction to an invariant subspace cannot increase displacement rank. -/
theorem finrank_displacement_le [Module.Finite k U] (g : D) :
    Module.finrank k (LinearMap.range (W.toRepresentation g - LinearMap.id)) ≤
      Module.finrank k (LinearMap.range (ρ g - LinearMap.id)) :=
  LinearMap.finrank_le_finrank_of_injective (W.displacementRangeInclusion_injective g)
end Subrepresentation
end
