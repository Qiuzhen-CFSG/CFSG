module
public import Theory.Representation.BinaryEndpointInduction.SurvivorModels
public import Theory.Representation.BinaryEndpointInduction.CosetTransitions

/-!
# The original endpoint parabolic fixes no survivor vector

The four literal parabolic actors already have zero common fixed space in
both recognized survivors. The finite check uses the explicit standard
model matrices, including the inverse for the original left action.
-/
public section
open Matrix
open scoped MatrixGroups
namespace BinaryEndpointInduction

private theorem fixed_check : ∀ (dual : Bool)
    (x : Fin (if dual then 4 else 6) → ZMod 2),
    (∀ k : Fin 4, x ᵥ* survivorModelMatrix dual ((parabolicGenerator k)⁻¹)=x) → x=0 := by
  decide +kernel

/-- The same marked endpoint parabolic has no nonzero common fixed vector
on either whole-module survivor. -/
theorem survivor_parabolic_fixed_eq_zero (dual : Bool)
    (x : Fin (if dual then 4 else 6) → ZMod 2)
    (hx : ∀ k : Fin 4, x ᵥ* survivorModelMatrix dual ((parabolicGenerator k)⁻¹)=x) :
    x=0 := fixed_check dual x hx

end BinaryEndpointInduction
