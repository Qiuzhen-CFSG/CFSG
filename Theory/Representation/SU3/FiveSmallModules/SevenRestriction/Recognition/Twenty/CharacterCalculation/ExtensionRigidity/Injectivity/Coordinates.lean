module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.Data


/-!
# Marked coefficients for the averaged Bruhat calculation

The finite arithmetic certificate can be applied only after identifying both
literal Bruhat coefficients in a genuine basis. `Coordinates` records this
identification for two actual root-center cosets. It contains no injectivity
or Weyl-comparison assertion. `TwentyBruhatCoordinates` states the outstanding
uniform realization problem, retaining every original hypothesis.

Source of the actor formulas: Huppert II.10.12, proved in `Averaging`.
The constants come from the retained 126-coset calculation; see `source/README.md`.
-/

@[expose] public section

open Module
open scoped BigOperators Matrix
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Left coefficient of the literal Bruhat term, zero on the omitted term. -/
noncomputable def leftCoefficient (τ : Representation K J.specialSubgroup V)
    (z : hermitianUnipotentCoord J) : Module.End K V :=
  if hz : z.val.2 = 0 then 0 else
    τ (hermitianUnipotentSU J hJ (hermitianBruhatLeft J z hz) *
      hermitianTorusSU J hJ (Units.mk0 z.val.2 hz))

/-- Right coefficient of the literal Bruhat term, zero on the omitted term. -/
noncomputable def rightCoefficient (τ : Representation K J.specialSubgroup V)
    (z : hermitianUnipotentCoord J) : Module.End K V :=
  if hz : z.val.2 = 0 then 0 else
    τ (hermitianUnipotentSU J hJ (hermitianBruhatRight J z hz))

theorem bruhatTerm_coefficients (τ : Representation K J.specialSubgroup V)
    (X : Module.End K V) (z : hermitianUnipotentCoord J) :
    bruhatTerm J hJ τ X z = leftCoefficient J hJ τ z * X * rightCoefficient J hJ τ z := by
  unfold bruhatTerm leftCoefficient rightCoefficient
  split_ifs <;> simp

/-- An actual basis and two actual root-center cosets with the marked
coefficients used by the finite certificate. No injectivity is a field. -/
structure Coordinates (τ : Representation K J.specialSubgroup V) where
  basis : Basis (Fin 20) K V
  point : Fin 2 → hermitianUnipotentCoord J
  centerEquiv : center (hermitianUnipotentCoord J) ≃ Fin 5
  left_eq (s : Fin 2) (c : center (hermitianUnipotentCoord J)) :
    LinearMap.toMatrixAlgEquiv basis (leftCoefficient J hJ τ (point s * c.val)) =
      Certificate.matrix (Certificate.Data.leftRows s (centerEquiv c))
  right_eq (s : Fin 2) (c : center (hermitianUnipotentCoord J)) :
    LinearMap.toMatrixAlgEquiv basis (rightCoefficient J hJ τ (point s * c.val)) =
      Certificate.matrix (Certificate.Data.rightRows s (centerEquiv c))

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open Degrees.RootEigenline
universe v

/-- The remaining structural input for the checked two-coset certificate:
realize its marked Borel coefficients over the original coefficient field. -/
def TwentyBruhatCoordinates : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
    Nat.card F = 5 ^ 2 → (∀ x, J.conj x = x ^ 5) →
    ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      (U : Type v) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
      (ρ : Representation K (standardGroup J) U),
      Module.finrank K U = 20 →
      Subgroup.center (standardGroup J) ≤ ρ.ker →
      invariants (ρ.comp (standardRootCenter J).subtype) = ⊥ →
      Nonempty (ExtensionRigidity.Injectivity.Coordinates (FormTransport.standardForm J) rfl ρ)

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
