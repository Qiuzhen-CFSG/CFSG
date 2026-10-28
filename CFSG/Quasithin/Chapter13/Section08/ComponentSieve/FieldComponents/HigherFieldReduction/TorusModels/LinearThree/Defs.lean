module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.SpecificGroups.PSL3.CartanActions.BorelResidual
public import Theory.GroupAction.Defs

/-!
# The intrinsic actor boundary for the linear degree-three calculation

The source Borel is the normalizer of the specified Sylow two-subgroup;
B is its two-residual. Fixation means pointwise fixation of
O³(B)O₂(B)/O₂(B), expressed by actual automorphism displacements in D.
The inner Sylow is the image under conjugation, so no faithful ambient
extension or missing action kernel is asserted by these definitions.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
variable {D : Type*} [Group D]

/-- The source B inside its actual carrier, at the specified Sylow subgroup. -/
def intrinsicResidual (S : Sylow 2 D) : Subgroup D :=
  borelResidual (normalizer (S : Set D))

/-- Actual pointwise fixation of the residual torus section. -/
def FixesResidualTorus (B : Subgroup D) (α : MulAut D) : Prop :=
  ∀ x ∈ residualIn 3 B ⊔ B.pCoreIn 2, α x * x⁻¹ ∈ B.pCoreIn 2

/-- The inner image may have a kernel; it is not identified with the ambient Sylow. -/
def innerSylow (S : Sylow 2 D) : Subgroup (MulAut D) :=
  (S : Subgroup D).map MulAut.conj

/-- The explicit Sylow-stability hypothesis on a subgroup of actual automorphisms. -/
def StabilizesSylow (A : Subgroup (MulAut D)) (S : Sylow 2 D) : Prop :=
  ∀ α ∈ A, (S : Subgroup D).map α.toMonoidHom = S

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
