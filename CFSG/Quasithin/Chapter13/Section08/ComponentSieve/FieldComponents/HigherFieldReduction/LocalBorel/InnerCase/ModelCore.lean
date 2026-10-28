module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ResidualGeneration

/-!
# The full Borel two-core in all seven higher-field models

The intrinsic residual of the Sylow normalizer has two-core equal to the
specified Sylow. Each branch uses its genuine matrix or projective model;
transport uses the given multiplicative equivalence. The symplectic branch
uses the four-root generation proof, including the full unipotent subgroup.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954/PDF p.971.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase
open TorusModels TorusModels.Assembly
universe u v
variable {D : Type u} [Group D] [Finite D]

private theorem core_transport {E : Type v} [Group E]
    (e : D ≃* E) (h : ∀ S : Sylow 2 E, (residualAt S).pCoreIn 2 = S)
    (S : Sylow 2 D) : (residualAt S).pCoreIn 2 = S := by
  let : Finite E := Finite.of_equiv D e.toEquiv
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_pCoreIn_of_injective 2 _ e.toMonoidHom e.injective, residualAt_map, h]
  rfl

/-- The Borel residual retains the entire specified Sylow in every actual model. -/
theorem model_residual_twoCore {n : ℕ} {unitary four : Bool}
    (model : Model.{u,v} D n unitary four) (hn : 1 < n)
    (S : Sylow 2 D) : (residualAt S).pCoreIn 2 = S := by
  cases model with
  | linearTwo F hF e _ =>
    exact core_transport e (LinearTwo.borelResidual_twoCoreIn hn hF) S
  | specialLinearThree F hF e _ =>
    exact core_transport e (LinearThree.special_residual_twoCore hF hn) S
  | projectiveLinearThree F hF e _ =>
    exact core_transport e (LinearThree.projective_residual_twoCore hF hn) S
  | specialUnitaryThree E J hE hconj e _ =>
    exact core_transport e (UnitaryThree.su_borelResidual_twoCore J n hn hE hconj) S
  | projectiveUnitaryThree E J hE hconj e _ =>
    exact core_transport e (UnitaryThree.psu_borelResidual_twoCore J n hn hE hconj) S
  | symplecticFour F hF e _ =>
    exact core_transport e (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.residualAt_twoCore_eq_sylow hF hn) S
  | g2 F hF e _ =>
    exact core_transport e (G2.residual_borelAt_twoCore hF hn) S

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase
