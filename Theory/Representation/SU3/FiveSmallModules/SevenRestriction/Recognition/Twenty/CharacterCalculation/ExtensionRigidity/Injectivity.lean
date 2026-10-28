module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.BorelTransport
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.LinearSystem
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.ReferenceFieldTransport
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.TableRealization

/-!
# Applying the degree-twenty Bruhat certificate to actual representations

The kernel-checked coefficient system is injective over any field of
characteristic two. The actual 126-coset quotient realizes its marked matrices;
entrywise field transport supplies the reference model over every order-25
matrix field. Borel comparison then transports its basis to the arbitrary
input representation. In this basis, two values of the literal root-center-coset
operator are the checked system, proving `twenty_rootCoset_injectivity` over
the original coefficient field with every realization premise discharged.

Source of the equations: Huppert II.10.12, via `ExtensionRigidity.Averaging`.
The finite witnesses come from the actual 126-coset model; see `Injectivity/source/README.md`.
-/

@[expose] public section

open scoped BigOperators Matrix
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The coordinate certificate applies to the literal root-center sum. -/
theorem rootCosetOperator_matrix (τ : Representation K J.specialSubgroup V)
    (C : Coordinates J hJ τ) (X : Module.End K V) (s : Fin 2) :
    LinearMap.toMatrixAlgEquiv C.basis (rootCosetOperator J hJ τ X (C.point s)) =
      Certificate.system (LinearMap.toMatrixAlgEquiv C.basis X) s := by
  classical
  let := Fintype.ofFinite (center (hermitianUnipotentCoord J))
  simp only [rootCosetOperator, map_sum, bruhatTerm_coefficients, map_mul,
    C.left_eq, C.right_eq, Certificate.system]
  exact Equiv.sum_comp C.centerEquiv (fun t : Fin 5 =>
    Certificate.matrix (K := K) (Certificate.Data.leftRows s t) *
      LinearMap.toMatrixAlgEquiv C.basis X *
        Certificate.matrix (K := K) (Certificate.Data.rightRows s t))

/-- Checked coefficient arithmetic gives injectivity whenever the actual
Borel actors have the specified marked coordinates. -/
theorem rootCosetOperator_injective_of_coordinates [CharP K 2]
    (τ : Representation K J.specialSubgroup V) (C : Coordinates J hJ τ) :
    Function.Injective (rootCosetOperator J hJ τ) := by
  intro X Y h
  apply (LinearMap.toMatrixAlgEquiv C.basis).injective
  apply Certificate.system_injective
  funext s
  rw [← rootCosetOperator_matrix J hJ τ C X s,
    ← rootCosetOperator_matrix J hJ τ C Y s, h]

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
universe v

/-- Marked coordinates suffice for the exact uniform injectivity contract. -/
theorem twenty_rootCoset_injectivity_of_coordinates
    (hcoords : TwentyBruhatCoordinates.{v}) : TwentyRootCosetInjectivity.{v} := by
  intro F _ _ J hc hconj K _ _ _ U _ _ _ ρ hdim hcenter hfix
  obtain ⟨C⟩ := hcoords F J hc hconj K U ρ hdim hcenter hfix
  exact ExtensionRigidity.Injectivity.rootCosetOperator_injective_of_coordinates
    (FormTransport.standardForm J) rfl ρ C

/-- A reference realization suffices for the exact original injectivity
contract; no whole-group recognition is used. -/
theorem twenty_rootCoset_injectivity_of_reference_models
    (hmodels : TwentyBruhatReferenceModels.{v}) : TwentyRootCosetInjectivity.{v} :=
  twenty_rootCoset_injectivity_of_coordinates
    (twenty_bruhat_coordinates_of_reference_models hmodels)

/-- The actual averaged Bruhat operator is injective for every representation
in the original degree-twenty contract. The genuine coset quotient and its
field transport discharge all marked-coordinate premises. -/
theorem twenty_rootCoset_injectivity : TwentyRootCosetInjectivity.{v} :=
  twenty_rootCoset_injectivity_of_reference_models
    (twenty_bruhat_reference_models_of_table twenty_table_bruhat_models)

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
