module
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.RealizationInputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Construction
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Cosets
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.GenerationFromBorel
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Borel
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Density20
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CosetCardinality
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.CentralDescent
/-!
# The genuine degree-twenty table representation

The checked 126-coset enumeration constructs the literal augmentation quotient.
Transport its upper coordinates and the canonical group comparison to obtain
an action on twenty coordinates with the two prescribed generator matrices.
Their proved density gives irreducibility. Central descent then kills the SU
center and the fixed space of the literal root center.

Source: the retained MiddleFactors coset data; Huppert II.10.12–13 and
Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
open HermitianForm.InvolutionConjugateBounds.Five.Embedding
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization
open Degrees.TrivialCalculation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
universe v
noncomputable def enumeration : MiddleFactors.Realization.CosetEnumeration := Classical.choice MiddleFactors.Realization.coset_enumeration
noncomputable def quotientCoordinates (K : Type v) [Field K] [Finite K] [CharP K 2] :
    MiddleFactors.Coordinates K :=
  MiddleFactors.Realization.coordinates K enumeration canonical_borel_coset_card
    (enumeration.generates_of_borel canonical_borel_coset_card MiddleFactors.Realization.tableBorel_le_generated)
variable (K : Type v) [Field K] [Finite K] [CharP K 2]
theorem quotientCoordinates_actors (j : Fin 2) :
    (quotientCoordinates K).actors j = MiddleFactors.Realization.actor j := rfl
attribute [local irreducible] quotientCoordinates
noncomputable def representation : Representation K MiddleFactors.Realization.TableGroup (Fin 20 → K) :=
  (quotientCoordinates K).upper.conjRingEquiv.toMonoidHom.comp
    ((within (quotientCoordinates K).space augmentationKernel).quotientRepresentation.comp
      MiddleFactors.Realization.canonicalEquiv.toMonoidHom)
theorem representation_actor (j : Fin 2) (v : Fin 20 → K) :
    representation K (MiddleFactors.Realization.tableActor j) v =
      (CycleCertificate.castMatrix K (MiddleFactors.factor20 j)).mulVec v := by
  change (quotientCoordinates K).upper
    ((within (quotientCoordinates K).space augmentationKernel).quotientRepresentation
      (MiddleFactors.Realization.actor j) ((quotientCoordinates K).upper.symm v)) = _
  simpa only [quotientCoordinates_actors, LinearEquiv.apply_symm_apply] using
    (quotientCoordinates K).upper_action j ((quotientCoordinates K).upper.symm v)
theorem representation_irreducible : (representation K).IsIrreducible := by
  apply irreducible_of_coordinate_matrices (by decide : 0 < 20) MiddleFactors.Realization.tableActor
    (fun j => CycleCertificate.castMatrix K (MiddleFactors.factor20 j))
    (LinearEquiv.refl K (Fin 20 → K))
  · exact representation_actor K
  · exact MiddleFactors.factor20_density_charTwo K
theorem representation_centers :
    (representation K).ker = Subgroup.center MiddleFactors.Realization.TableGroup ∧
    invariants ((representation K).comp (Degrees.RootEigenline.standardRootCenter MiddleFactors.Realization.tableForm).subtype) = ⊥ := by
  let := representation_irreducible K
  exact irreducible_twenty_kernel_and_root_invariants MiddleFactors.Realization.tableForm F25.card
    F25.conjugation_eq_fifth (representation K) (by simp)
noncomputable def matrixRepresentation : MiddleFactors.Realization.TableGroup →* Matrix (Fin 20) (Fin 20) K :=
  (LinearMap.toMatrixAlgEquiv (Pi.basisFun K (Fin 20))).toMonoidHom.comp (representation K)
theorem matrixRepresentation_actor (j : Fin 2) :
    matrixRepresentation K (MiddleFactors.Realization.tableActor j) = CycleCertificate.castMatrix K (MiddleFactors.factor20 j) := by
  ext i k
  change representation K (MiddleFactors.Realization.tableActor j) (Pi.single k 1) i = _
  rw [representation_actor]
  simp
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization
