module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.Model
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Data
public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.CycleSimplicity.Arithmetic

/-!
# Separate geometric and algebraic inputs to the two middle factors

`Coordinates` requires an invariant subspace of the literal canonical coset
representation and equivariant coordinates on its literal two quotients.
It asserts no simplicity. The two independent `BinaryDensity` statements
concern fixed binary matrices; scalar extension of the full matrix algebra
will prove simplicity over every characteristic-two coefficient field.

These are explicit outstanding inputs, not certificates of their existence.
The parent `MiddleFactors` module consumes all three and retains final assembly.
Source motivation: Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

universe v

/-- Density over the prime field, which is stronger than irreducibility only
over that field and suffices for simplicity after any scalar extension. -/
def BinaryDensity {d : ℕ} (A : Fin 2 → Matrix (Fin d) (Fin d) (ZMod 2)) : Prop :=
  ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)),
    (∀ j, A j ∈ Q) → Q = ⊤

/-- Actual subspace and coordinates; every group element here belongs to the
canonical antidiagonal SU₃, and both actions are literal quotient actions. -/
structure Coordinates (K : Type v) [Field K] [CharP K 2] where
  space : Subrepresentation (functionAction (K := K) (G := CanonicalGroup) (Ω := CanonicalPoints))
  constants_le : constants ≤ space
  le_augmentation : space ≤ augmentationKernel
  actors : Fin 2 → CanonicalGroup
  lower : (space.toSubmodule ⧸ (within constants space).toSubmodule) ≃ₗ[K] (Fin 104 → K)
  upper : (augmentationKernel.toSubmodule ⧸ (within space augmentationKernel).toSubmodule)
    ≃ₗ[K] (Fin 20 → K)
  lower_action : ∀ j v, lower ((within constants space).quotientRepresentation (actors j) v) =
    (CycleCertificate.castMatrix K (factor104 j)).mulVec (lower v)
  upper_action : ∀ j v, upper ((within space augmentationKernel).quotientRepresentation (actors j) v) =
    (CycleCertificate.castMatrix K (factor20 j)).mulVec (upper v)

/-- The geometric realization remains uniform in the original coefficient field. -/
def CanonicalCoordinates : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2], Nonempty (Coordinates K)

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors
