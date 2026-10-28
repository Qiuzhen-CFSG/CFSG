module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.ChevalleySource.Source
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.ChevalleySource.Endomorphisms
public import Theory.Representation.Triality.RestrictedWeights.ConcreteBasicFamily
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.ClassificationLeft
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights.Graph

/-!
# Concrete rational tensor geometry for Spin D4

The existing Clifford pinning supplies the full Chevalley system and actual
ordinary Frobenius and pinned triality. The torus, Borel, root datum and
character coordinates agree literally with the finite geometry. Consequently
the existing sixteen basic factors feed the proved rational tensor theorems
without a carrier change or an additional representation premise.

Only algebraic universality remains explicit; its source producer is the
separate semisimple-center argument. These conclusions concern rational
representations; finite restriction is handled by its existing source owner.
Sources: GLS3 1.12.1 and 2.8.5--6; Steinberg 13.1.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.RestrictedWeights.SteinbergTensors
namespace Triality.RestrictedWeights.Concrete
@[expose] public noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

/-- Actual Spin root and torus geometry for the rational tensor theorems. -/
def algebraicGeometry : AlgebraicTensor.D4Geometry (groupVariety k) where
  simple := source_simple k
  universal := hu
  torus := CorootTorus.closedSubgroup k
  maximalTorus := CorootTorus.isMaximal k
  roots := pinnedRootData k
  realized := pinnedRootData_isRealization k
  rootEquiv := Equiv.ulift
  based := pinnedRootData_isRootSystemRealization k
  addition := pinnedRootData_isRootAdditionRealization k
  bigCell := OppositeBorels.bigCell k
  characters := weightEquiv k
  coroot_coordinates := weight_coordinate k
  chevalley := ChevalleySource.data k
  chevalley_spec := ChevalleySource.isChevalleySystem k
  rootParam := pinnedRootParametrization k
  rootParam_spec := pinnedRootParametrization_inclusion k
  coroot_spec := pinnedRootData_rootCocharacter k

/-- The original regular ordinary Frobenius, with its root and Borel actions. -/
def ordinaryFrobenius : AlgebraicTensor.OrdinaryFrobenius (algebraicGeometry k hu) where
  morphism := regularFrobeniusLift k 1
  surjective := (regularFrobeniusLift_bijective k 1).2
  root_formula := by
    intro r t
    change (regularFrobeniusLift k 1).onPoints (rootPoint k r.down t) =
      rootPoint k r.down (t^2)
    rw [regularFrobeniusLift_onPoints, GraphField.frobenius_rootPoint]
    simp only [pow_one]
  torus_formula := ChevalleySource.Endomorphisms.frobenius_torus_formula k
  borel_stable := ChevalleySource.Endomorphisms.frobenius_borel_stable k

/-- The original pinned triality with the forward numbered diagram convention. -/
def pinnedTriality : AlgebraicTensor.PinnedTriality (algebraicGeometry k hu) where
  iso := Diagram.pinnedIso k
  root_formula := by
    intro r t
    exact GraphField.diagram_rootPoint k r.down t
  coroot_formula := ChevalleySource.Endomorphisms.diagram_coroot_formula k
  torus_stable := ChevalleySource.Endomorphisms.diagram_torus_stable k
  torus_inverse_stable := ChevalleySource.Endomorphisms.diagram_torus_inverse_stable k
  borel_stable := ChevalleySource.Endomorphisms.diagram_borel_stable k
  borel_inverse_stable := ChevalleySource.Endomorphisms.diagram_borel_inverse_stable k

open D4RestrictedWeight AlgebraicTensor

/-- Irreducibility of the literal tensors of the existing concrete basic family. -/
theorem rationalTensor_irreducible (a : ℕ → BasicWeight) (n : ℕ) :
    IsIrreducibleRepresentation (rationalTensor (basicFamily k hu).factor
      (pointEnd (regularFrobeniusLift k 1)) a n) :=
  leftRationalTensor_irreducible (algebraicGeometry k hu) (ordinaryFrobenius k hu)
    (basicFamily k hu) a n

/-- Unique rational tensor parameters in a specified restricted weight range,
retaining the original basic-family carriers and actual linear intertwiners. -/
theorem rationalTensor_exhaustive (C : RationalFactor (groupVariety k))
    (n : ℕ) (x : Weight) (hx : InRestrictedRange n x)
    (hC : ∃ v, HasHighWeight C.action (finiteGeometry k hu).bigCell.data.B
      (finiteGeometry k hu).torus v ((finiteGeometry k hu).leftWeightEmbedding x)) :
    ∃! a : Fin n → BasicWeight, AreEquivalentRepresentations C.action
      (leftWordTensor (algebraicGeometry k hu) (ordinaryFrobenius k hu)
        (basicFamily k hu) n a).action :=
  leftRationalTensor_exhaustive (algebraicGeometry k hu) (ordinaryFrobenius k hu)
    (basicFamily k hu) C n x hx hC
end
end Triality.RestrictedWeights.Concrete
