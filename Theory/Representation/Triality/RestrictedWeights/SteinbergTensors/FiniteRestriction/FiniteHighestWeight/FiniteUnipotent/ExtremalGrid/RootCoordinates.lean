module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.RegularFunctions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Spaces
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Scalars
public import Theory.SpecificGroups.Triality.Model.QTKEParameters

/-!
# Actual coordinate contract for the two twisted D4 cells

The ordered products below use precisely the supplied root subgroups and their
one-parameter maps. The orbit-compatible order is the standard twelve-root
order, transported by `Geometry.rootIndex`; the opposite chart negates these
roots. A coordinate witness identifies the Frobenius-fixed scalar tuples with
each literal finite cell and proves the ambient point equations. This is a
geometric obligation, with no representation or evaluation conclusion.

Once the witness is constructed, the scalar count gives both cell cardinalities,
including q = 2. Source: Steinberg, `Chapter2St2.tex`, 6.2(b), 11.8, 12.2,
and 13.3(a); GLS3, Definition 2.8.1 and Theorem 2.8.2.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open Triality.Standard

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The supplied positive roots in the standard triality orbit order. -/
def positiveCoordinateRoot (S : Geometry K) (i : Fin 12) : S.roots.Root :=
  S.rootIndex.symm (PositiveCoordinates.rootIndex i)

/-- The negatives of the same ordered roots. -/
def negativeCoordinateRoot (S : Geometry K) (i : Fin 12) : S.roots.Root :=
  S.roots.neg (positiveCoordinateRoot S i)

/-- Ordered product of actual one-parameter root elements. -/
def orderedRootPoint (S : Geometry K) (r : Fin 12 → S.roots.Root)
    (x : Fin 12 → k) : Variety.Point K :=
  (List.ofFn fun i => (S.roots.rootSubgroup (r i)).includePoint
    ((S.rootParameter (r i)).value (x i))).prod

/-- Coordinate equivalences anchored by actual ambient root-product equations.
Their construction from `Geometry` is a separate proof obligation. -/
structure TwistedCellCoordinates (S : Geometry K) (n : ℕ) (P : Parameters) where
  coefficientEmbedding : ExtensionField P →+* k
  negative : PositiveCoordinates.FixedCoordinates P ≃
    finiteCell S n (S.roots.neg ⁻¹' S.roots.positive)
  positive : PositiveCoordinates.FixedCoordinates P ≃ finiteCell S n S.roots.positive
  negative_point : ∀ a,
    cellInclusion S n (S.roots.neg ⁻¹' S.roots.positive) (negative a) =
      orderedRootPoint S (negativeCoordinateRoot S) (fun i => coefficientEmbedding (a.val i))
  positive_point : ∀ a,
    cellInclusion S n S.roots.positive (positive a) =
      orderedRootPoint S (positiveCoordinateRoot S) (fun i => coefficientEmbedding (a.val i))

/-- The scalar orbit count transfers to both literal elementary cells. -/
theorem cellCardinalities_of_coordinates (S : Geometry K) (n : ℕ)
    {P : Parameters} (C : TwistedCellCoordinates S n P) (hq : P.q = 2 ^ n) :
    CellCardinalities S n := by
  constructor
  · rw [← Nat.card_congr C.negative, PositiveCoordinates.card_fixedCoordinates, hq]
  · rw [← Nat.card_congr C.positive, PositiveCoordinates.card_fixedCoordinates, hq]

/-- Binary specialization retains every positive exponent, including one. -/
theorem binary_cellCardinalities_of_coordinates (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (C : TwistedCellCoordinates S n (binaryParameters n hn)) : CellCardinalities S n :=
  cellCardinalities_of_coordinates S n C rfl

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
