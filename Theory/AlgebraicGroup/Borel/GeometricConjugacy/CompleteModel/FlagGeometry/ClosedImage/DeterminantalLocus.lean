module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.Annihilator
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus.Assembly
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus.BihomogeneousZeroLocus

/-!
# Determinantal equations for full-flag exterior coordinates

The descendants prove the rank/minor equivalence, construct the polynomial
matrix of the actual stacked wedge maps in arbitrary bases, and prove the
bihomogeneity and rational-point comparison of its minors. Bihomogeneous
equations define closed subsets of the actual scheme product of two projective
spaces, constructed using normalized coordinates on standard charts. Pulling
these loci back along pairs of projections and intersecting all required
minors gives the simultaneous flag rank locus.

The point criterion holds for arbitrary exterior-coordinate bases, including
diagonal degree pairs and the empty product in dimension zero. It concerns
the explicit annihilator dimension bounds; identifying this locus with the
full-flag image uses the separate decomposability and reconstruction results.

Source: Borel, *Linear Algebraic Groups*, §11.1.
-/

public section

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The simultaneous wedge-annihilator dimension bounds cut out a closed
subset of the full-flag ambient scheme, in every choice of exterior coordinates. -/
theorem exists_flagRankConditions_locus (b : CoordinateBases (k := k) V) :
    ∃ Z : TopologicalSpace.Closeds (flagAmbient (k := k) V).toScheme,
      ∀ x : Variety.Geometric.Point (flagAmbient (k := k) V),
        x.val (IsLocalRing.closedPoint k) ∈ Z ↔
          FlagRankConditions (ambientPointEquiv b x) :=
  DeterminantalLocus.exists_flagRankConditions_locus_of_bihomogeneous
    DeterminantalLocus.bihomogeneousZeroLoci b

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry
