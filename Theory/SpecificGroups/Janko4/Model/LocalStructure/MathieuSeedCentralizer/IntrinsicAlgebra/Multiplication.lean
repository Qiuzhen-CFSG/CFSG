module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Grading
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Quartic

/-!
# The graded cyclic algebra and quartic of the literal seed operators

The ten operators commute and square to zero. Their generated algebra has the
exact saved 56-element basis, evaluation at `cyclicVector` is an isomorphism,
and its full matrix commutant is itself. The nonzero saved top operator is the
product of operators 0, 1, 2, and 3.

The published squarefree homogeneous spaces form a multiplicative grading:
they are independent, span the algebra, have dimensions 1, 10, 34, 10, 1 in
degrees 0 through 4, and vanish in higher degrees. The top operator spans
degree 4. All 210 saved quartic coefficients are certified in their exact
lexicographic order. Arbitrary fourfold products are unchanged by permutation
and vanish on repeated indices; their top-line coordinates have the prescribed
normalization.

The proofs use kernel-checked finite identities, the cyclic-vector commutant
argument, and the independent monomial basis. These are statements about the
literal matrices alone; identifying them with the intrinsic radical space and
proving tensor preservation are separate parts of the parent development.

See `Multiplication/source/README.md` for the coordinate conventions and the
kernel certificate reproduction.
-/
