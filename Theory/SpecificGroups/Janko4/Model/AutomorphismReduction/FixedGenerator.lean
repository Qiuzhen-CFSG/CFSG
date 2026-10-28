module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.Reduction

/-!
# The fixed-generator branch of the J₄ automorphism calculation

`FixedGenerator.Reduction` gives the conditional matrix route: construct an
ambient implementer and prove that its square lies in the concrete matrix
subgroup. The latter membership realizes a conjugator in `Janko4.Model`.
Both model-specific inputs remain to be proved before exporting the
unconditional `fixedGeneratorSquareOrbit` theorem.

This branch is independent of the first-generator conjugacy calculation.
Source: GLS3, Table 5.3i; Aschbacher–Smith, printed pp.33 and 510.
-/
