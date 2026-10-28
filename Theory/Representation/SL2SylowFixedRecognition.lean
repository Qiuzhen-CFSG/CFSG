module

public import Theory.Representation.SL2SylowFixedRecognition.Complementary

/-!
# Binary SL₂ recognition from Sylow fixed spaces

G.1.6 is `quotientCoordinates_of_fixedSpaceHypotheses`: the original module
surjects equivariantly onto natural copies with exactly the global fixed
space as kernel. G.1.7 is `natural_of_complementary_sylow_fixed`: two
complementary Sylow fixed spaces yield an equivariant linear equivalence.
Both theorems work over every finite binary field of degree at least two.
They retain the original matrix actors and permit zero multiplicity.

Source: Aschbacher--Smith, printed pp.329--330. The proof reconstructs the
field action from root relations instead of using irreducible constituents.
-/
