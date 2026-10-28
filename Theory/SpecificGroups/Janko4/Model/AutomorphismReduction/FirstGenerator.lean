module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.Reduction

/-!
# Assembly interface for first-generator square conjugacy in J₄

The reduction combines the certified local involution fusion with Sylow
conjugacy and the automorphism action on at most two conjugacy classes.
It needs only odd index for the literal ATLAS local subgroup, equivalently
`¬ 2^22 ∣ Nat.card Janko4.Model`. That concrete bound remains unproved, so
this module does not yet export the unconditional `firstGeneratorSquareConjugacy`.

The stronger source assertion is Out(J₄) = 1 in GLS3, Table 5.3i;
the required consequence is used in `refs/quasithin.pdf`, printed p.510.
-/
