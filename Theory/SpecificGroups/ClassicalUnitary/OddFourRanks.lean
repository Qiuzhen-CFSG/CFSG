module

public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Torus
public import Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining

/-!
# Dimension-four unitary rank witnesses in odd characteristic

The torus construction supplies a nonidentity involution in the actual PSU₄
of an arbitrary Hermitian form over a field of order r². For every odd prime
s dividing r+1 its centralizer contains an elementary abelian subgroup of
order s³ and generator rank three. The scalar kernel is retained throughout.

An independent construction embeds the additive prime field cubed using
trace-zero symmetric shears, giving ordinary defining rank greater than two.
Both constructions transport through actual projective basis equivalences.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39 (PDF p.50). The arithmetic source consumer is
`CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalRanks.UnitaryFour`.
-/
