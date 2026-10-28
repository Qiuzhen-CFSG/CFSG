module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Holomorph
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ReflectionOrbit

/-!
# Local structure of Aut(A₆)

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.567–570.

The proved results identify the actual inner A₆ and natural S₆, give the
Sylow order 32, identify its normal inner intersection with D₈, and
transport through the actual conjugation action with centralizer kernel.
The marked equivalence transports the holomorph calculations to every actual
Sylow subgroup: the elementary quotient, Frattini subgroup, centers and
centralizers, normal cyclic-four geometry, two four-groups, rank-one subgroup
classification, and normal-subgroup automorphism-prime bound.

The involution interface gives the actual S₄ and D₁₀ fixed groups, inner
involution centralizers, and four-group normalizers with their compatible
outer complements. In particular, `four_transitive` and `outside_coboundary`
are unconditional scalar facts on A₆ for the source fusion argument.
`four_normalizer_reflection_orbit` supplies the actual Sylow conjugator
making the outer reflection fix the specified four-group normalizer.
Chapter-specific records and the global centralizer premise of 2.5.22(2)
belong to the source assembly.

`normal_subgroup_dichotomy_obstruction` rules out interpreting the
p.567 intermediate dichotomy as a claim about all normal subgroups.
-/
