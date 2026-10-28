module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Surjectivity
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.CocodeActions
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.BasicSubgroups
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticData
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.LocalQuotient
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticQuotient

/-!
# Structural development of the concrete Parker triality group

This interface exports the actual standard-automorphism group, its surjection
onto the marked Golay permutation group, and its cocode kernel. It also exports
the unique normal forms, the normal four-group `K`, the relative normality of
`Q1` in `N1`, and the unconditional axis and orbit-kernel calculations.

The quotient `Q1/⟨k1⟩` is a plus-type extraspecial group of order `2^25`,
canonically identified with the image of `Q1` in `N/K`. Its center is generated
by the image of `z1N` and equals its centralizer in `N1/K`. The actual central
quotient is isometric to the 24-dimensional space with the twisted addition
of Exercise 4.6; its square and commutator laws are proved on the concrete words.

The proofs combine collection and the three-axis action with Golay
polarization and cocode duality. These are the group and permutation
ingredients of Aschbacher, *Sporadic Groups*, Lemmas 14.3–14.6, Exercise 4.6,
and Section 27, pp. 144–146. The real-module and tensor-action constructions
are separate consumers.
-/
