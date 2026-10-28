module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import CFSG.Quasithin.ChapterA.Section01.RankActions.AutomorphismQuotient
public import CFSG.Quasithin.ChapterA.Section01.RankActions.DisjointPlane
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ThreeAutomorphisms
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PrimeSL2CoverRigidity
public import CFSG.Quasithin.ChapterA.Section01.RankActions.IrreducibleActions
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ExtraspecialExtensions

/-!
# Rank-two automorphism and action restrictions

This module assembles A.1.25–27, A.1.29 and A.1.32–33 of Aschbacher–Smith,
*The Classification of Quasithin Groups*, printed pp.25–29. Supercritical
rank detection and the small p-group models yield the cyclic, elementary,
and extraspecial alternatives with actual isomorphisms. Orbit counting
excludes a disjoint p-subgroup normalized by an elementary plane, and
small Frattini quotients give the {2,3}-automorphism restriction at p = 3.
The Frattini action and a normal Hall complement in its linear image give
the embedding of the automorphism p-core quotient in GL₂(p).

The linear normalizer calculations and generalized Fitting detection prove
the residual-action restrictions. Dickson recognition and prime-field
SL₂ cover rigidity identify the perfect-action quotient and its odd core.
The irreducible normalizer action controls normal small-rank odd subgroups;
fixed planes and central-cover splitting give all three extraspecial
extension rank obstructions. Every independent input is discharged.

The model list in A.1.25(1) explicitly assumes a nontrivial p-group; rank
equality and the automorphism quotient include the trivial group. A.1.32(2)
retains the trivial normal subgroup as an additional alternative.
-/
