module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.SLThree
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.SpFour
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.Orbit

/-!
# Compatible rank-two natural, Borel and diagram markings

`slThree_compatible_markings` and `spFour_compatible_markings` start with
an established natural constituent and an independently marked source Borel
and diagram action. They construct one inner correction of the constituent
marking, act on its linear coordinates by the same element, and transfer the
diagram witness to this exact marking while retaining its inducing element
of T. The standard point and plane parabolics are retained throughout.

The target field order follows from the actual comparison of group carriers
and the orders of their Sylow two-subgroups. Thus source and module field
carriers may differ. Entrywise finite-field transport identifies their flags;
the remaining comparison permutes the parabolic classes by checked geometry.
No agreement between the original markings is assumed.

`diagramOrbitIdentification` feeds these data to `Single.orbitPairIdentification`.
Its group map is the constituent's map, and its twist is the automorphism of
the transported witness. The source F.9.18 branch, constituent recognition,
source diagram action, and orbit sum clause remain the caller's obligations.

Source: Aschbacher–Smith, E.2.2(2)(b), printed pp.215–216; F.9.18(4)(iii),
pp.325–326; and the rank-two branch of 15.3.65, printed p.1152.
-/
