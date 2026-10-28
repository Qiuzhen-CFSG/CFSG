module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Alignment
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Preparation
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Parabolic
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Seven
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.RadicalEscape
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.ThreeRadical
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.ThreeExclusion
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointCatalogue
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointRemainingRefinement
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointCoverExclusion
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Source
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.LargeEscape
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.JankoEscape
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Four
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Six
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Projection
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.RadicalSeparation
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Radical
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Remaining
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoSpan
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoMax4
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoNativeParabolic
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoActorSeed
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoMax1Actor
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoMax4Actor
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoLocalAlignment
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoLargeSeed
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoCrossLocal
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoReverseLocal
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Linear
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.Mathieu
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointAlternative
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointModels
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointNonenlargement
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointEvenRankTwo
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointSporadic
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.PointSporadicComplete
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Source
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Source
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Completion

/-!
# The source local branch for the exterior-square exclusion

The original exterior marking extends to LT and can be aligned with the
Sylow flag, using only the earlier structural invariance of the chosen V.
The resulting ambient subgroups have their literal inclusions and Sylow
normalization, and the basic point geometry is available here.

The original local residuals have the actual SL₃(2) and SL₄(2) two-core
quotients. They belong to the local family, so source 1.2.4 constructs
their unique normal containing components inside Gᵢ. The literal L₃ and L₄
actions are full, giving Gᵢ = LᵢC_G(Vᵢ) for i = 3,4 and equality with
any containing component having quasisimple two-core quotient. The A₈
section proves that quotient is quasisimple at i = 4,6. Hence K₄ = L₄,
and the literal irreducible six-space action excludes the three proper
overgroups at i = 6, giving K₆ = L₆. Both residuals are normal C-components
in their respective local groups. The full six-space normalizer also
factors as G₆ = L₆C_G(V₆), using the original Sylow action.
The original residuals satisfy L₁ ∨ Lᵢ = L for i = 3,6. Thus the two ambient
normalizer containments reduce to the centralizers' action on L₁, and both
hold in the equal-point-component branch.

The first-node parabolic has its original Sylow supplement, SL₂(2) quotient,
and index three. Its literal residual Y lies in L₃ ∩ L₆, is normal in M₁,
and commutes with L₁ modulo O₂(L₁). The original M₁ has its marked
SL₂(2) × SL₃(2) quotient, and the two parabolic intersections factor through
P and Pᵢ with intersection T.

For the point-core argument, V = [V,L₁] ≤ O₂(L₁). The equal and Ξ₇
component rows give V ≤ O₂(G₁). The G.2.2 argument on the actual
G₁/V₁ makes the original V₇-closure reduced in the quotient and puts
V₇ and its ambient G₁-closure in O₂(G₁). The original chief intervals
then give the source intersections and commutator bound under failure
of full V-containment. Its image in G₁/O₂(G₁) is elementary of order
eight and irreducible under the original point-parabolic image. The
normal component quotient is identified with its actual image, and the
action on U₁/V₁ descends through O₂(G₁).
The M₁* core quotient retains both original diagonal blocks. Its actual
intersection with K₁* has Sylow index 63. In the linear component row,
this recognizes a middle parabolic in an actual five-space basis, whose
irreducible order-sixty-four radical excludes the normal eight-group.
Thus the linear row of V ≤ O₂(G₁) is proved from the source containments,
without assuming a parabolic comparison.
The native M₂₄ normal-eight catalogue also excludes the literal index-63
Sylow intersection. Its octad and trio normalizer bounds prove the Mathieu
point-core row. In the J₄ row, the actual component action on U₁/V₁ is
faithful, and a seed involution's at-most-seven-dimensional displacement
contradicts the native lower bound of twelve. This completes all rows of
V ≤ O₂(G₁) conditional on LocalComponents. The original weak-closure,
point-control, generation-one and terminal consumers now have that
point-core premise discharged.

The nonquasisimple source refinement at i = 1,3 now constructs the literal
E₄₉-by-SL₂(7) quotient and Kᵢ = Ξ₇(Kᵢ)Lᵢ, including the embedded product.
At the point this gives V ≤ O₂(G₁) without assuming LocalComponents or a
quotient model. A strict radical point component supplies a solvable H-star
inside Ξ₇(K₁)T with generation parameter one. The genuine generation-one
exclusion therefore settles this row of 12.5.11(2), conditional on the earlier
structural input and normalizer containments. At the three-space full natural
action leaves equality or the radical row. The quasisimple point sieve, remaining branches of G₃,G₆ ≤ N_G(L), and the
strict-enlargement escape for the large quasisimple rows of 12.5.11(2) remain open.

For the three-space radical, the full natural action puts the actual Ξ₇(K₃)
inside G₁. Its nontrivial two-core and uniqueness over LT show that L₁
cannot normalize it. Its genuine Ξ-family membership then supplies a
quasisimple containing component orbit in G₁. The original comparison
O²(C_{K₃}(V₁)) contains both this radical and Y, lies in G₁ ∩ G₃, and is
normalized by T. The solvable radical Sylow join also gives an actual
generation-one H-star inside both normalizers. Thus the generation-one
exclusion settles the three-space component conditionally; its existing
source proof still requires the pending normalizer containments.

The subsequent seven-rank argument excludes the three-space radical using
only the refined point component. Its detected orbit either centralizes
the original point residual modulo O₂(G₁), contradicting SQTK by rank
addition, or equals the normal point component. The latter is quasisimple
of seven-rank at least two, contrary to each allowed point quotient.
Thus a refined point component now constructs all of LocalComponents,
including relative normality at three. The point-core, point-control and
generation-one consumers use this construction, and the equal-point branch
supplies both ambient normalizer containments without assuming the other
local components. The point refinement itself remains to be proved.

For each allowed large point quotient, the rank-two and outer-automorphism
arguments now prove that the actual point component has index prime to three
in G₁. The identity Y = O³′(P) then gives the original containment Y ≤ K₁.
Consequently the large quotient model alone constructs LocalComponents and
supplies the point-core, point-control and generation-one applications. The
nonquasisimple point branch also constructs all four local components. The
remaining point obligation is the quasisimple model sieve, which must exclude
the other containing models; the two general normalizer containments and
quasisimple strict-enlargement escape still require their source arguments.

The alternating and binary higher-linear point rows are now settled. The
literal point-parabolic intersection has Sylow index 63; an A₇ or A₈ quotient
would therefore have a subgroup of index five, impossible by its coset action.
The original L₁ section also excludes A₅ and A₆ by seven-divisibility. Thus the
binary-linear row is L₅(2) and supplies the full large alternative and the
point-core consumer. Other quasisimple model rows remain to be excluded.

The rank-one point sieve now proves equality for all Bender models,
binary L₃(2), even SU₃ covers, and odd PSL₂ over prime or quadratic prime
fields. The quadratic case first forces L₂(49), then the actual L₁T
quotient order 168 excludes its order-sixteen Sylow intersection. These
branches construct all local components and discharge both normalizer
containments, point-core containment, and the local premises of point
control and generation one. Other point-model rows, the remaining
normalizer branches and quasisimple escape remain open.

The full characteristic-two rank-two catalogue and both signs of the even
classical three-cover rows now also force K₁ = L₁. Proper local components
in linear-three, symplectic-four and G₂ carriers have SL₂ core quotients,
whose orders exclude the original order-168 quotient. Genuine triality and
Ree parabolic placement preserves its binary-three section and gives the
order-four obstruction in binary rank one. The small derived and Tits
endpoints are included. These branches construct all local components and
discharge the normalizer, point-core, point-control and generation-one local
premises. The odd ternary, remaining sporadic and central-cover point rows,
general normalizers, and quasisimple escape remain open.

The next sporadic sieve excludes M₁₁, M₁₂, J₂, HS and Ru. The first two
contradict the original seven-section; the latter three contradict the literal
index-63 point parabolic after cubic rank and outer automorphisms supply Y ≤ K₁.
Rudvalis simplicity is inherited from the original component, with the radical
row excluded by its order. The covered sporadic rows now construct all local
components and the point-core conclusion, and feed point control and generation
one with the structural and normalizer premises still explicit. M₂₂, M₂₃ and He,
the separate J₁ row, odd ternary and central covers remain in the point sieve.
The general normalizers and quasisimple strict-enlargement escape also remain.

The sporadic point sieve is now complete, including the separate J1 row.
The literal point-parabolic intersection has nontrivial two-core in M22,
M23 and Held, since otherwise its full Sylow would embed in the original
order-1008 two-block quotient. Native two-local bounds exclude M22 and Held;
the M23 heptad/triple catalogue excludes the index-63 intersection. J1's
elementary Sylow subgroups exclude its SL3(2) section. Only M24 and J4 remain
among sporadic point models, and their existing residual containment supplies
LocalComponents and point-core containment. The point-control and generation-one
consumers retain the earlier structural and general normalizer premises.
Odd ternary and central-cover point models, general normalizer containments
and the quasisimple strict-enlargement escape remain open.

The complete source point-core containment now follows without assuming
LocalComponents. The odd ternary and small alternating-cover rows use the
rank-two bound and perfect movement of the original seed. The central M22
cover maps to a native two-local obstruction while preserving the original
Sylow restriction and seven-section. Together with the checked simple and
radical rows, the full A.3.6 catalogue proves V ≤ O₂(G₁). Its original
point-control, weak-closure, generation-one and terminal consumers now retain
only their structural and normalizer inputs (and the terminal configuration).
The point-component refinements, general normalizer containments and
quasisimple strict-enlargement escape remain open.

The central M₂₂ and A₆ cover point rows are now excluded. The literal
L₁T-intersection preserves a full Sylow and its seven-section through the
M₂₂ central quotient; a nontrivial two-core then contradicts the native
two-local bound. The full original catalogue now constructs LocalComponents
or an actual normal point component in a signed odd ternary or central A₇
model. Excluding those two families, the general normalizer containments
and quasisimple strict enlargement remain open.

The odd ternary point rows now force prime seven and identify the image
of the original L₁ in K₁/O₂(K₁) with SL₂(7). The argument retains the full
relative Sylow and the original order-168 quotient of L₁T. In the central
A₇ row, cubic containment proves Y ≤ K₁; the literal parabolic intersection
has order 504 and index 15. The full catalogue therefore constructs
LocalComponents or one of these two explicitly marked remaining cases.
Their final Sylow-action exclusions, general normalizer containments and
quasisimple strict enlargement remain open.

The central A₇ cover is now excluded. The original residual image is
core-free of order 168, and the literal two-block marking makes every
M₁* action on it inner. The A₇-cover automorphism fixer forces M₁* to fix
the cubic center of K₁*. That center lies in the original order-504
parabolic, contradicting the centerless two-core quotient of M₁*.
Thus the full catalogue leaves only the signed ternary-seven models
before unconditional LocalComponents; the general normalizers and
quasisimple strict-enlargement escape remain open.

Both remaining ternary-seven rows are now excluded using the original
L₁T-intersection. Its two-core quotient has order dividing 168, while its
full relative Sylow conflicts with the actual GL₂(7) or GU₂(7) scalar
centralizer bound. The special and projective coverings and the supplied
Hermitian forms are retained. Thus source 12.5.3 now constructs all four
LocalComponents from the original hypotheses, including Y ≤ K₁ and the
Ξ₇ alternative. Combining this with the checked Sylow alignment gives the
construction on the original V from an exterior marking and Structural1222.
The normalizer reduction no longer assumes LocalComponents. Under the
genuine generation-one exclusion, strict point enlargement is reduced to
L₅(2), M₂₄ or J₄. General normalizer control and strict enlargement remain the source
obligations of this local owner.

The strict L₅(2) and M₂₄ enlargements now supply actual escaping cubic
overgroups of the original Sylow. In the linear row, the literal middle
parabolic forces the Sylow action to be inner; the native Mathieu generating
triple supplies the other row. Their lifts are solvable and yield H-star
subgroups of generation parameter one. The genuine exclusion therefore
proves K₁ = L₁ in both rows. The original source-parameter application now
leaves only J₄ for strict enlargement, retaining the earlier structural
input and the still-open general normalizer containments.

The J₄ row now also supplies an escaping cubic Sylow overgroup. Its actual
Sylow-invariant Mathieu seed cannot normalize L: prime 23 forces its
intersection with L into its two-core, and squares then contradict the
original dihedral point-Sylow section. Thus every strict point enlargement
gives a genuine generation-one H-star. The source generation exclusion
proves K₁ = L₁ and relative normality in G₁ in all rows. Its source-parameter
application retains the earlier structural input and the two independent
general normalizer containments, which remain the local source obligations.

The independent normalizer argument now has its literal point-component
projection. Normalization of L₁* lifts through O₂(G₁), since the original
Sylow contains that kernel and normalizes the perfect L₁. In all three
large point models, outer two-group coverage reduces G₃,G₆ ≤ N_G(L) to
the action of the projected local intersections on L₁*. These projections
retain the original Sylow intersections, normalize the original local
residual intersections, and keep the normal closure of Y* inside the
actual point parabolic. In the linear row, Y* is a non-two normal subgroup
of the middle parabolic and therefore contains its minimal self-centralizing
radical. The radical determines the stabilized subspace, so the projected
closure containment forces both actors into that parabolic. This proves
G₃,G₆ ≤ M in the L₅(2) row independently of the generation-one exclusion,
and discharges both normalizer premises in its strict-enlargement consumer.
The Mathieu row now also supplies both containments independently. The
original point parabolic is recognized as a native trio stabilizer using its
nontrivial two-core and Sylow index 63. Every non-two normal seed contains
the irreducible trio core. The native order-64 elementary catalogue and the
distinct trio/sextet normalizer orders make the trio core weakly closed in
its stabilizer, forcing the projected actors into the original parabolic.
Its strict-enlargement application retains only Structural1222At.
The radical separation step now proves Ξ₇(K₁) ∩ Gᵢ = O₂(Ξ₇(K₁))
for i = 3,6. The actual Ξ-family detection and the SQTK seven-rank bound
exclude containment of the whole radical; irreducibility under the original
Sylow gives the exact intersection. Its image in G₁/O₂(G₁) is disjoint
from the image of Gᵢ ∩ G₁, with the whole two-core kernel retained.
The radical complement-normalization step is now proved. Its literal image
is the full seven-core, with the natural SL₂(7) action from A.3.6. The original
point residual complements that plane. Its unique involution inverts the
plane and lies in the actual Sylow; radical separation forces each local
intersection to fix it and normalize its centralizer, the original complement.
Thus both normalizer containments hold in the radical row independently of
the generation-one exclusion. Its strict-enlargement application retains only
Structural1222At. Combining the completed rows shows that any normalizer
escape constructs an actual J₄ point component and a projected actor failing
to normalize the original residual image. The J₄ projection exclusion and
full local assembly remain.
The projected Y-closure is now proved solvable from the original geometry:
M₁ ∩ Mᵢ is the product of the index-three first-node parabolic and a proper
subgroup over the whole two-core of L₁. In the J₄ row this forces the
projected actor to be proper, since a full actor would make its nontrivial
solvable closure normal in the inherited simple point component. Every
remaining normalizer failure now retains these literal solvable-span and
properness constraints. The J₄ parabolic placement and exclusion remain open.

In the native max4 cover branch, the original parabolic is now the full
preimage of an S₄ point stabilizer times SL₃(2). The same supplied component
map identifies the original perfect L₁* image with the linear factor in
that quotient. The native first-centralizer branch is excluded through its
literal M22 projection: the whole kernel and full original Sylow are retained,
and the original order-1008 core quotient forces a nonzero Mathieu two-core.
The native max1 branch identifies the original parabolic as a full Mathieu
trio preimage, again preserving the supplied component equivalence.
In either max1 or max4, the original Y-closure has nonzero two-core, using
the self-centralizing native local core and its containment in the original
Sylow. Its central omega is a nonzero elementary subgroup inside the same
projected actor and normalized by it; in particular that actor has nonzero
two-core. If the original actor and parabolic lie in the same native max1,
the literal Mathieu projection forces the actor into that parabolic and
proves the original G_i ≤ M for i = 3,6. The whole elementary kernel is
retained. In max4, the full projection kernel lies in the original parabolic
and normalizes its perfect point residual. Solvable-residual uniqueness then
lifts the normal linear-factor image to normalization of that same residual
by all of max4. This gives the original ambient normalizer conclusion for
actors in the same max4. Independently conjugated cover placements in either
one of these rows now align through the same original full Sylow, using native
Sylow self-normalization. Native coverage, the max1/trio-to-max4 comparison,
the remaining Y*/Pᵢ* markings and the exclusion of actors in other native locals
remain open.

The complete native-row argument now proves both normalizers from the named
maximal-two-local cover. The marked max2 scalar-kernel comparison preserves
the original cubic image, and the original parabolic intersection supplies
the matching order bound. The accepted linear-five recognition excludes
max3 by its two-part. Together with both max1/max4 incidence directions,
these results settle every projected actor row. Local.Source applies the
normalizers to point control, generation exclusion and K1 = L1 with relative
normality. Local.Completion now discharges the native cover with the proved
CompleteCover.maximalTwoLocalCover. Both normalizers follow from the original
hypotheses, and the complete fusion consumer retains only Structural1222At.
The final construction supplies Sylow coordinates, all LocalComponents,
both normalizers, point-core containment and ExteriorFusion on the original V.
The earlier structural theorem and construction of the terminal configuration
remain with their existing producers and the final exterior assembly.

Source: Aschbacher--Smith, 12.5.2--4, 12.5.8(1), 12.5.11(2), pp.817--821.
-/
