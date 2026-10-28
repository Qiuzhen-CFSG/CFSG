module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.CentralLayers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Witness
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.Radicals
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.NonFrattini
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.XDecomposition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.KernelAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.PairedImages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondarySection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondaryClosure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondaryKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondaryPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.InnerEdge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondaryNatural

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SharpImages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FullKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedAttachment

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FullMovement

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.PairedOrbit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.NormalizerComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.ProperImages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SmallRadicalEdges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.WholeKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SmallRadicalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SmallRadicalLayers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedKernelComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.KernelDichotomy
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedCoreTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedFrattini

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.OriginalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.OverlapAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.OverlapComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SharedCenter
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.CenterAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.OriginalLayers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SquareKernels

/-!
# Preparation for nonbinary symplectic recognition at distance two

The characteristic replacement retains the literal component marking and the
original odd-index witness. Its moving subgroup has an actual natural cover
with the full ambient semilinear action. Normal attachments in the opposite
critical kernel lie in the full fixed layer and vanish under that projection.
The original marked radical is a conjugate point core, plane core, or Sylow
two-subgroup, with the same marking on its full normalizer. At the original
field degree, the reciprocal critical actions are inner. Failure of the
whole-core Frattini bound makes both images roots of order q and decomposes
the whole X-layer as U times its component-fixed part. The whole opposite
kernel acts inside the symplectic component, with the exact kernel intersection.
The secondary commutator equals its seed commutator and is fixed by the
whole endpoint stabilizer. Both secondary images are elementary of order at
most q cubed, with their literal opposite-kernel intersections. Their paired
commutator intersection remains in the common edge center, fixed by both
endpoint stabilizers. The secondary orbit contains the full endpoint Z-layer.
Its literal quotient by Z is elementary and has an action of the original
local two-core quotient with the same component marking. The opposite
secondary image acts quadratically with binary fixed codimension at most 2n,
by the paired q-factor index estimate.
The normal closure of the opposite Z-kernel intersection contains the actual
core. If the component fixed the secondary quotient, this closure would
centralize the entire elementary secondary orbit but displace the opposite
Z-layer outside it. The whole displacement is now proved equal to the displacement of the
moving layer. Its constructed equivariant natural projection retains the
entire kernel in the maximal secondary seed. A containing Sylow supplies a self-orthogonal plane whose full cover preimage
lies in the seed once the full edge acts inside the component. The source star
modulo its entire component centralizer is now elementary at positive distance,
even without whole-star commutativity. Its marked dual cover gives the second
star inclusion and the characteristic cut proves M=M*. This discharges the
inner-edge premise and proves nontrivial component action on the literal
secondary quotient at distance two. Choosing the smaller secondary image
makes the opposite image an offender on that quotient. Its action is faithful,
and FF recognition supplies a natural moved section at the original degree
with the original quotient coordinates and all fixed attachments retained.
The natural ratio bound now makes both secondary images exactly q cubed,
and both full secondary fixed codimensions exactly 2n. The quotient
centralizer is the literal opposite-kernel intersection times Z. Equality
also gives fixed-vector lifting through the full natural-section kernel
and a supplement by the whole fixed space. On the original group, the
secondary orbit is its component commutator times that kernel supplement.
The maximal elementary image is self-centralizing, so the full opposite
kernel has the same image and displacement as the secondary orbit. The
whole intrinsic core lies in that orbit and equals its component commutator.
The entire fixed X-layer lies in the common edge center; hence X = Z and
Z = U Z_t in the non-Frattini branch. The whole kernel image is a point
radical on the original marked cover: the plane alternative would lift to
quadratic action, contradicting the non-Frattini displacement. Its critical
root fixes exactly the natural displacement hyperplane. Lifting that space
through the full cover proves Z_z intersect Q_a lies in [Q_a,Z_z] Z_t.
Consequently A = core Z_a, and the literal secondary quotient is fully moved
by the component, with its fixed kernel still retained.

Point-radical hyperplane displacement now proves the paired seed commutators
and ambient Frattini subgroups disjoint. The full fixed preimage of A/Z is
central in A and lies in [A,A'] Z, so it is elementary. Natural-vector
transitivity makes A elementary, and the exact whole-kernel factorization
then contradicts the non-Frattini branch. This establishes the whole graph-core
Frattini bound at distance two and proves shortness and the actual natural
block model for the original component at the original degree. The
replacement image D is nontrivial, and its full normalizer has odd index
from the original witness. Its two-core B is radical and satisfies
D ≤ B ≤ R₀, where R₀ is the original radical image. If R₀ is parabolic,
then B = R₀. These statements now hold through the literal replacement
projection with its exact O₂ kernel and original component marking.
At distance two, the literal critical indices give |D| ≥ q. If B is not
Sylow, its normalizer contains the full point or plane local factor, so a
proper D is exactly the corresponding central root. In the nonsylow original
branch, the replacement and original images have the same full normalizer.
Before projection its two-core is exactly R restricted to the replacement
overgroup. In the proper nonsylow branch both critical layers fill the
edge quotient. Thus Q_a Z_z = Q_z Z_a = Q_t, the full kernel displacement
equals [Z_a,Z_z], and its centralizer index is q. Four marked roots then
decompose the full X-layer as U times its complete fixed factor. The whole
commutator core equals U at every original-color vertex. The literal quotient
of Q by its full component centralizer is elementary and carries the original
vertex quotient action. The four-root bound now saturates its natural
submodule, proving Q = U C_Q(L) in the field-sized branch, also transported
back to the original replacement overgroup. In the field-sized branch,
the full edge displacement is central and elementary. The third lower
commutator and fourth-power subgroup agree with those of its vertex kernel;
MS3 eliminates both. Thus the entire replacement radical, including its
fixed attachment, has class at most two and exponent at most four. The
original nonsylow radical restriction is exactly q² above a proper replacement.
The full central layer in this branch is now Z = U Z_t, and the common
critical displacement is exactly [U_a,U_z]. It contains both complete
component-fixed kernels with index q over each. Its order is q times the
fixed-kernel order; no equality or vanishing of those kernels is inferred.
Individual critical commutators meet either full fixed kernel trivially.
Below the maximal orthogonal kernel, every other displacement element is
an individual commutator. Hence the two fixed kernels agree unless both
have order q; this is applied with the original odd-index witness. A nonidentity common fixed-kernel element now forces equality even in
the maximal case. Thus unequal kernels are disjoint, each has order q, and
their product is the complete common displacement. The entire fixed part
C_Qa(L_a) also centralizes the opposite Z-layer and lies in its actual
two-core, with the original odd-index witness supplying the field-sized
premise. The unequal maximal case, the proper-root and original Sylow
comparisons, and the field restriction in MS93 (3.7) remain unresolved. The complete paired
kernels now have the same square sets, derived subgroups and Frattini images.
Their common Frattini image belongs to both full fixed parts. If the moving
fixed kernels differ, the common Frattini image is disjoint from both moving
layers. The full edge Frattini subgroup is exactly that retained image times
the critical displacement, with disjoint factors in the unequal case. The
literal replacement radical satisfies the transported formula
Phi(d.radical) = Phi(O_2(d.overgroup))[O_2(d.overgroup),d.radical], using the
original odd-index witness and an actual involutory supplement. The moving
intersection U intersect Phi(T) is exactly [U,T], with the full fixed
Frattini factor retained. The original radical normalizes this displacement;
its intersection with the replacement overgroup centralizes it pointwise,
by the marked root action and fixed-vector lifting through the full cover.
The original radical restriction now selects an actual complement of order q:
its action on C_U(T) has displacement D disjoint from the entire C_U(K),
and [U,T] = D C_U(K). The construction is transported to the original ambient
group through the same literal replacement and component marking.
The full opposite fixed kernel is now either the first kernel or exactly the
normalizer-selected overlap. In the unequal case both selected overlaps are
the opposite fixed kernels and are disjoint complementary factors. This uses
actual individual commutator values and the original odd-index witness.
The full edge center now decomposes as the moving root centralizer times
the center of the complete fixed factor. The latter centralizes the entire
replacement overgroup, so the selected overlap is exactly [Z(T), R intersect M].
In particular both paired displacements now act on the SAME whole edge center.
The original R normalizes both complementary factors, and R intersect M fixes
their product pointwise. The two original normalizer actions still need to be
compared: excluding the exchanged-complement case, radical saturation, the
original Sylow branch and the field restriction remain unresolved.
The full edge center now has exactly the edge as its centralizer inside each
endpoint group. On the literal replacement, C_M(Z(T)) = T; the original
radical restricted to M therefore acts on the entire center with kernel T
and image of order q squared. In the unequal-kernel branch the two endpoint
normalizer cores have disjoint elementary abelian action images, and together
move the whole common displacement while fixing it pointwise. These action
restrictions retain the exchanged-kernel branch; its exclusion still needs
further original-radical structure.
The full first original-radical displacement is now C_U(T), including the
entire covering kernel. Its second displacement equals the shared-center
overlap, has order q and is disjoint from the complete component-fixed kernel;
the third displacement is trivial. In the unequal-kernel branch this second
displacement is exactly the opposite fixed kernel. These identities hold
through the literal original R intersect M embedding. The exchanged-kernel
exclusion, radical saturation, Sylow branch and field restriction remain open.
The full edge square values now retain the complete fixed-factor square.
In the unequal-kernel branch, a nonidentity element of the common displacement
is a square exactly when it lies outside both full kernels. Intrinsic edge
automorphisms preserving that displacement therefore permute the two kernels.
The original odd-index witness supplies both applications. This still allows
exchange and does not assert characteristicity of the displacement.

-/
