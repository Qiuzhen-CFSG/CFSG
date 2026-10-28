module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ExtraspecialReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.CentralizerReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.RadicalCentralizerReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuCase
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuRadicalApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.FormReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MixedFourNormalizers
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.TwoConjugateReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryCentralizers
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuForm
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NativeFBranch
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NativeFNormalizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PointParabolicBranch

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.Residual
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.ExactImages
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.HexadLift
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.OctadNormalizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.EightLift
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.SextetLift
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.SextetCentralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.SextetShears
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.ZeroFormReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.ZeroFormMaximal
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularCApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Positioning
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.SourceRows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Applications
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.NativeEightApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ABB.Positioning
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ABB.Application
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxPair
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxResidualSmall
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxPurePair
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairTransport
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairExclusion
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.Positioning
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.ContainerObstruction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.PureImageBound
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.KernelGeometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonModel
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonPlacement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.TwoImagePlacement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.ExceptionalApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CompletePlacement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.Larger

/-!
# Elementary normalizers in the native J₄ model

This umbrella exposes the checked pieces of the Kleidman--Wilson elementary
normalizer argument.  The central-involution enlargement and extraspecial orbit
reduction give the pure-subgroup reduction under a centralizer-core placement
premise and its literal radical restriction. The Mathieu leaf records the
native kernel normalizer and radical endpoint. The certified elementary action
bound proves uniqueness of the order-2048 elementary kernel in max1 and the
Mathieu normalizer argument for a subgroup of that kernel containing an
involution outside the first class. The native kernel-orbit and seed-centralizer
proofs discharge the centralizer-containment premise. The intrinsic symmetry
theorem now supplies the actual form unconditionally.
`FourGroupGeometry` gives native marked representatives for pure-2A four-groups
and nonsingular four-groups with a first-class member, including literal
centralizer transport. `PureTwoA.NativePairTransport` identifies pure census
row seven with the literal kernel pair 818/1449 by a checked matrix-rank
invariant, transporting the full centralizer and normalizer together.
`PureTwoA.NativePairCentralizer` identifies the full ambient centralizer of
that marked pair with its literal max1 centralizer: its order is 196608,
and its actual Mathieu image has order 96. The quotient equivalence retains
the original binary kernel and agrees with the original projection on
representatives. `NativePairApplication` transports elementary extensions,
whole centralizers, and trivial-image normalizers using one ambient
conjugator, with literal maximal-two-local and arbitrary-radical consumers.
`MathieuPureNormal` excludes nontrivial pure elementary normal subgroups of
max1 using the two certified binary-kernel orbits. `NativePairExclusion`
therefore rules out trivial-image pure extensions at maximal-TWO-local level.
For an actually normalized four-subgroup of a larger pure maximal normalizer,
it eliminates row seven and retains only row two. It does not assert the
existence of a normalized four-subgroup in an arbitrary larger pure group.
These native results make no identification with a printed MOG AAA type.
`PureTwoA.NativeExtensions.Images` exhausts the actual 96-element image and
places every elementary subgroup in four literal elementary groups of order
sixteen. Its maximal pure-extension application retains the original Mathieu
projection and excludes the trivial image. `NativeExtensions.Positioning`
reduces these four image positions to two by an actual ambient conjugator
centralizing the marked pair, transporting the whole centralizer and normalizer.
`NativeExtensions.PureLifts` restricts actual first-class lifts to two max1
census representatives and gives the seven possible kernel masks for the
ninth representative. `NinthKernelRanks` bounds their pair-displacement
ranks by sixteen; `FirstLiftPositioning` compares this with the native pair's
rank twenty to exclude that lift. Every nonidentity element of the actual
Mathieu image is therefore fixed-point-free. `PureImageBound` proves that
the image has order two or four at maximal TWO-local level, and applies this
to proper extensions in the two image positions with purity, maximality and
both whole ambient local-group transports retained. `DisplacementKernel`
proves kernel transitivity on the actual first-class lift fibers and forces
every kernel element into each lift's displacement. `DisplacementActions`
uses linear certificates to reduce the two positions to explicit four-groups.
`KernelGeometry` proves that the exceptional order-four case has exactly the
native pair as kernel, selects two actual lifts determining the full
centralizer, and gives its kernel section's fixed-vector equations. The common
case's kernel has order at most thirty-two. The proper-extension consumer
retains both whole ambient transports. `CommonSpace` identifies the exact
common fixed kernel and its pointwise image stabilizer. `CommonCompletion`
proves that every full common-image extension has a pure self-centralizing
completion of order 128. Its intrinsic double centralizer is pure and has
the same whole normalizer at maximal TWO-local level. `CommonCenter` puts
eight explicit kernel elements, including involution 1257, in that full
double centralizer. `CommonModel` exhausts the actual lift and kernel choices
by identifying every such completion with one fixed native 128-subgroup.
`CommonKernelRanks` and `CommonLiftRanks` certify its intrinsic rank
geometry; `CommonRankGeometry` applies the certificates to every actual
lift and kernel. `CommonPlacement` proves that the WHOLE original normalizer
fixes involution 1257 in the common order-four case, hence lies in a literal
native max2 conjugate. It supplies the maximal-TWO-local equality, the
original proper-extension reduction with this branch removed, and the
actual radical restriction and normalizer-core identities. `CommonLiftProduct`
checks compatibility of the fixed common lifts. `CommonModelStructure` proves
that the fixed common group is pure, elementary and self-centralizing of order
128, and bounds the actual double centralizer for every nontrivial common
image. `CommonNontrivialPlacement` consequently extends whole-normalizer max2
placement and the literal radical identities to all nontrivial common images.
`TwoImagePlacement` transports every order-two image from either position into
that case by an actual pair-centralizing conjugator. The proper-extension
reduction now retains only the exceptional order-four image, with purity,
maximality and both whole-group transports intact. `ExceptionalTransitivity`
proves kernel conjugacy of every actual pure exceptional lift configuration
and forces its order to be sixteen. `ExceptionalKernel` identifies the exact
order-sixteen kernel of its entire ambient centralizer.
`ExceptionalCentralizer` corrects arbitrary image lifts twice in the binary
kernel to prove that the full centralizer image is the literal order-sixteen
container, hence the centralizer has order 256. `ExceptionalApplication`
removes every extension of order different from sixteen from the remaining
branch, retaining whole-normalizer max2 equality for arbitrary native-pair
markings and the original radical restriction and both core identities.
`ExceptionalEnlargement` now shows that kernel mask 64 normalizes that entire
centralizer but moves the original pure extension. Since the centralizer has
order 256, this gives a strict two-local enlargement, excluding the exceptional
position under maximal two-locality. `CompletePlacement` consequently closes
EVERY native-pair extension, without an order restriction, with its whole
normalizer in an actual max2 conjugate and literal radical/core restrictions.
The independent larger pure branch containing no conjugate native pair remains
required for the full cover; no native-eight fusion is needed for this
maximal-two-local specialization.
`NativeExtensions.ContainerObstruction` identifies the native pair's double
centralizer with the pair and proves that its whole normalizer has trivial
ambient centralizer. Thus this literal pair cannot have a unique conjugate
extraspecial first-core container, as the printed AAA(2) argument requires
of its source marking. This obstructs that seed-only identification; it does
not exclude a unique container for a larger elementary extension.
`PureTwoA.EightApplication` consumes the proved native-eight automizer placement
in the exceptional centralizer branch, including literal maximal-TWO-local and
arbitrary-radical applications. It retains the exact centralizer fusion as a
geometric hypothesis and has no additional normalizer-placement premise.
`PureTwoA.Larger` packages the maximality upgrade from a characteristic pure
four-subgroup to each of the four literal endpoints; the characteristic
subgroup and endpoint containment remain explicit source geometry.
`FormReduction` proves the zero/pure, zero/mixed and
nonsingular source trichotomy at maximal-two-local level. `PairCentralizerSplit`
identifies the literal direct factors of nonsingular pair centralizers and of
their intermediate subgroups. `MixedFourNormalizers` proves the native max1/max2
normalizer placement for the two mixed nonsingular four-group configurations,
with maximal-two-local and literal radical consumers. `TwoConjugateReduction`
proves the one-or-two-F normalizer argument from the native occurrence inputs,
including its conjugate and radical consumers. `ElementaryCentralizers` reduces
the elementary-centralizer cases to a nontrivial zero-form witness or the same
self-centralizing nonsingular centralizer. `MathieuForm` proves that the native
kernel has zero intrinsic form, so a nontrivial nonsingular subgroup in max1
has nontrivial image under the literal Mathieu quotient. The remaining four-group containers, orthogonal lift calculations and
order-256 configurations still require their source geometry before the full
four-local cover can be assembled.
`NativeFBranch` packages the checked literal linear-five subgroup, its full
normalizer and intrinsic quotient. `NativeFNormalizer` instantiates the native
global occurrence and centralizer results and uses the actual F-normalizer
to position any second-class member in E. It proves whole-normalizer coverage
for every subgroup of a conjugate of F containing such a member, including
maximal-two-local and literal radical consumers with no positioning premise. `PointParabolicBranch` packages
the certified elementary subgroup in a native point parabolic, its full ambient
normalizer as a genuine two-local, and the corresponding literal radical
restriction.
`M22Images` gives exhaustive elementary-subgroup placement in six literal
native M22 containers, identifies the two order-16 source kernels, and lifts
the alternatives and conjugators through the actual second-centralizer residual.
Its quotient kernel is the original ambient E, and its trivial-image radical
consumer retains the full normalizer and core maps. `M22Images.Fusion` reduces
the four saved E8 rows to one E8 and the two E16 kernels using literal native
conjugators. `EightProper` proves that every proper subgroup of this E8 extends
into an E16, and `ExactImages` retains equality with the full E8 in the final
residual-image case. `HexadLift` identifies the first E16 inverse image with an actual conjugate
of the native octad pullback Q, retaining the original M22 and Mathieu quotient
comparison. `OctadNormalizer` combines this comparison with the producer's
exact Q orthogonality and native F-normalizer theorems. It closes the first
M22 lift with whole-normalizer coverage, maximal-two-local equality and
literal radical restriction, without a premise positioning the second-class
member in E. `EightKernel` and `EightLift` prove that the exceptional full
E8 image has only the original seed line in its orthogonal kernel, so its
zero-form lift has order sixteen. The calculation applies through every
residual conjugator. `SextetKernel` certifies the orthogonal order-eight kernel
container by linear reconstruction on eleven basis vectors. `SextetImages`
splits the literal E16 into five pointwise-octad cases or thirty non-octad
four-groups. `SextetLift` transports this split through the original residual
quotient, closes the octad normalizers and bounds every remaining mixed
zero-form witness by order 128. Larger witnesses now give actual
maximal-two-local equality and literal radical restriction.
`SextetCentralizer` constructs the actual 2A involution defined by the common
fixed tetrad of each non-octad sextet four-group. The whole centralizer fixes
it, and it belongs to the canonical central omega. The residual lifts,
maximal-two-local enlargement and literal arbitrary-radical restriction retain
the original maps. Extraspecial-core containment for the remaining sextet
cases, the pure-2A normalizer analysis, the exceptional order-sixteen group's centralizer and strict
normalizer enlargement, and the remaining pure and nonsingular configurations
still require their source geometry.
`SextetShears` certifies four actual kernel shears and uses them to construct
a pure-2A subgroup invariant under the whole normalizer when the sextet's
tetrad involution belongs to X. The full order-eight kernel intersection
supplies this involution, in particular for every order-128 sextet lift.
The exhaustive M22 image split now reduces every order-128 zero-form group
with the original 2B seed to native E/F coverage or a smaller pure-2A
normalizer. The residual conjugators, maximal-two-local equality and literal
radical normalizer/core restriction are retained. `SextetEnlargement` puts the tetrad involution in the intrinsic radical of
Ω₁(Z(C(X))). Adjoining that radical preserves zero form, the full centralizer
and normalization by N(X). `ZeroFormReduction` constructs a maximal zero-form
extension and thereby eliminates every smaller-kernel sextet case. The
exhaustive mixed zero-form reduction now leaves E/F coverage, a pure-2A
normalizer, or the exceptional order-sixteen lift, retaining its original
residual maps and seed line. Groups of order greater than sixteen therefore
admit E/F or pure-2A whole-normalizer reduction, with maximal-TWO-local equality
and literal radical normalizer/core restriction. `EightEnlargement` now proves strict enlargement for every exceptional lift:
the displayed kernel shear normalizes the full centralizer and its central
omega but moves X. The original residual maps discharge both alignment and
ambient centralizer placement. `ZeroFormMaximal` therefore eliminates the
exceptional case and removes the witness-order bound from the maximal mixed
zero-form reduction. Every maximal two-local, and every arbitrary radical
via a chosen maximal overgroup, now reduces to native E/F coverage or an
explicit pure-2A or nonsingular witness. The literal full local normalizer
and two-core maps are retained, and the remaining witness lies in the same
radical. Pure-2A classification, the exact exceptional order-256 centralizer
and its nondegenerate form, the remaining nonsingular source branches and the
full four-local assembly remain unfinished.

`NonsingularC` now supplies the weak nontrivial zero-form enlargement for
both literal Figure 2(c)/(c′) images, including the original Figure 1 pair.
The native tetrad lies in the form radical of Ω₁(Z(C(X))); the original
2B seed discharges full ambient centralizer placement. `NonsingularCApplication`
reduces this selected nonsingular branch to E/F coverage or a pure-2A normalizer
at maximal-TWO-local level and retains the literal arbitrary-radical restriction.
The exact elementary centralizer assertion for these rows, general row selection,
pure-2A classification and the other nonsingular source configurations remain.

`NonsingularImages` identifies the literal marked quotient container of order
2688 and certifies a Sylow subgroup of order 128 in it. For an elementary group
with the original seed and Figure 1 pair permutation, the Sylow conjugator lifts
through the native seed centralizer, preserves both markings, and transports
the full centralizer and normalizer. `SylowRows` proves exhaustive whole-subgroup coverage in six native elementary
containers. `FigureA` supplies the literal printed (a) generators, and `FourRows`
fuses all six containers into (a), (b), (c), or (d), including the Figure 1 pair.
`SourceRows` lifts this exhaustive selection through the actual seed-centralizer
quotient, preserving the seed, marked permutation, full centralizer and whole
normalizer under the same ambient conjugation. `Subgroups` and `ExactRows`
refine containment to equality with (b), (c), (d), (c′), or (d′) outside the
box image, and `ExactSource` lifts this equality through the literal quotient.
`PairPositioning` and `NonsingularPositioning` place an arbitrary nontrivial
nonsingular group in these rows or retain an explicit fixed-point-free outer
pair. `Applications` consumes the existing (c)/(c′) enlargement and selected
eight-centralizer results with the proved equality of `starHom` and
`starProjection`. It gives whole-normalizer, maximal-TWO-local and literal
radical restrictions. The fixed-point-free ABB(3) enlargement, box and pure-2A
geometry, invariant isotropic subgroup of the eight-normalizer, and final
four-local coverage with its arbitrary-radical consumer remain unfinished.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988),
Proposition 2.2.3, pp.490--491.
-/
