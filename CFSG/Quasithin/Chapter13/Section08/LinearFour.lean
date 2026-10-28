module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.Constructions
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.FinalCentralizers
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceApplication
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExclusion
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorSeed
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorMarking
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorAction
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedCoordinates
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorKernel
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorActors
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourcePointQuotient
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceNormalizerFactors
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceNormalizerProduct
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedNormalizer
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceNaturalConsequences
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSeedPlane
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExteriorAlignment
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExteriorPresentation
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceExteriorTensor
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondAction
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondDuality
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondStabilizer
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondCover
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondKernel
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondRows
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceSecondProduct
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceCriticalGeometry
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefAccounting
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceLocalImage
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceMaximalChief
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalSpan
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalKernel
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalTensorSpan
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalResidualSpan
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalPairKernel
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalSecondComparison
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceOriginalPlaneComparison
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorSecondProduct
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ComplementObstruction

/-!
# The L₄(2) branch of §13.8

The source constructions and final centralizer and commutator-image
calculations are proved in the imported modules. `ChiefSections` constructs
the faithful irreducible action of the actual H/O₂(H) on every noncentral
chief quotient between V_H and H_C, identifies its natural four-space
model by the full G.6.4, and bounds the chief count by one.

`source_linear_four_exclusion` constructs a chief series,
proves that its factors remain K-irreducible, identifies the K-noncentral
count, and obtains the final contradiction from the explicit 13.8.31
obstruction. The whole H_C/V_H is not assumed elementary abelian.

`SourceChiefGeometry` constructs the maximal quotient for 13.8.30 from the
earlier seed action, proves faithfulness and the literal restricted coordinates,
and reduces the nine-factor bound to the tensor spans. Its marked-strata
accounting and intersection calculations retain the remaining geometric inputs.

`SourceTensorSeed` constructs the first tensor from compatible cyclic seed
embeddings and commuting factor actions. Its literal quotient application
retains the source conjugator, proves the product and intersection of the
two U_H copies, and computes the order-sixteen section U₀/V.
`SourcePointQuotient` constructs the natural U_H/V₂ action from the given
four-dimensional marking, identifies the actual K₂/O₂(K₂) with PSL₃(2),
and proves U_H = ⟨V₃^{K₂}⟩. Its tensor-intersection application removes
the separate seed-generation premise while retaining both original maps.
`SourceTensorKernel` uses the original shear and seed irreducibility to prove
the maximal quotient has kernels V₃ on U_H and V on U₀. `TensorImages` gives
the resulting field dimensions one and two and supplies the literal field
line in the nine-factor application. `OrthogonalSpan` then uses the exterior
marking and the two literal parabolic shears to compute the next conjugate
span, identify its kernel as V, and prove the corrected quotient has field
dimension two. This discharges that dimension premise in its combined
first-tensor and orthogonal-span consumer.

`SourceTensorActors` identifies the actual point-normalizer and K₂ images,
proves K₂ perfect, and derives its trivial action on the soluble second
factor. It lifts the required parabolic actors and applies them to the exact
intersection and critical-pair obstruction with the same natural quotient marking.

`SourceNormalizerFactors` proves K₂ is normal and a C-component of the full
G₂ using the original normal I₂, its symmetric quotient and transitivity.
It constructs the actual two-core quotient's S₃ factor, preserves the I₂
quotient map, and applies the resulting factor placement to the literal
tensor intersection with the retained conjugator. Identification of the
complementary centralizer factor with K₂/O₂(K₂) is supplied by
`SourceNormalizerProduct`. That module constructs the full marked
PSL₃(2) × S₃ quotient and the generating equality G₂ = ⟨K₂,L₂,₊,T⟩
from the original I₂ and Sylow data. Its intersection application preserves
both intrinsic factor maps and the same source conjugator.

`SourceSeedNormalizer` proves the literal equality N_H(V₃) = L₁T from
the natural marking, the earlier source theta bound and the original Sylow
subgroup. It discharges the separate seed-normalizer-control premise in
the critical geometry and terminal exclusion applications.

`SourceNaturalMarking` constructs that natural marking from F.9.2's
faithful action, the original order |U_H|=32 and H/O₂(H)≃L₄(2). It
retains the canonical quotient and sends the actual V₂/V₁ to the first
coordinate line. `SourceNaturalConsequences` removes the separate natural
marking from the two G₂-factor identifications, generation, seed normalizer
and seed-centralizer index. `SourceNaturalFlag` additionally marks the original
seed plane in that same basis. `SourceSeedPlane` lifts its plane cubic to an
actual order-three element of L₁ using the original theta bound. Its exterior
span application removes the separate block and cubic-lift premises, proves
the index 64, and obtains field dimension three and kernel V in the maximal
quotient. `SourceTensorMarking` aligns the product quotient with the same natural
point-quotient coordinates and constructs both compatible tensor seed
embeddings from literal sections. It derives cyclicity from K₂-generation
and applies the resulting tensor to the specified conjugate intersection.
`SourceTensorAction` constructs the whole U₀/V₂ action through that same
product quotient. Normal factors put U₀ in the elementary V_H, and the
natural point-quotient kernel yields [O₂(G₂),U₀] ≤ V₂. Its tensor and
same-conjugator intersection applications remove the whole-action premise
and derive V ≤ U₀ from the smaller seed section. `SourceSeedDuality`
identifies the actual V₂ as Lagrangian and equates its pointwise action
kernel with that on V/V₂. `SourceSeedCoordinates` constructs the covered-case
natural seed section, retaining the supplied I₂ map and choosing coordinates
for the original g. Its tensor and intersection applications remove the
seed-marking and generating-actor premises. `SourceExteriorAlignment`
forces the actual U₀/U_H three-space and the image of V in any compatible
exterior action, using the first-tensor index and original seed normalizer.
Its intersection and index-64 span applications remove the separate image
and parabolic-actor premises. Construction of that compatible exterior
action and the second-tensor marking remains necessary.

`SourceExteriorPresentation` constructs the compatible exterior marking from
one local line relation, using the original quotient map. The singular model's
point and ordered-line transitivity and linear presentation are proved directly.
The original seed normalizer supplies point-stabilizer invariance, and
H-generation makes the intertwiner surjective. The constructed marking feeds
the actual index-64 span calculation. Transporting the local line relation
from the first tensor is completed in `SourceExteriorTensor`: the literal
quotient and same-g tensor row construct its nonzero seed and local line.
The resulting compatible exterior marking feeds both the actual index-64
span and same-conjugator intersection, with no exterior action assumed.

`SourceSecondAction` constructs the literal elementary quotient V₀/U₀ and
its action through the supplied G₂/Q₂ map from the natural/exterior markings
and the original I₂ core identity. It proves the V_H-image has dimension three,
is K₂-minimal, generates the whole quotient and has a disjoint same-g translate.
Its original-seed application first constructs the exterior marking from the
saved first tensor. `SourceSecondDuality` uses the Pfaffian pairing and the
same-g first-tensor row to construct an injective intertwiner from the dual
of the supplied natural K₂ module into that second quotient. Its image is
exactly V_H/U₀, and its original-input application retains both quotient
factor maps and canonical coordinates. The two full second-tensor rows are constructed below.
`SourceSecondStabilizer` constructs the
pointwise fixation of that seed by the original natural-line stabilizer,
using the first tensor and exterior displacement. `SourceSecondCover` then
constructs a surjective intertwiner from the dual-natural module tensored
with the three-point permutation module onto the literal second quotient.
Its marked slice is the actual seed and its dimension is at most nine.
`SourceSecondKernel` proves that the kernel is zero or the whole constant
tensor subspace, using the original disjoint translate and K₂-minimality.
`SourceSecondRows` constructs both full quotient equivalences and preserves
the literal V/V₂ natural section, both factor maps, marked slice and original g.

`SourceTensorSecondProduct` lifts both second-tensor rows to the ordered
product V₀ = V_H V_H^g V_H^(g²), preserving the source conjugator and the
literal kernel. `SourceSecondProduct` applies it to the constructed original
rows for a cubic image of the same g and proves |V₀:U₀| is 64 or 512.
The source definition of L₂,₊ as a two-residual discharges that cube condition
for the original g ∈ L₂,₊, preserving the supplied quotient map.
Its separate choice application constructs a cubic representative in I₂
with the same first V_H translate and generated overgroup; it does not
assert placement of that representative in a smaller L₂,₊. The extra-line
norm consumer remains conditional: its
pure second-factor scalar-cubic placement cannot be instantiated together
with the source first tensor on the same quotient map.

`SourceCommonCubic` proves the actual placement from centralization of V:
the common cubic has second quotient coordinate one. It also lifts the
complementary-plane natural cubic into the original scalar subgroup and
G₂. `ComplementAccounting` and `ComplementObstruction` retain this basis,
compute its action on the literal radical, and apply the surrounding
1, 2, 1, 2 chief counts to the conditional terminal exclusion. The
extra-line movement step needs a route compatible with this placement.

`SourceCriticalGeometry` connects the constructed first tensor and exterior
action to the actual critical pair. The point obstruction applies in both
orientations of the original critical conjugator, deriving both excluded
lines. The earlier 13.8.27(3) implication and chief movement exclude case (1)
and give all three critical conclusions. Its terminal consumer takes the
literal three-chief-factor lower bound and derives the unique-four-factor
obstruction, without assuming that H_C/V_H is elementary abelian.

`SourceChiefAccounting` derives the three-factor bound from the complete
nine-factor lower bound on the literal L₀ and its complementary-plane matrix
image. It constructs the radical action, odd terminal quotient and normal
intersection strata. Its original-seed terminal application also constructs
the exterior and dual markings and derives Q_H's normalization of L₀ from
the original Sylow data. No separate three-factor premise remains there.

`SourceLocalImage` identifies that original L₀ matrix image from the natural
A₆ setup, the covered quotient and the proved seed-normalizer bound. It
retains the same marked plane and quotient map. Its terminal application
removes the separate matrix-image hypothesis from the nine-factor consumer.

`SourceMaximalChief` constructs the central image of the original L₀ on the
canonical covered quotient. For an intrinsic L-normal generated two-group span,
it constructs a maximal quotient and derives its binary degree bound on every
complete chief series of that same L₀, recovering all field and scalar data.
Its nine-factor application retains the exclusion of order 64 for those literal
maximal quotients as an explicit premise; it does not supply tensor movement
or assert that an arbitrary normalized ambient span lies in L.

`SourceOriginalSpan` now proves the required containment of the literal U_L
in L from the original natural and F.9 data. The complementary cubic supplies
U_H = V₃ [U_H,L₀], and U_H normalizes L. Natural transitivity and orders give
V < U_L. The selected maximal quotient therefore has the original ambient
numerator and kernel, faithful covered action and degree/chief-count bound;
no independent span-placement or seed-commutator premise remains there.

`SourceOriginalKernel` derives U_H intersect W = V₃ for the selected kernel
from that same natural action and complementary cubic. Its application adds
the order-four seed image to the selected quotient, retaining the original
numerator, kernel, covered map and chief-count bound. No separately marked
irreducible U_H/V₃ section is needed for this intersection.

`SourceOriginalResidualSpan` uses the original two-residual definition to
place the supplied g in L. On the same selected maximal quotient it proves
that every g-power translate of S has kernel intersection V and image order
64, retaining the original linear actor. It also proves S intersect S^g = U₀
and strict movement of S before projection. Distinctness of the projected
images, needed to exclude the degree-six quotient, remains unproved.

`SourceOriginalPairKernel` computes |S S^g:V| = 256 on that same quotient.
An order-64 maximal quotient forces a kernel of order four modulo V on this
join, escaping both spans. The second-section image of that kernel is
disjoint from each span image. This exposes the extra kernel the movement
argument must exclude; it does not exclude order 64.

`SourceOriginalSecondComparison` retains both full second tensor rows on the
canonical second section and compares the original-g orbit of S with the
same maximal quotient modulo image(U₀). The comparison has the exact kernel,
intertwines every original g-power and is injective on each translated slice.
An order-64 maximal quotient would yield a common quotient of order four.
Its exclusion still requires the original ambient action constraints; slice
injectivity alone does not exclude the extra-line row's trivial projection.

`SourceOriginalPlaneComparison` extends the comparison to the canonical
intersection U_L intersect V₀. It intertwines every original actor in
L intersect G₂, whose normalization of the domain and kernel is derived.
Both tensor rows and every original-g slice remain marked. In the order-64
branch the invariant second-image kernel has index four in this whole
intersection image. This additional equivariance does not itself exclude
the extra-line projection; the remaining argument must use the original
ambient geometry beyond these separate tensor-factor actions.

The remaining extra-line movement, complete nine-factor bound and earlier
local inputs remain assembly obligations. This conditional exclusion does not discharge Theorem 13.8.28.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed pp.963–966.
-/
