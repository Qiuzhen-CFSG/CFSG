module

public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.SixCover
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CubicNormalizer
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PointComparison
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PointFlags
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerActions
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerKernel
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerCore
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OuterSquare
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerLift
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerInvolution
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PlaneCentral
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PlaneFlags
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PlaneGroup
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CoreComparison
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CoreGroup
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.EvenGroup
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CentralTwist
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.ToddTwist
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OuterTwists
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCharacteristic
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCentralKernel
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapModuleReduction
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapAutomorphisms
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.LocalAgreement
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.EdgeTwist
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.Recognition

/-!
# Source J₄ comparison: compatible covers, core modules and outer twists

The exports construct the genuine six-cover comparison, retaining both
central attachments. Full normalizer conjugation is compatible with the
original quotient, with its exact six-element kernel. The six-cover and
quadratic core-module comparisons use the same native triple-cover marking.
The quadratic comparison now lifts to an isomorphism of the actual cores,
intertwining the whole original six-cover and retaining the central involution.
These maps glue on their common center to compare the original O²(H),
with both core and cover restriction equations. The core comparison now
intertwines every matching full-normalizer actor. Faithful descent compares
the entire plane groups modulo their marked centers, retaining both
restrictions and the literal normalizer image. The two outer M₂₂ involution
classes are linked by an inner commuting square root. After quotienting
only the scalar cubic, this proves that every matching splitting actor
has square one. Gluing across that actual involution now constructs the
full H isomorphism, with its core and six-cover restrictions, marked
central involution, scalar cubic, and full cubic normalizer retained.

The actual plane and point outer twists are constructed, with O²(H)=QC_H(A)
and the literal twelve-dimensional full-cocode extension. Their original
point-plane overlaps are preserved. The earlier point comparison retains
one M₂₄ quotient conjugator for the trio and sextet, the marker, and both
literal point overlaps together with their triple intersection.

A single correction in the cubic normalizer now aligns both plane flags,
retaining the scalar cubic, center and explicit six-cover restriction. The
same map transports the actual pointwise and setwise edge stabilizers inside H.
The actual Todd correction now represents the nontrivial outer class of
I/(Q A), using its literal tetrad-parity affine quotient. Both Q and Q A
are characteristic in I, so this quotient factorization applies to every
original overlap automorphism. The kernel on the original Q/Z(Q) now
consists of inner corrections through Q and the plane central twist; the
pointwise Q-fixing kernel consists exactly of identity and that twist.
Every overlap automorphism is now inner followed by the actual Todd and
plane twists. The full section commutant is trivial: the certified even
hexad preimage permits only cubic scalars, and an actual outer actor
eliminates the two nonidentity scalars. This calculation uses the original
full core-module marking. Applying the factorization to the discrepancy
between the two local isomorphisms now makes them agree on every element
of the literal common intersection, retaining both central attachments,
the six-cover restriction and the point quotient conjugator. The full
edge fixer now has its literal source description K N_(S∩M)(Y), with Y
constructed in the original S∩M. The actual Todd twist preserves each of
the seven cores generating K; averaging over Y then gives an outer correction
preserving the whole edge fixer. The local maps now agree on the overlap while preserving that
edge. Odd-index averaging identifies the residual on K as conjugation by
Z(H); its discrepancy vanishes at the index-five point stabilizer and hence
everywhere. This proves the full original edge-reversal equation. The direct
source-base extension constructs the recognition equivalence, retaining both
local restrictions and all markings. Source simplicity and actual target
generation suffice; earlier local data and cubic-normalizer construction
remain explicit source and native inputs.
-/
