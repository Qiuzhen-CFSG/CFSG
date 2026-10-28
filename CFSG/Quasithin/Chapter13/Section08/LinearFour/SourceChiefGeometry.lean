module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.Accounting
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.CubicAccounting
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.CubicObstruction
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.MatrixAccounting
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.LocalMatrixAccounting
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.Indices
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.LineContainment
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.LineAlignment
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.PointObstruction
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.TensorIntersection
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.MaximalQuotient
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.TensorImages
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.OrthogonalSpan
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.SecondTensor
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ResidualSpan
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ExtraLine
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.OrthogonalActors
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.HyperplaneExclusion
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ReciprocalAxes
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.StrictImages
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.SeedRadical
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.NaturalDuality

/-!
# Chief and intersection reductions for the covered-A₆ branch

`HyperplaneConstruction` derives the upper critical image's order four
from its actual plane-radical placement and fixed natural hyperplane. The
inverse source conjugator then identifies E_H and constructs E_H U_H with
index two in V_H. `HyperplaneExclusion` obtains the required axis
centralization from the seed centralizer bound and excluded critical line,
then applies the resulting critical geometry to the terminal exclusion.
`ReciprocalAxes` constructs the natural axis and both critical indices from
the marked actions, mutual endpoint placement and the excluded critical
lines. It uses the inverse of the actual CriticalPair conjugator and derives
the terminal centralizer and normalizer premises from the source definitions.
`StrictImages` proves the strict inclusion from the natural kernel and
orthogonal displacement, using the same critical conjugator. It also derives
the commutator on V_H ∩ Qγ from that kernel and applies both results to the
terminal exclusion. The initial markings, excluded lines, plane-radical
placement and the chief obstruction still require source assembly.
`SeedRadical` supplies a separate route through the actual seed-normalizer
two-core. The natural action constructs its parabolic image and geometric
radical containment. The original F.9 critical path supplies the edge cores
and both endpoint containments. The seed-normalizer bound N_H(V₃) ≤ LT
then replaces the separate matrix-radical marking in all three critical
conclusions and the terminal exclusion. That earlier bound, the initial
action markings, excluded lines and chief obstruction remain explicit.
`NaturalDuality` constructs the literal Q_H/H_C dual section in the given
natural coordinates from the nonzero seed commutator. It supplies the
centralizer index four and the complementary cubic's dual length, and
removes the separate index premise from the terminal exclusion.

The checked hexacode coset filtration supplies the needed faithful degrees.
The maximal quotient is constructed from the earlier seed action and actual
covered quotient; its faithfulness and literal intersection coordinates are proved.
The corrected quotient dimension calculation and a literal scalar section
then give nine noncentral chief factors of L₀. Actual homogeneous strata
with multiplicities 1, 2, 1, 2 account for the six factors surrounding
H_C/V_H, leaving at least three there and forcing component movement.
Restriction of a unique factor of order sixteen contributes at most two
noncentral factors, establishing the required obstruction from that lower bound.
The intersection-index argument supplies the two numerical inputs used
by the faithful-section G.6.4 application. A nonzero image in the literal
quotient V_H/U_H recovers containment of the critical line A₁.

The first tensor and its seed irreducible determine the maximal kernel on
U_H and U₀. The scalar action then gives the literal field line and plane,
and the line feeds the nine-factor calculation. `OrthogonalSpan` computes
the actual L₁-conjugate span from its exterior marking, proves its kernel
is V, and derives the corrected quotient dimension two over the field of
four elements. Its final consumer combines this with the first tensor.
`SecondTensor` proves movement in the maximal quotient for the natural
two-dimensional second-tensor row and feeds it to the nine-factor consumer.
The proof uses only the known kernel on the orthogonal span; it adds no
kernel containment elsewhere. `ResidualSpan` gives a separate route using
an odd-order plane actor lifted into the actual parabolic two-residual.
Generation and irreducibility recover the maximal kernel and field dimension,
then the natural second tensor supplies movement. This route needs no
Levi-involution placement in L₁ or separate point marking for V.
`OrthogonalActors` proves the displacement bound and its equality case on
the actual orthogonal six-space. It derives the two critical intersection
indices and recovers A₁ ≤ V_H from the source hyperplane and its commutator
modulo U_H. The exterior marking carries all three conclusions into the
terminal chief-factor contradiction.

`CubicAccounting` provides an alternative to the four supplied homogeneous
filtrations. The same cubic on the natural, exterior, dual and upper radical
sections gives the six surrounding chief factors, with literal intersection
transport and relative normality. Its final application leaves three factors
in H_C/V_H from the nine-factor lower bound. `CubicObstruction` transports
that count to the actual restriction of an H-chief series, supplies both
13.8.31(3) obstruction clauses, and applies them in the terminal exclusion.

`MatrixAccounting` lifts one exact cubic through the original two-group
kernel and constructs the radical action from its literal matrix image.
`LocalMatrixAccounting` identifies the actual two-core and its order-three
quotient from the local matrix image, constructs the normal strata and
chief-count quotient, and derives the critical indices from the exterior
action. Its terminal application no longer needs separate cubic actors,
a radical module marking, or a terminal quotient assumption.

`LineAlignment` lifts the natural quotient's transitivity through the central
line and constructs the conjugator in the contrary case A₁ ≤ U_H. The same
conjugator aligns the actual CriticalPair's Uγ and Vγ with the specified
source conjugates. Its LocalSetup application proves Uγ ≤ V_H and
[U_H,Uγ] = 1 from the tensor-span containment and earlier source inputs.
`PointObstruction` identifies the actual point-normalizer image and its
nontrivial normal two-subgroup with the full line radical. The natural,
tensor and orthogonal markings compute the index eight and identify the
literal kernel Q_H intersect V_H^g as U0. The section centralizer's simple
image and two-perfectness then force [H_C,K] <= V_H. Its critical-pair
application contradicts the existing three-chief-factor bound, retaining
the same source conjugator and the earlier case-one endpoint premises.

`TensorIntersection` derives the exact intersection from the first tensor,
commuting quotient factors, exterior point-parabolic action and earlier
maximal two-local uniqueness. It feeds the result and the computed index
eight into the critical-pair obstruction with the same original conjugator.
The quotient irreducibility used in that calculation is proved directly in
the exterior model, rather than supplied as another section assumption.

`ExtraLine` has a conditional norm argument for the second tensor with a
trivial line. Its pure second-factor scalar placement is incompatible with
the actual common quotient, as proved in `SourceCommonCubic`. A compatible
movement argument remains necessary for that source row.

These are conditional reductions. The initial tensor markings, the orthogonal
and dual markings, the local matrix image, the second-tensor markings and
common cubic, and the remaining critical-pair and hyperplane geometry
still require construction from 13.8.27(b) and 13.8.29. These modules do not
yet prove all of source 13.8.30–32.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed pp.964–965.
-/
