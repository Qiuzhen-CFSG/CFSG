module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Action
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Cycles
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.System
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Recognition
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.System
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.GeneratedSystem
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.RowComparison
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.NativeVertex
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.AlignPlane
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PlaneSplitting
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.AlignEdge
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.AlignPlaneGroup
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.AlignPlaneEdge
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Overlap
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Similarity
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.GenerationReduction
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PairCentralizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.SecondFour
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.SecondCentralizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.FourLifts
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LocalPlacement

/-!
# Native octad geometry for the Mathieu uniqueness argument

The extension exposes actual octads, trios, sextets, their incidence and
stabilizers, the equivariant octad/coset identification, and coplanarity of
triangles and quadrangles. The native uniqueness system satisfies all three
generation identities. Its local graph is precisely the graph of incident
octads in the marked sextet. Rank descent proves four-generation and hence
its cycle-base condition without extra premises. Recognition now requires
only an equivalence with this native system (or a similarity and edge-fixer
rigidity). The source extensions identify the point and line residues,
construct the literal coset collinearity graph and its transitive action,
prove the line-stabilizer product and ambient flag transitivity, and establish
both vertex and plane-local generation identities. Each source plane has
fifteen literal point cosets; its actual action has image S₆ and kernel
of order 192, identified through the original rectangle and cubic quotient
maps. Distinct collinear source points determine a unique actual line.
The ambient edge fixer has the literal GL₃(2) tensor quotient; its plane
intersection is a hyperplane parabolic of index seven, and its pointwise
automorphism fixer is trivial. The source system and native recognition
consumer now discharge this rigidity premise. The normalizer-generated
subgroup inherits the same oriented fusion sets and has a complete faithful
source system without a simplicity premise. The full edge fixer is the
derived subgroup of the point–line flag stabilizer, so marked source-row
comparisons preserve both flag intersections and the actual edge subgroup.
A source-row/native-octad isomorphism matches the literal kernel coordinates
and quotient actions and supplies a vertex map for the oriented induction
system. The native common four now identifies the literal point–plane
intersection with its two-space parabolic, and a conjugated row map carries
the source point–plane subgroup onto it, retaining both kernel coordinates
and quotient action. The actual plane normalizer splits over A₂; its
semidirect coordinates retain the original quotient map. The native common
eight now identifies the actual point–line group with its hyperplane
parabolic, and the common four lies in that eight. One row isomorphism
therefore preserves both flags simultaneously, together with its kernel
coordinates and quotient action. The same map preserves the whole edge
fixer, supplying the complete vertex-side comparison on the oriented
normalizer-span system. Explicit source rectangle coordinates identify its
exceptional locus with the native weight-six hexacode locus, giving the full
quotient comparison and an actual plane-group isomorphism preserving both
the original kernel and quotient coordinates. It carries the literal
plane-point action kernel to the native tetrad kernel. The source common
four becomes a native double-zero plane; conjugation within the sextet
stabilizer aligns it with the marked common four and hence aligns the full
point–plane flag. The same oriented induction system now has actual maps
on both local groups preserving their point flags. The plane map is now
corrected within the actual point–plane group to align the second endpoint
and preserve the entire local setwise edge. The source plane–edge fixer
has order 1536, identifying the disjoint-pair orbit in the native sextet.
The row kernel recovers the common eight from this local fixer, proving
the normalizer implication needed to correct the vertex map. Source 41.3's
full innerness assertion is now proved: a marked row isomorphism identifies
the literal overlap with the linear point–plane parabolic, where Sylow
conjugacy and its order-two center reduce to the proved marked innerness.
The corrected maps consequently agree pointwise on their entire overlap
and supply an actual similarity and an unconditional recognition of the
oriented normalizer span as M₂₄. The native two-class involution coverage
then proves the same two marked classes in both the span and G and gives
full involution fusion control in the span. The first class has a unique
fixed coset, and the 7.3/7.5 argument reduces ambient generation and final
recognition to containment of the second involution's full centralizer.
The marked pair centralizer now lies in the original Sylow, giving the
weak-closure transporter step. The actual residual-fixed B(t) is identified
with its coordinate four-group; every nonzero A₂/B(t) coset has a point
lift and a unique fixed coset. The two fixed-coset steps now reduce the
remaining ambient generation to local placement of C_L(t) in G₃ and
point-class lifts for involutions of (L∩C_G(B))/B. The latter calculation
is now proved from the former: a source Sylow of I has order 512, its
intersection with C_I(B) is Sylow there, and every square-in-B element
of the original Sylow centralizing B lies in A₁ or A₂. Their actual
point-class lifts discharge the quotient premise. The fifteen fixed octads of the native second involution now recover its
invariant sextet and bound its centralizer by 7680. Comparing with the
literal source local centralizer of that order proves C_L(t)≤G₃. The
original full normalizers therefore generate G, and the same oriented
producer data yields an actual ambient M₂₄ isomorphism from Mathieu fusion
without further local placement, lift or graph-comparison premises.
-/
