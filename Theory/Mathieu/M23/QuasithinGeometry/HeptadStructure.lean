module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Local
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Order
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryAction
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.ConcreteLocal

/-!
# The split heptad and four-set stabilizers in M23

The actual heptad stabilizer is identified with F2^4 ⋊ A7. Its kernel acts
regularly by binary translations on the sixteen complementary points, and
its alternating complement acts through the faithful exceptional binary
representation. The source three-cycle has no nonzero fixed vector.
The labelled, conjugation, affine, and quotient maps are compatible with the
original inclusion in the concrete design automorphism group.

The local intersection Ix/U is S3 × C2. The two-pair intersection and the
pointwise four-set kernel are U B for the lifted cyclic group of order three.
The individually fixed partition and the generation of I by Ix and the
setwise stabilizer of {x,y} are retained from the local calculation.

Source: Aschbacher--Smith, §5.2, printed pp.655--657, especially 5.2.20 and
5.2.22; Aschbacher, *Sporadic Groups*, Chapter 6, Lemma 19.1 and its M23
specialization.
-/
