module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.FourSpace
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.Reduction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations

/-!
# Faithfulness of the four-space action on the full binary Levi

The five explicit chain words give a faithful four-dimensional representation
of S₆. Their ambient evaluations satisfy the Coxeter relations and recover
the four original root generators, by the certified comparison on all 52
coordinates. Hence the ambient S₆ map covers the entire split Levi and
intertwines with the faithful four-dimensional map. Any Levi element fixing
the four-space therefore lifts to the identity of S₆ and is itself the identity.

The theorem `fourSpace_faithful` discharges both word-identity premises of
`fourSpace_faithful_of_chain_relations`. No local projection, Levi–radical
factorization, or fixed-subgroup equivalence is assumed.

Source context: Aschbacher–Smith F.1.12(I)(5), printed pp.263–264
(PDF pp.274–275) of `refs/quasithin.pdf`.
-/

namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification

/-- An element of the full split binary Levi fixing the four half-root lines
pointwise is the identity. -/
public theorem fourSpace_faithful (x : splitLevi)
    (hx : (ambientLeviHom x).val * fourEmbedding = fourEmbedding) : x = 1 :=
  fourSpace_faithful_of_chain_relations KernelProof.ambientChain_liftable
    KernelProof.ambientChain_recovery x hx

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification
