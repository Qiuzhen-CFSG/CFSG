module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortVectors
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortLifts
public import Theory.SpecificGroups.Monster.Construction.LocalC.TensorSpace
public import Theory.SpecificGroups.Monster.Construction.LocalC.OrthogonalSpace
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison
public import Theory.SpecificGroups.Monster.Construction.LocalC.RealLeech
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies
public import Theory.SpecificGroups.Monster.Construction.LocalC.Carrier
public import Theory.SpecificGroups.Monster.Construction.LocalC.N1Equivariance
public import Theory.SpecificGroups.Monster.Construction.LocalC.Pullback
public import Theory.SpecificGroups.Monster.Construction.LocalC.N1Embedding
public import Theory.SpecificGroups.Monster.Construction.LocalC.Descent
public import Theory.SpecificGroups.Monster.Construction.LocalC.TensorKernel
public import Theory.SpecificGroups.Monster.Construction.LocalC.Action
public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceConstruction

/-!
# The Leech local construction and its orthogonal action

The actual ATLAS Leech lattice supplies 98,280 short binary classes and
sign-independent symmetric tensors with the normalization required by
(28.2) and (28.6). The fixed natural-spin tensor space has dimension 98,304
and positive tensor-product form.

The fixed source Golay–Leech comparison identifies the actual central
quotient of `Q1/⟨k1⟩` with the binary Leech space. It is equivariant for
the whole concrete `N1` and its actual natural action. Instantiating the
signed short module with this map gives the fixed positive definite space
`B` of dimension 196,884. The explicit short families are also re-exported.

The orthogonal spin normalizer and full Leech isometry group have a fixed
pullback over their actual binary actions. Its tensor image `C` contains
`N1/K` faithfully and acts faithfully and orthogonally on `B`. The tensor
kernel consists exactly of the paired scalar signs. The short action is
actual conjugation on the embedded extraspecial subgroup, and the specified
central involution has the source signs on all three summands.

The spin normalizer is identified with the actual relative normalizer
inside SL, and every real Leech isometry has determinant one. The resulting
isomorphism of pullbacks preserves both linear factors. Thus
`sourceTensor_range_eq_C` identifies `C` with the determinant-one source
construction; `mem_C_iff_source` states its exact membership conditions.
The existing conditional space interfaces are preserved for their consumers.

Source: Aschbacher, *Sporadic Groups*, Sections 22–23 and 27–28; compare
the ATLAS Monster entry, pp. 228–230. The ATLAS product-one triples are
not identified with the Aschbacher triples with zero.
-/
