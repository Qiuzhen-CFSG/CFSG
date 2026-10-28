module

public import Theory.SpecificGroups.Monster.Construction.LocalC.RealLeech.Symmetric

/-!
# The fixed real Leech action and its two scalar kernels

The full isometry group of the actual integral Leech lattice acts faithfully
on `LocalC.NaturalSpace`. Its unique real extension agrees exactly with
`leechVector`, including the fixed marking and division by `sqrt 8`, and
preserves `naturalForm`. Lattice negation acts as minus identity.

The induced action on `SymmetricPart` preserves its trace form and product.
Its kernel and the kernel of the actual binary lattice action are both
precisely identity and lattice negation. The proof uses short-class
uniqueness and the concrete glue and coordinate-pair vectors; it requires
no Conway simplicity or group-order theorem. The two kernels are also
identified as subgroups for downstream descent.

Source: Aschbacher, *Sporadic Groups*, Sections 22–23 and 27, especially
Lemma 23.3 and printed pp. 147–149. These are the Leech-action ingredients
for the spin-normalizer pullback and the tensor-image construction.
-/
