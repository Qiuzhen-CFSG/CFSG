module

public import Theory.Representation.G2.RestrictedModules.Steinberg.Construction
public import Theory.Representation.G2.RestrictedModules.Steinberg.FieldTransport
public import Theory.Representation.G2.RestrictedModules.Steinberg.Irreducible
public import Theory.Representation.G2.RestrictedModules.Steinberg.RootAction

/-!
# The concrete level-two G₂ Steinberg factor

The carrier is the orbit span of an explicit tensor in the cube of the actual
natural representation of `Atlas.G2.Model`. Its 64 binary-unipotent translates
of the lowest vector form a basis. The action is absolutely irreducible over
every characteristic-two field, in particular over each finite field of order
`2^n` with `n ≥ 2`.

The highest vector is nonzero and its line is exactly the common fixed space
of the six actual positive root groups. Its torus character is `l²*m`, with
short-then-long coroot pairings `(1,1)`, the weight `λ₁+λ₂` in GLS3. The root
formulas are explicit on the carrier's tensor coordinates and on the sparse
64-element spanning family. Coefficient Frobenius is identified with the
genuine field-automorphism twist through representation equivalences that
persist after arbitrary scalar extension.

Independence follows from the nonzero binary-unipotent norm of the lowest
vector. Explicit root, Weyl and torus calculations prove whole-group stability.
The unique unipotent fixed line and cyclicity prove irreducibility and the
scalar-commutant criterion proves absolute irreducibility. This constructs the
algebraic Steinberg factor of level two, of dimension 64; the finite group's
dimension-`|F|^6` Steinberg module is not used.

Sources: GLS3, 2.8.6, 2.8.7 and 2.8.10(g); Aschbacher--Smith, the proof of G.9.3,
printed pp.354,356--357. No tensor-exhaustivity or classification theorem is used.
-/
