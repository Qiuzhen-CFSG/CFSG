module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.Contracts
public import Mathlib.Algebra.Field.ZMod

/-!
# Binary construction interfaces for the larger M₂₄ modules

The eight candidate degrees are 120, 252, 220 twice, 320 twice, 1242 and
1792. A binary model here is an actual representation of the Witt-design
group, together with absolute irreducibility. For each repeated degree, the
two models must additionally be inequivalent over the binary field.

These structures specify finite construction obligations; they do not assert
that any candidate exists. `LargeModels` assembles supplied witnesses, using
scalar extension and descent of intertwining equivalences. Thus construction
owners do not need to repeat the argument over every closed field.

Sources: James, *The modular characters of the Mathieu groups*, J. Algebra
27 (1973), 57–111; the candidate matrix models at
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M24/.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
open Sporadic.Mathieu

/-- An actual absolutely irreducible binary representation of native M₂₄. -/
structure BinaryModel (d : ℕ) where
  representation : Representation (ZMod 2) M24 (Fin d → ZMod 2)
  absolute : representation.IsAbsolutelyIrreducible

/-- Two inequivalent actual binary models of the same degree. -/
structure BinaryPair (d : ℕ) where
  first : BinaryModel d
  second : BinaryModel d
  inequivalent : IsEmpty (first.representation.Equiv second.representation)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
