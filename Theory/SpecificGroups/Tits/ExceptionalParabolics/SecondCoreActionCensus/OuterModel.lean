module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-!
# A finite candidate for the outer action of the second Tits core

The reconstruction of the second parabolic uses a marked quotient of the
actual automorphism group. This file fixes the common finite target and the
transposition to be marked. It asserts no identification of that quotient;
constructing a surjection with precisely the inner kernel is a separate proof.

The target suggested by the collection relations is C₂² × S₄. The relevant
finite question concerns order-six subgroups containing one specified element
whose S₄ coordinate is a transposition, retaining its C₂² coordinate.
Source context: Parrott (1972), §5, p.683; Aschbacher--Smith F.1.12 and14.2.21.
-/

@[expose] public section
namespace Tits.ExceptionalParabolics.SecondCoreAction

abbrev BinaryPair := Multiplicative (ZMod 2 × ZMod 2)

abbrev OuterModel := BinaryPair × Equiv.Perm (Fin 4)

/-- The central coordinate is retained, rather than suppressed by an unmarked
abstract group identification. -/
def markedTransposition (v : BinaryPair) : OuterModel := (v, Equiv.swap 0 1)

end Tits.ExceptionalParabolics.SecondCoreAction
