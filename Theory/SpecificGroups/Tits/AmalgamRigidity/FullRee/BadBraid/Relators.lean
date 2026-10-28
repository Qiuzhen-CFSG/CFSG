module
public import Theory.GroupTheory.CosetWordCertificate
public import Mathlib.Data.Fin.VecNotation
/-!
# Local words for the binary Ree reflection-pair test

The alphabet is the first relative root, core roots 3 and 5, and the two
specified Weyl lifts. The first twenty-two words lie in the Suzuki endpoint;
the other seventeen lie in the linear endpoint. Their actual validity is
proved in the coordinate and Weyl-action extensions. No mixed braid is among
these local words.

These are the finite local relations used in the F.4.8 pointed-pair argument.
They are extracted from the actual root groups, using Shinoda's coordinates
and the marked binary Ree inclusions. Extraction is only witness discovery;
the consumers prove every word equality in the literal endpoint.
-/
@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid
open Subgroup.CosetWordCertificate
def relator : Fin 39 → Word Nat := ![
[(3, true), (3, true)],
[(1, true), (1, true)],
[(2, true), (2, true), (2, true), (2, true)],
[(2, true), (0, false), (2, false), (0, true)],
[(3, true), (2, false), (3, true), (2, true)],
[(0, true), (0, true), (0, true), (0, true)],
[(1, true), (2, false), (2, false), (1, true), (2, false), (2, false)],
[(3, true), (0, false), (0, false), (3, true), (0, false), (3, true), (0, true)],
[(1, true), (2, true), (1, true), (2, true), (1, true), (2, true), (1, true), (2, true)],
[(3, true), (1, true), (3, true), (0, true), (3, true), (1, true), (3, true), (0, false)],
[(3, true), (1, true), (3, true), (2, true), (2, true), (3, true), (1, true), (3, true), (0, true), (0, true), (2, true), (2, true), (0, true), (0, true)],
[(0, true), (1, true), (2, true), (2, true), (0, true), (0, true), (3, true), (1, true), (3, true), (1, true), (0, false), (1, true), (0, false), (0, false), (1, true)],
[(0, false), (0, false), (2, true), (3, true), (1, true), (2, false), (1, true), (3, true), (0, false), (0, false), (2, true), (3, true), (1, true), (2, false), (1, true), (3, true)],
[(0, true), (1, true), (0, false), (1, true), (2, false), (0, false), (1, true), (0, true), (1, true), (3, true), (2, false), (0, false), (1, true), (0, true), (1, true), (2, false), (3, true), (1, true), (2, false)],
[(1, true), (2, true), (3, true), (1, true), (0, false), (1, true), (0, true), (3, true), (1, true), (2, false), (3, true), (1, true), (0, false), (1, true), (0, true), (2, true), (1, true), (2, true), (1, true), (3, true)],
[(1, true), (0, true), (2, true), (3, true), (1, true), (3, true), (0, true), (2, false), (3, true), (1, true), (3, true), (0, true), (0, true), (1, true), (2, false), (3, true), (1, true), (2, false), (1, true), (3, true)],
[(2, false), (1, true), (0, false), (0, false), (1, true), (2, true), (1, true), (0, false), (1, true), (0, false), (0, false), (1, true), (0, false), (0, false), (1, true), (0, false), (0, false), (1, true), (0, true), (1, true)],
[(1, true), (0, true), (1, true), (0, false), (2, true), (1, true), (0, false), (2, true), (1, true), (0, false), (1, true), (0, true), (1, true), (2, false), (0, false), (1, true), (2, false), (0, false), (1, true), (0, false)],
[(0, false), (0, false), (1, true), (0, true), (1, true), (2, false), (1, true), (2, true), (3, true), (1, true), (3, true), (2, false), (0, false), (0, false), (1, true), (0, false), (0, false), (1, true), (0, true), (1, true), (2, false)],
[(1, true), (0, false), (2, true), (1, true), (3, true), (1, true), (3, true), (0, false), (0, false), (2, true), (1, true), (0, false), (2, true), (1, true), (0, true), (1, true), (3, true), (1, true), (3, true), (0, false), (1, true), (2, true), (1, true), (0, false), (1, true), (0, true)],
[(1, true), (0, false), (0, false), (1, true), (2, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, false), (2, true), (1, true), (2, true), (3, true), (1, true), (3, true), (0, false), (1, true), (0, true), (1, true), (0, false), (1, true), (0, false), (2, false), (1, true), (0, true)],
[(1, true), (2, false), (0, false), (1, true), (0, true), (1, true), (0, true), (3, true), (1, true), (3, true), (1, true), (0, false), (1, true), (2, true), (0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (2, false), (1, true), (0, true), (0, true), (1, true), (0, true), (3, true), (1, true), (3, true), (2, true)],
[(1, true), (1, true)],
[(4, true), (4, true)],
[(0, true), (2, false), (0, false), (2, true)],
[(0, true), (0, true), (0, true), (0, true)],
[(2, true), (2, true), (2, true), (2, true)],
[(2, false), (1, true), (2, true), (2, true), (1, true), (2, false)],
[(4, true), (1, true), (4, true), (1, true), (4, true), (1, true)],
[(1, true), (2, true), (4, true), (0, false), (0, false), (4, true), (1, true), (2, false)],
[(1, true), (4, true), (0, true), (1, true), (4, true), (1, true), (0, false), (4, true)],
[(0, false), (4, true), (2, false), (0, false), (4, true), (0, true), (2, true), (4, true), (0, true), (4, true)],
[(1, true), (4, true), (2, true), (4, true), (0, false), (1, true), (0, true), (2, false), (1, true), (2, false), (0, true), (1, true), (0, false), (2, false)],
[(1, true), (0, true), (0, true), (2, false), (1, true), (0, false), (2, true), (1, true), (2, false), (4, true), (2, false), (4, true), (1, true), (0, false)],
[(1, true), (2, true), (1, true), (0, true), (1, true), (2, false), (0, true), (1, true), (0, false), (1, true), (2, false), (0, true), (1, true), (0, false), (2, true), (0, false)],
[(2, true), (4, true), (0, true), (4, true), (2, true), (4, true), (0, true), (4, true), (2, false), (4, true), (0, false), (4, true), (2, false), (4, true), (0, false), (4, true)],
[(1, true), (0, false), (2, false), (1, true), (0, false), (4, true), (0, false), (4, true), (2, false), (4, true), (0, true), (4, true), (0, true), (1, true), (0, true), (2, false), (1, true), (2, false)],
[(0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, false), (1, true), (0, true), (1, true), (0, true), (2, false), (1, true), (0, false), (0, false), (4, true), (0, false), (4, true), (2, false), (2, false)],
[(0, true), (1, true), (0, false), (2, true), (1, true), (0, false), (4, true), (0, false), (4, true), (0, true), (0, true), (1, true), (2, true), (0, false), (1, true), (0, false), (4, true), (0, false), (4, true), (0, true)]]
end Tits.AmalgamRigidity.FullRee.BadBraid
