module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The local residuals of the concrete triple cover of A₆

These are the actual inverse images of natural-module point stabilizers under
the coordinate map of the even hexacode group. The second residual is formed
from the commutator with a supplied Sylow two-subgroup. Keeping the whole
stabilizer separate from its two-residual is essential: their coordinate
images are S₄ and A₄ respectively.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed p.877. The definitions use the
licensed hexacode carrier imported by `Cover`; no quotient order is assumed.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Representation.Hexacode.CubicLocalModel

abbrev H := Atlas.Codes.HexEvenAutomorphisms
abbrev Natural := BinaryPermutation.natural (Fin 6)

/-- The six-coordinate action of the actual triple cover. -/
def coordinate : H →* Equiv.Perm (Fin 6) :=
  (alternatingGroup (Fin 6)).subtype.comp Atlas.Codes.hexEvenCoordinate

/-- The binary natural action pulled back along the coordinate map. -/
def naturalAction : Representation (ZMod 2) H Natural :=
  (BinaryPermutation.naturalRepresentation (Fin 6)).comp coordinate

/-- The full inverse image of the stabilizer of a specified subspace. -/
def stabilizer (W : Submodule (ZMod 2) Natural) : Subgroup H :=
  BinaryOffender.subspaceStabilizer naturalAction W

/-- The intrinsic two-residual embedded in the cover. -/
def residual (A : Subgroup H) : Subgroup H := (pResidual 2 A).map A.subtype

/-- The actual local residual of the natural point stabilizer. -/
def pointResidual (W : Submodule (ZMod 2) Natural) : Subgroup H :=
  residual (stabilizer W)

/-- The residual of its commutator with the specified Sylow subgroup. -/
def commutatorResidual (W : Submodule (ZMod 2) Natural) (P : Sylow 2 H) : Subgroup H :=
  residual ⁅pointResidual W, (P : Subgroup H)⁆

end Representation.Hexacode.CubicLocalModel
