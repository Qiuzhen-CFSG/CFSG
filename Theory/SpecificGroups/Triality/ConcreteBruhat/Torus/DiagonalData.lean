module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Coordinates

/-!
# The expected coroot diagonal in the actual Geck basis

A coroot fixes the four Cartan vectors and multiplies a root vector by
t raised to its integral Cartan pairing with that coroot. This definition
uses the same 28-dimensional lattice as the published split group.
No equality with a Geck word is assumed or asserted in this module.

Source: the Chevalley coroot formulas, GLS3 §2.4 and 1.12.1
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.ConcreteBruhat.TorusCoordinates
open Parabolics.RankOneMatrices
open Theory.AlgebraicGroup.StandardRootSystem
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

/-- Integral weight of a Geck basis vector for a numbered simple coroot. -/
def corootWeight (i : Fin 4) : LatticeIndex → ℤ :=
  Sum.elim (fun _ => 0)
    (fun r => (typeDRootPairing 2).pairingIn ℤ r (typeDSimpleRootIndex 2 i))

/-- The specified diagonal matrix, before proving the coroot-word formula. -/
def corootDiagonal (P : Parameters) (i : Fin 4) (t : (ExtensionField P)ˣ) :
    Matrix LatticeIndex LatticeIndex (ExtensionField P) :=
  Matrix.diagonal (fun r => (t.val) ^ corootWeight i r)

end Triality.Standard.ConcreteBruhat.TorusCoordinates
