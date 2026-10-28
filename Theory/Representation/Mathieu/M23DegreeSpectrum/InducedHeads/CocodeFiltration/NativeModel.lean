module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.Defs
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.Data

/-!+# The native comparison contract for the M23 cocode matrices

The saved matrices must represent the actual induction of the native M22
cocode along the point-9 stabilizer. An invertible change of coordinates
and its two generator equations suffice once this particular generator
pair is proved to generate M23. None of these facts is asserted here.

The contract retains the right-coset action, native marking and generator
order. A dimension equality alone cannot produce this witness. Its consumer
constructs the invariant flag and the literal successive quotient actions.
Source application: Guralnick--Malle I, Proposition 5.1, M23 paragraph.
-/

@[expose] public noncomputable section
open Sporadic.Mathieu
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration

/-- The native generators, in the order of the original GAP discovery data. -/
def actor : Fin 2 → M23 := ![m23GeneratorAInM23, m23GeneratorBInM23]

/-- A comparison with the actual coinduced action and generation of its actor.
This contract contains no filtration or irreducibility conclusion. -/
structure GeneratorCoordinates where
  equiv : Coordinates.Space false ≃ₗ[ZMod 2] Space
  intertwines : ∀ j v, equiv (canonicalCocodeAction (actor j) v) =
    (generatorMatrix j).mulVec (equiv v)
  generates : Subgroup.closure
    ({m23GeneratorAInM23, m23GeneratorBInM23} : Set M23) = ⊤

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration
