module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Steps00
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Steps01
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Steps02
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Steps03
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Steps04
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Steps05
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Steps06
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits.Steps07

/-!
# All literal degree-1000 column-word transitions

The eight checked intervals cover the 999 nonroot source words. Each transition
certifies an earlier parent, equality of the actual shared word with the new
letter prepended to its parent, and the packed vector product in the corresponding
shared transpose tree. False denotes A and true denotes B.

Balanced interval concatenation assembles the kernel-checked numerical witnesses.
The independent transpose certificates connect these products to the published
generators via `ColumnSpan.columnOrbit_eq_of_checks`.

Source: R. A. Wilson et al., *ATLAS of Finite Group Representations*,
HSG1-f2r1000B0 and `Binary/source/density1000.json`.
See `Orbits/source/README.md` for attribution and source rights.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits

/-- All 999 prepended source-word transitions, with their literal vector products. -/
theorem stepsChecks : ColumnSpan.On
    (ColumnSpan.OrbitStep ColumnSpan.aTransposeTree ColumnSpan.bTransposeTree
      ColumnSpan.columnTree ColumnSpan.wordTree) 1 1000 :=
  ((steps00.append steps01).append (steps02.append steps03)).append
    ((steps04.append steps05).append (steps06.append steps07))

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.ColumnSpan.Orbits
