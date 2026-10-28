module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Steps00
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Steps01
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Steps02
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Steps03
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Steps04
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Steps05
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Steps06
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan.Steps07

/-!
# Identification of all 1000 source row vectors

The interval certificates cover all the required source indices. Their kernel
checks refer to the unchanged source tables. See `RowSpan/source/README.md`
for the proof structure, measurements and ATLAS attribution.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan

/-- Every nonempty source row word has its checked right-vector transition. -/
theorem all_steps : On 1 1000 StepCheck :=
  (((steps00.append steps01).append (steps02.append steps03)).append ((steps04.append steps05).append (steps06.append steps07)))

/-- Literal orbit-vector identification for every source word. -/
theorem rowOrbit_eq (i : Fin 1000) :
    rowOrbit i = RowArithmetic.vector 1000 Data.rowRows[i.val]! :=
  rowOrbit_eq_of_checks all_steps i

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RowSpan
