module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block00
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block01
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block02
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block03
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block04
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block05
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block06
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block07
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block08
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block09
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Block10
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowData

/-!
# Complete packed row recurrence certificate

The independently checked blocks concatenate to all 1407 nonseed steps.
A separate kernel check compares their inputs, outputs and generator choices
with the literal published arrays, including each specified parent lookup.
No mathematical property of the generated matrix algebra is assumed.
Source: `../source/README.md` and its preserved `cyclic_witness.json`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences

def blocks : List (List Step) := [block00, block01, block02, block03, block04, block05, block06, block07, block08, block09, block10]

def steps : List Step := blocks.flatten

theorem steps_products : products aRows.toList bRows.toList steps = true := by
  apply products_flatten
  simp only [blocks, List.all_cons, List.all_nil, block00_products,
    block01_products,
    block02_products,
    block03_products,
    block04_products,
    block05_products,
    block06_products,
    block07_products,
    block08_products,
    block09_products,
    block10_products, Bool.and_true]

set_option maxRecDepth 4096 in
theorem steps_correspondence : correspondence steps
    rowOrbitRows.toList.tail rowOrbitParents.toList.tail rowOrbitChoices.toList.tail = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem steps_parents : parentScan 0 rowOrbitRows.toList
    (inputs steps rowOrbitParents.toList.tail) = true := by
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences
