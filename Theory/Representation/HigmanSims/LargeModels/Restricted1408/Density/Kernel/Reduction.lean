module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Initial
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block00
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block01
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block02
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block03
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block04
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block05
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block06
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block07
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block08
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block09
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block10
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block11
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block12
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block13
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block14
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block15
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block16
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block17
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block18
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block19
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block20
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Block21
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.Final

/-!
# The complete checked reduction of the degree-1408 packed table

The indexed elimination checks every pivot and every resulting row, then checks
both reindexings to the unchanged published normal form. No multiplication,
density, cyclicity, irreducibility, or descent premise is used. See
`Reduction/source/README.md` for the computational proof and attribution.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData

/-- The literal proposed table and the published normal form have identical solutions. -/
theorem reductionCertificate : ReductionCertificate := by
  intro w
  have h0 := IndexedReduction.solutions0000 w
  have h1 := (IndexedReduction.solutions0064 w).trans h0
  have h2 := (IndexedReduction.solutions0128 w).trans h1
  have h3 := (IndexedReduction.solutions0192 w).trans h2
  have h4 := (IndexedReduction.solutions0256 w).trans h3
  have h5 := (IndexedReduction.solutions0320 w).trans h4
  have h6 := (IndexedReduction.solutions0384 w).trans h5
  have h7 := (IndexedReduction.solutions0448 w).trans h6
  have h8 := (IndexedReduction.solutions0512 w).trans h7
  have h9 := (IndexedReduction.solutions0576 w).trans h8
  have h10 := (IndexedReduction.solutions0640 w).trans h9
  have h11 := (IndexedReduction.solutions0704 w).trans h10
  have h12 := (IndexedReduction.solutions0768 w).trans h11
  have h13 := (IndexedReduction.solutions0832 w).trans h12
  have h14 := (IndexedReduction.solutions0896 w).trans h13
  have h15 := (IndexedReduction.solutions0960 w).trans h14
  have h16 := (IndexedReduction.solutions1024 w).trans h15
  have h17 := (IndexedReduction.solutions1088 w).trans h16
  have h18 := (IndexedReduction.solutions1152 w).trans h17
  have h19 := (IndexedReduction.solutions1216 w).trans h18
  have h20 := (IndexedReduction.solutions1280 w).trans h19
  have h21 := (IndexedReduction.solutions1344 w).trans h20
  have h22 := (IndexedReduction.solutions1407 w).trans h21
  exact (IndexedReduction.final_solutions w).trans h22

end Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData
