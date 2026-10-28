module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.InitialCheck

/-! The checked input table has the literal initial homogeneous solution space. -/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData.IndexedReduction
open PackedBinaryRows.Indexed
open Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates

theorem solutions0000 (w : Fin 1408 → ZMod 2) :
    solutions 1408 1408 rows0000 w ↔ PackedBinaryRows.stateSolutions 1408 state0000 w := by
  have he (i : Nat) (hi : i < 1408) : sRows[i]! = rows0000 i := by
    simpa only [initialCheck, Nat.zero_add, beq_iff_eq] using
      (checkRange_spec initialCheck 0 1408).mp initialChecked i hi
  have hi : solutions 1408 1408 rows0000 w ↔ solutions 1408 1408 (fun i => sRows[i]!) w := by
    constructor
    · intro h i hi
      simpa only [he i hi] using h i hi
    · intro h i hi
      simpa only [he i hi] using h i hi
  have hs := solutions_array 1408 1408 sRows (by decide +kernel) w
  exact hi.trans (by simpa only [PackedBinaryRows.stateSolutions, state0000,
    PackedBinaryRows.solutions_nil, true_and] using hs)

end Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData.IndexedReduction
