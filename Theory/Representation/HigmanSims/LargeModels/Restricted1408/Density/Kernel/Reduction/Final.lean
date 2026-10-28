module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Reduction.FinalCheck

/-!
# Checked row operations for the degree-1408 table

These untrusted proposals use fixed row indices and independently validate each
pivot. The pointwise XOR formula is proved in `Indexed.lean`; the following
finite checks use only Lean's kernel. See `source/README.md` in this directory
and the original numerical attribution in `../../source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData.IndexedReduction
open PackedBinaryRows.Indexed
open Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates

theorem final_solutions (w : Fin 1408 → ZMod 2) :
    PackedBinaryRows.stateSolutions 1408 kernelNormalForm w ↔ solutions 1408 1408 rows1407 w := by
  have hn := solutions_normal 1407 3037566777681267535834465479477380210446177044093850219542017719937461953016038750181753272333662566324377528990954025738249985938610247160176175638580520348176498059831193934536735574962891405363127719209003405508515098615267758094552103906262663260137666912768254730890609589573719963388200362861770965963113113402544595261017349602099599066548935105647282472801271845992658676808526609012602330107685271989261917926201689 w
  exact hn.symm.trans (solutions_reindex 1408 1408 rows1407 canonicalRows
    (fun i => forward[i]!) (fun i => backward[i]!) forwardChecked backwardChecked w)

end Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData.IndexedReduction
