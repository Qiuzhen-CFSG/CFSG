module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.RelatorCertificates.Checked

import Mathlib.Tactic.FinCases

/-!
# Shared-subword certificates for the local presentation

The words and masks are from `UpperBound.Data` and its adjacent
`source/relator_masks.json`. The generator matrices implement the ATLAS
`J4G1-max1W1` program. Repeated subwords are factored into binary products;
all proposed products are checked by kernel reduction of packed arithmetic.
The external generator supplies witnesses only, never trusted evaluations.
-/

public section
namespace Janko4.Cardinality.QuotientCount.UpperBound
open KernelCount KernelCount.Relations Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

/-- Every explicit presentation relator evaluates to its certified kernel product. -/
theorem localRelator_matrix_evaluation (i : Fin 47) :
    KernelCount.representation hA hB (localRelator hA hB i) =
      KernelCount.matrixProduct (fun j => (relatorMask i).testBit j.val) := by
  fin_cases i
  · exact RelatorCertificates.evaluation_0 hA hB
  · exact RelatorCertificates.evaluation_1 hA hB
  · exact RelatorCertificates.evaluation_2 hA hB
  · exact RelatorCertificates.evaluation_3 hA hB
  · exact RelatorCertificates.evaluation_4 hA hB
  · exact RelatorCertificates.evaluation_5 hA hB
  · exact RelatorCertificates.evaluation_6 hA hB
  · exact RelatorCertificates.evaluation_7 hA hB
  · exact RelatorCertificates.evaluation_8 hA hB
  · exact RelatorCertificates.evaluation_9 hA hB
  · exact RelatorCertificates.evaluation_10 hA hB
  · exact RelatorCertificates.evaluation_11 hA hB
  · exact RelatorCertificates.evaluation_12 hA hB
  · exact RelatorCertificates.evaluation_13 hA hB
  · exact RelatorCertificates.evaluation_14 hA hB
  · exact RelatorCertificates.evaluation_15 hA hB
  · exact RelatorCertificates.evaluation_16 hA hB
  · exact RelatorCertificates.evaluation_17 hA hB
  · exact RelatorCertificates.evaluation_18 hA hB
  · exact RelatorCertificates.evaluation_19 hA hB
  · exact RelatorCertificates.evaluation_20 hA hB
  · exact RelatorCertificates.evaluation_21 hA hB
  · exact RelatorCertificates.evaluation_22 hA hB
  · exact RelatorCertificates.evaluation_23 hA hB
  · exact RelatorCertificates.evaluation_24 hA hB
  · exact RelatorCertificates.evaluation_25 hA hB
  · exact RelatorCertificates.evaluation_26 hA hB
  · exact RelatorCertificates.evaluation_27 hA hB
  · exact RelatorCertificates.evaluation_28 hA hB
  · exact RelatorCertificates.evaluation_29 hA hB
  · exact RelatorCertificates.evaluation_30 hA hB
  · exact RelatorCertificates.evaluation_31 hA hB
  · exact RelatorCertificates.evaluation_32 hA hB
  · exact RelatorCertificates.evaluation_33 hA hB
  · exact RelatorCertificates.evaluation_34 hA hB
  · exact RelatorCertificates.evaluation_35 hA hB
  · exact RelatorCertificates.evaluation_36 hA hB
  · exact RelatorCertificates.evaluation_37 hA hB
  · exact RelatorCertificates.evaluation_38 hA hB
  · exact RelatorCertificates.evaluation_39 hA hB
  · exact RelatorCertificates.evaluation_40 hA hB
  · exact RelatorCertificates.evaluation_41 hA hB
  · exact RelatorCertificates.evaluation_42 hA hB
  · exact RelatorCertificates.evaluation_43 hA hB
  · exact RelatorCertificates.evaluation_44 hA hB
  · exact RelatorCertificates.evaluation_45 hA hB
  · exact RelatorCertificates.evaluation_46 hA hB

/-- All 47 presentation relators belong to the actual local matrix kernel. -/
theorem localRelator_mem (i : Fin 47) :
    localRelator hA hB i ∈ localKernel hA hB :=
  relator_mem_of_matrix_evaluation hA hB i (localRelator_matrix_evaluation hA hB i)

end Janko4.Cardinality.QuotientCount.UpperBound
