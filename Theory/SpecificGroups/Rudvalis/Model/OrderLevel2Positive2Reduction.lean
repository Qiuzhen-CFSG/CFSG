module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Reduction

/-!
# Cancellation batches for the third Rudvalis level-2 generator

Twenty-six of the 256 four-representative batches reduce entirely by free
cancellation.  The remaining batches are certified pointwise in the bounded
modules imported by `OrderLevel2Positive2`.

Source: the ATLAS degree-4060 witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.OrderLevel2Positive2
open Level2Reduction
set_option Elab.async false

@[expose] public def algebraicBatch (b : Fin 256) : Prop :=
  b.val ∈ [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 14, 17, 20, 23, 26, 27, 29, 32,
    39, 43, 51, 62, 66, 76, 93, 111]

public instance (b : Fin 256) : Decidable (algebraicBatch b) :=
  inferInstanceAs (Decidable (_ ∈ _))

set_option maxRecDepth 30000 in
private theorem algebraic_checks : ∀ b : Fin 256, algebraicBatch b →
    ∀ r : Fin 4, algebraic 2 (batchRep b r) := by
  apply allFin
  decide +kernel

public theorem algebraic_batches (b : Fin 256) (h : algebraicBatch b) :
    stepBatch 2 b := by
  apply ofStepBatchCheck
  intro r
  exact Or.inl (algebraic_checks b h r)

end Rudvalis.OrderCertificate.OrderLevel2Positive2
