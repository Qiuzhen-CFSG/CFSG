module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.OrderBound.Steps0Row1

/-!
# Cardinality consequence of the 224-representative cover

The complete checked transition rows instantiate positive-word induction.
Source application: AS I.1.3(6), GLS3 §6.1.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate

theorem step0 (i : Fin 2) (r : Fin 224) :
    gen0 i * rep0 r = rep0 (act0 i r) * word gen1 (factor0 i r) := by
  fin_cases i
  · exact step0_row0 r
  · exact step0_row1 r

theorem card0_le : Nat.card (Submonoid.closure (Set.range gen0)) ≤
    224 * Nat.card (Submonoid.closure (Set.range gen1)) :=
  closure_card_le gen0 gen1 rep0 act0 factor0 0 rfl step0

end Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate
