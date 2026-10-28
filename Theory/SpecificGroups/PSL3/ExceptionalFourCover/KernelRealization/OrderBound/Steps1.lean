module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.OrderBound.Steps1Row7

/-!
# Cardinality consequence of the 90-representative cover

The complete checked transition rows instantiate positive-word induction.
Source application: AS I.1.3(6), GLS3 §6.1.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate

theorem step1 (i : Fin 8) (r : Fin 90) :
    gen1 i * rep1 r = rep1 (act1 i r) * word gen2 (factor1 i r) := by
  fin_cases i
  · exact step1_row0 r
  · exact step1_row1 r
  · exact step1_row2 r
  · exact step1_row3 r
  · exact step1_row4 r
  · exact step1_row5 r
  · exact step1_row6 r
  · exact step1_row7 r

theorem card1_le : Nat.card (Submonoid.closure (Set.range gen1)) ≤
    90 * Nat.card (Submonoid.closure (Set.range gen2)) :=
  closure_card_le gen1 gen2 rep1 act1 factor1 0 rfl step1

end Matrix.PSL3.ExceptionalFourCover.KernelModel.OrderCertificate
