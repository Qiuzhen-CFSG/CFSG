module

public import Theory.SpecificGroups.SymplecticFour.Flag
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder.PairRecurrence

/-!
# Order of the symplectic four-space matrix group

The actual matrix group over a finite field of order q has order
q⁴(q² − 1)(q⁴ − 1). Apply the normalized-hyperbolic-pair orbit-stabilizer
recurrence twice, ending with the trivial rank-zero matrix group.
The proof works in every characteristic, including the characteristic-two
case needed for the Sylow subgroup of the standard flag.

Source: the ATLAS pair-counting argument, attributed and licensed in
`AmbientOrder/PairRecurrence.lean`. This supplies the ambient-order prerequisite
for Aschbacher--Smith, F.1.12(I)(2), printed pp.262–264.
-/

namespace Theory.SpecificGroups.SymplecticFour

/-- The order of the actual symplectic four-space matrix carrier over any finite field. -/
public theorem card_sp (F : Type*) [Field F] [Finite F] :
    Nat.card (Sp F) = (Nat.card F)^4 * ((Nat.card F)^2 - 1) * ((Nat.card F)^4 - 1) := by
  change Nat.card (Matrix.symplecticGroup (Fin (1 + 1)) F) = _
  rw [AmbientOrderProof.card_sp_succ, AmbientOrderProof.card_sp_succ (n := 0)]
  have hzero : Nat.card (Matrix.symplecticGroup (Fin 0) F) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  norm_num [hzero]
  ring

end Theory.SpecificGroups.SymplecticFour
