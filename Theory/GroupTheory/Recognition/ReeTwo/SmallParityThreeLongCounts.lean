module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongCentralizers

/-!
# Profile counts for long rank-three parity rows 0, 1, and 5

Replace each inner commuting enumeration by the independently verified
centralizer table, then count the eight coordinate fibers. The order tests use
the original collected powers; the square-centralizer condition is vacuous by
`tests_spec`. All finite certificates are checked by kernel reduction.

This is a certificate on the explicit parameters and ambient operations. It
requires no closure-membership or subgroup-structure certificate.

Source: Shinoda (1975), (2.3), pp. 81–82, through
`SmallParityThreeLongCoordinates`; the profile conventions are from
`SmallParityProfiles`.
-/

@[expose] public section
namespace ReeTwo.SylowModel.SmallParityLong
set_option maxRecDepth 32768

private def reducedTest (c k : Fin 3) (n : Fin (Counts.size c)) : Prop :=
  let t := smallParityThreeTests (index c) k
  Counts.centralTable c n = t.2.1 ∧ orderTest t.1 (element c (Counts.enumerate c n))
private instance (c k : Fin 3) (n : Fin (Counts.size c)) : Decidable (reducedTest c k n) := by
  unfold reducedTest; infer_instance

private theorem test_iff (c k : Fin 3) (n : Fin (Counts.size c)) :
    test c k (element c (Counts.enumerate c n)) ↔ reducedTest c k n := by
  simp only [test, reducedTest, (tests_spec c k).2, true_or, and_true,
    Counts.commutingCount_table]
  exact and_comm

private def reducedCount (c k : Fin 3) (v : SmallParityThreeQuotient) : ℕ :=
  Fintype.card {n : Fin (Counts.size c) //
    coordinates c (element c (Counts.enumerate c n)) = v ∧ reducedTest c k n}

private theorem fiberCount_eq (c k : Fin 3) (v : SmallParityThreeQuotient) :
    fiberCount c k v = reducedCount c k v := by
  unfold fiberCount reducedCount
  apply (Fintype.card_congr ((Counts.enumeration c).subtypeEquiv ?_)).symm
  intro n
  exact and_congr Iff.rfl (test_iff c k n).symm

set_option maxHeartbeats 4000000 in
private theorem reduced_certificate : ∀ (c : Fin 3) (v : SmallParityThreeQuotient),
    (reducedCount c 0 v, reducedCount c 1 v, reducedCount c 2 v) =
      smallParityThreeProfile (index c) v := by decide +kernel

/-- Exact finite profile counts for the three long rows. -/
theorem count_certificate : ∀ (c : Fin 3) (v : SmallParityThreeQuotient),
    (fiberCount c 0 v, fiberCount c 1 v, fiberCount c 2 v) =
      smallParityThreeProfile (index c) v := by
  intro c v
  simp only [fiberCount_eq]
  exact reduced_certificate c v
end ReeTwo.SylowModel.SmallParityLong
