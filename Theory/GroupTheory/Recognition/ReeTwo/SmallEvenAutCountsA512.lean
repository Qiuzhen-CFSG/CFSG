module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenAutCountsA512Arithmetic

/-!
# The six intrinsic order-centralizer fiber profiles

The exact 512-element parametrizations transport each fixed coordinate fiber
to a finite filter. The arithmetic certificate computes orders and centralizers
inside the original candidate. Kernel reduction of these filters gives exactly
the five rank-four tables and the corrected rank-three table, with their
original coordinate and basis conventions.

Source: Shinoda (1975), (2.3), pp. 81–82, through the carrier and arithmetic
certificates and the profile conventions in `SmallEvenAutProfilesA`.
-/

namespace ReeTwo.SylowModel
open ReeTwo.SmallEvenAutProfilesA SmallEvenAutCountsA512
set_option maxRecDepth 32768
set_option synthInstance.maxSize 8192

private def fourIdx : Fin 5 → Fin 6 := ![0,1,2,4,5]
private def fourCount (j : Fin 5) (k : Fin 2) (v : FourQuotient) : ℕ :=
  Fintype.card {n : Fin 512 //
    smallEvenFourCoordinatesA512 j (smallEvenElementA512 (fourIdx j) (parameters n)) = v ∧
      (invariantTable (fourIdx j) n).1 = (fourTests (smallEvenFourRowA512 j) k).1 ∧
      (invariantTable (fourIdx j) n).2 = (fourTests (smallEvenFourRowA512 j) k).2.1}
private def threeCount (v : ThreeQuotient) : ℕ :=
  Fintype.card {n : Fin 512 //
    smallEvenThreeCoordinatesA512 (smallEvenElementA512 3 (parameters n)) = v ∧
      (invariantTable 3 n).1 = threeTest.1 ∧ (invariantTable 3 n).2 = threeTest.2.1}

private theorem card_four (j : Fin 5) (k : Fin 2) (v : FourQuotient) :
    Nat.card {x : smallEvenCandidate (fourIndex (smallEvenFourRowA512 j)) //
      smallEvenFourMapA512 j x = v ∧
        MulAut.orderCentralizerTest (fourTests (smallEvenFourRowA512 j) k) x} =
      fourCount j k v := by
  have ho : ∀ j k, (fourTests (smallEvenFourRowA512 j) k).1 = 2 ∨
      (fourTests (smallEvenFourRowA512 j) k).1 = 4 := by decide
  have hz : ∀ j k, (fourTests (smallEvenFourRowA512 j) k).2.2 = 0 := by decide
  fin_cases j
  · exact card_orderCentralizerTest 0 (smallEvenFourCoordinatesA512 0) v _ (ho 0 k) (hz 0 k)
  · exact card_orderCentralizerTest 1 (smallEvenFourCoordinatesA512 1) v _ (ho 1 k) (hz 1 k)
  · exact card_orderCentralizerTest 2 (smallEvenFourCoordinatesA512 2) v _ (ho 2 k) (hz 2 k)
  · exact card_orderCentralizerTest 4 (smallEvenFourCoordinatesA512 3) v _ (ho 3 k) (hz 3 k)
  · exact card_orderCentralizerTest 5 (smallEvenFourCoordinatesA512 4) v _ (ho 4 k) (hz 4 k)

private theorem card_three (v : ThreeQuotient) :
    smallEvenThreeCoordinateProfileA512 v = threeCount v :=
  card_orderCentralizerTest 3 smallEvenThreeCoordinatesA512 v threeTest (Or.inr rfl) rfl

set_option Elab.async false in
set_option maxHeartbeats 16000000 in
private theorem four_certificate : ∀ j v,
    (fourCount j 0 v, fourCount j 1 v) = fourProfile (smallEvenFourRowA512 j) v := by
  decide +kernel

set_option Elab.async false in
set_option maxHeartbeats 4000000 in
private theorem three_certificate : ∀ v, threeCount v = threeProfile v := by decide +kernel

/-- The five rank-four coordinate maps have exactly the prescribed intrinsic
order/centralizer fiber counts in the original generator closures. -/
public theorem smallEvenFourCoordinateProfileA512_eq (j : Fin 5) (v : FourQuotient) :
    smallEvenFourCoordinateProfileA512 j v = fourProfile (smallEvenFourRowA512 j) v := by
  unfold smallEvenFourCoordinateProfileA512
  rw [card_four, card_four]
  exact four_certificate j v

/-- Candidate 4's corrected three coordinates have the prescribed intrinsic
order/centralizer fiber counts. -/
public theorem smallEvenThreeCoordinateProfileA512_eq (v : ThreeQuotient) :
    smallEvenThreeCoordinateProfileA512 v = threeProfile v := by
  rw [card_three]
  exact three_certificate v

end ReeTwo.SylowModel
