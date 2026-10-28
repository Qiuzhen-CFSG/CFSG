module

public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow.Products

/-!
# Involutions outside the two elementary Sylow candidates

Every element squaring to one is in one of the two displayed sublists or
is one of eight exceptional involutions. For each exception, only twelve
listed elements both square to one and commute with it. This is the finite
exclusion used for H.14.2(1), Aschbacher–Smith, printed p.397.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.ElementarySylow
open FusionCertificate
set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 600000 in
theorem square_cases : ∀ i : Fin 128,
    (∀ x, pointTable i (pointTable i x) = x) →
      (∃ b j, i = candidateIndex b j) ∨ ∃ k, i = exceptionalIndex k := by
  intro i
  fin_cases i <;> decide +kernel

private theorem exceptional_commuting_0 : ∀ i : Fin 128,
    (∀ x, pointTable i (pointTable i x) = x) →
    (∀ x, pointTable (exceptionalIndex 0) (pointTable i x) =
      pointTable i (pointTable (exceptionalIndex 0) x)) →
    ∃ j, i = commutingIndex 0 j := by
  intro i
  fin_cases i <;> decide +kernel

private theorem exceptional_commuting_1 : ∀ i : Fin 128,
    (∀ x, pointTable i (pointTable i x) = x) →
    (∀ x, pointTable (exceptionalIndex 1) (pointTable i x) =
      pointTable i (pointTable (exceptionalIndex 1) x)) →
    ∃ j, i = commutingIndex 1 j := by
  intro i
  fin_cases i <;> decide +kernel

private theorem exceptional_commuting_2 : ∀ i : Fin 128,
    (∀ x, pointTable i (pointTable i x) = x) →
    (∀ x, pointTable (exceptionalIndex 2) (pointTable i x) =
      pointTable i (pointTable (exceptionalIndex 2) x)) →
    ∃ j, i = commutingIndex 2 j := by
  intro i
  fin_cases i <;> decide +kernel

private theorem exceptional_commuting_3 : ∀ i : Fin 128,
    (∀ x, pointTable i (pointTable i x) = x) →
    (∀ x, pointTable (exceptionalIndex 3) (pointTable i x) =
      pointTable i (pointTable (exceptionalIndex 3) x)) →
    ∃ j, i = commutingIndex 3 j := by
  intro i
  fin_cases i <;> decide +kernel

private theorem exceptional_commuting_4 : ∀ i : Fin 128,
    (∀ x, pointTable i (pointTable i x) = x) →
    (∀ x, pointTable (exceptionalIndex 4) (pointTable i x) =
      pointTable i (pointTable (exceptionalIndex 4) x)) →
    ∃ j, i = commutingIndex 4 j := by
  intro i
  fin_cases i <;> decide +kernel

private theorem exceptional_commuting_5 : ∀ i : Fin 128,
    (∀ x, pointTable i (pointTable i x) = x) →
    (∀ x, pointTable (exceptionalIndex 5) (pointTable i x) =
      pointTable i (pointTable (exceptionalIndex 5) x)) →
    ∃ j, i = commutingIndex 5 j := by
  intro i
  fin_cases i <;> decide +kernel

private theorem exceptional_commuting_6 : ∀ i : Fin 128,
    (∀ x, pointTable i (pointTable i x) = x) →
    (∀ x, pointTable (exceptionalIndex 6) (pointTable i x) =
      pointTable i (pointTable (exceptionalIndex 6) x)) →
    ∃ j, i = commutingIndex 6 j := by
  intro i
  fin_cases i <;> decide +kernel

private theorem exceptional_commuting_7 : ∀ i : Fin 128,
    (∀ x, pointTable i (pointTable i x) = x) →
    (∀ x, pointTable (exceptionalIndex 7) (pointTable i x) =
      pointTable i (pointTable (exceptionalIndex 7) x)) →
    ∃ j, i = commutingIndex 7 j := by
  intro i
  fin_cases i <;> decide +kernel

theorem exceptional_commuting (k : Fin 8) (i : Fin 128)
    (hs : ∀ x, pointTable i (pointTable i x) = x)
    (hc : ∀ x, pointTable (exceptionalIndex k) (pointTable i x) =
      pointTable i (pointTable (exceptionalIndex k) x)) :
    ∃ j, i = commutingIndex k j := by
  fin_cases k
  · exact exceptional_commuting_0 i hs hc
  · exact exceptional_commuting_1 i hs hc
  · exact exceptional_commuting_2 i hs hc
  · exact exceptional_commuting_3 i hs hc
  · exact exceptional_commuting_4 i hs hc
  · exact exceptional_commuting_5 i hs hc
  · exact exceptional_commuting_6 i hs hc
  · exact exceptional_commuting_7 i hs hc

end Sporadic.Mathieu.M23Geometry.ElementarySylow
