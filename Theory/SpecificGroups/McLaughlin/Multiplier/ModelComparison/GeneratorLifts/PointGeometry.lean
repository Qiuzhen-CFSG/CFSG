module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.PointData
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.Blocks
/-!
# The 275 coordinate rows lie in the actual Leech triangle slice

The certificates check parity, the displayed Golay word, the sum congruence,
and the three slice equations. Batches of 25 keep kernel reduction bounded;
declarations are checked serially after the monolithic check exceeded the
compiler memory guard. These are the attributed coordinates of PointData.
-/
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped BigOperators
set_option maxRecDepth 10000
set_option Elab.async false

private def PointCertificate (j : Fin 275) : Prop :=
  (∀ i : Omega, vectorOfData (pointVectors j) i % 2 = pointParity j) ∧
  halfResidue (vectorOfData (pointVectors j)) (pointParity j) = wordOfMask (pointCoeffs j) ∧
  (∑ i : Omega, vectorOfData (pointVectors j) i) % 8 = 4 * pointParity j ∧
  integerDot (vectorOfData (pointVectors j)) (vectorOfData (pointVectors j)) = 32 ∧
  integerDot (normSixVector co3MarkedCoordinate).val (vectorOfData (pointVectors j)) = 24 ∧
  integerDot mclEndpoint.val (vectorOfData (pointVectors j)) = 16

private instance pointCertificate_decidable (j : Fin 275) : Decidable (PointCertificate j) := by
  unfold PointCertificate
  infer_instance

private theorem pointCert0 : ∀ j : Fin 25, PointCertificate (pointBlock 0 j) := by
  apply allFin
  decide +kernel

private theorem pointCert1 : ∀ j : Fin 25, PointCertificate (pointBlock 1 j) := by
  apply allFin
  decide +kernel

private theorem pointCert2 : ∀ j : Fin 25, PointCertificate (pointBlock 2 j) := by
  apply allFin
  decide +kernel

private theorem pointCert3 : ∀ j : Fin 25, PointCertificate (pointBlock 3 j) := by
  apply allFin
  decide +kernel

private theorem pointCert4 : ∀ j : Fin 25, PointCertificate (pointBlock 4 j) := by
  apply allFin
  decide +kernel

private theorem pointCert5 : ∀ j : Fin 25, PointCertificate (pointBlock 5 j) := by
  apply allFin
  decide +kernel

private theorem pointCert6 : ∀ j : Fin 25, PointCertificate (pointBlock 6 j) := by
  apply allFin
  decide +kernel

private theorem pointCert7 : ∀ j : Fin 25, PointCertificate (pointBlock 7 j) := by
  apply allFin
  decide +kernel

private theorem pointCert8 : ∀ j : Fin 25, PointCertificate (pointBlock 8 j) := by
  apply allFin
  decide +kernel

private theorem pointCert9 : ∀ j : Fin 25, PointCertificate (pointBlock 9 j) := by
  apply allFin
  decide +kernel

private theorem pointCert10 : ∀ j : Fin 25, PointCertificate (pointBlock 10 j) := by
  apply allFin
  decide +kernel

private theorem pointCertAll (x : Fin 275) : PointCertificate x := by
  apply allPointBlocks PointCertificate _ x
  intro b
  fin_cases b
  · exact pointCert0
  · exact pointCert1
  · exact pointCert2
  · exact pointCert3
  · exact pointCert4
  · exact pointCert5
  · exact pointCert6
  · exact pointCert7
  · exact pointCert8
  · exact pointCert9
  · exact pointCert10

theorem pointVectors_mem (j : Fin 275) : vectorOfData (pointVectors j) ∈ leech :=
  certificate_mem _ _ _ (pointCertAll j).1 (pointCertAll j).2.1 (pointCertAll j).2.2.1

theorem pointVectors_slice (j : Fin 275) :
    integerDot (vectorOfData (pointVectors j)) (vectorOfData (pointVectors j)) = 32 ∧
    integerDot (normSixVector co3MarkedCoordinate).val (vectorOfData (pointVectors j)) = 24 ∧
    integerDot mclEndpoint.val (vectorOfData (pointVectors j)) = 16 :=
  (pointCertAll j).2.2.2

def markedPoint (j : Fin 275) : Atlas.Sporadic.McLaughlin.Points :=
  ⟨⟨vectorOfData (pointVectors j), pointVectors_mem j⟩, pointVectors_slice j⟩

end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
