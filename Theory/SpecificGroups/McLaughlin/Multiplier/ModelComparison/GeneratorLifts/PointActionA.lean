module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.PointData
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.MatrixAction
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.Blocks
/-!
# Exact point images for generator A

The integer certificate clears the denominator 4. Its right side uses the
literal inverse-source permutation defining the original carrier, so it
certifies the specified left action under the common point labelling.
-/
@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices
open scoped Matrix
open Sporadic.LeechRelated.McL
set_option maxRecDepth 10000
set_option Elab.async false

private def PointActionACertificate (j : Fin 275) : Prop :=
  matrixAData *ᵥ pointVectors j = (4 : ℤ) • pointVectors (generatorA j)

private instance pointActionACertificate_decidable (j : Fin 275) : Decidable (PointActionACertificate j) := by
  unfold PointActionACertificate
  infer_instance

private theorem actionCert0 : ∀ j : Fin 25, PointActionACertificate (pointBlock 0 j) := by
  apply allFin
  decide +kernel

private theorem actionCert1 : ∀ j : Fin 25, PointActionACertificate (pointBlock 1 j) := by
  apply allFin
  decide +kernel

private theorem actionCert2 : ∀ j : Fin 25, PointActionACertificate (pointBlock 2 j) := by
  apply allFin
  decide +kernel

private theorem actionCert3 : ∀ j : Fin 25, PointActionACertificate (pointBlock 3 j) := by
  apply allFin
  decide +kernel

private theorem actionCert4 : ∀ j : Fin 25, PointActionACertificate (pointBlock 4 j) := by
  apply allFin
  decide +kernel

private theorem actionCert5 : ∀ j : Fin 25, PointActionACertificate (pointBlock 5 j) := by
  apply allFin
  decide +kernel

private theorem actionCert6 : ∀ j : Fin 25, PointActionACertificate (pointBlock 6 j) := by
  apply allFin
  decide +kernel

private theorem actionCert7 : ∀ j : Fin 25, PointActionACertificate (pointBlock 7 j) := by
  apply allFin
  decide +kernel

private theorem actionCert8 : ∀ j : Fin 25, PointActionACertificate (pointBlock 8 j) := by
  apply allFin
  decide +kernel

private theorem actionCert9 : ∀ j : Fin 25, PointActionACertificate (pointBlock 9 j) := by
  apply allFin
  decide +kernel

private theorem actionCert10 : ∀ j : Fin 25, PointActionACertificate (pointBlock 10 j) := by
  apply allFin
  decide +kernel

private theorem actionCertAll (x : Fin 275) : PointActionACertificate x := by
  apply allPointBlocks PointActionACertificate _ x
  intro b
  fin_cases b
  · exact actionCert0
  · exact actionCert1
  · exact actionCert2
  · exact actionCert3
  · exact actionCert4
  · exact actionCert5
  · exact actionCert6
  · exact actionCert7
  · exact actionCert8
  · exact actionCert9
  · exact actionCert10

theorem mapA_point (j : Fin 275) :
    mapA (rationalEmbedding (vectorOfData (pointVectors j))) =
      rationalEmbedding (vectorOfData (pointVectors (generatorA j))) :=
  mapA_vector _ _ (actionCertAll j)

end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
