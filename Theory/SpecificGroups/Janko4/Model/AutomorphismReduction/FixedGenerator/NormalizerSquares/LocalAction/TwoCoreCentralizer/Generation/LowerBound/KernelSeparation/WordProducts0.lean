module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.KernelSeparation.Matrices
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Evaluations

/-!
# Products certifying the conjugate factors

For each appended letter L, the checked matrix identity is
`L * C_new = C_old * L`. Invertibility of the source letter
then identifies the new matrix with its conjugate.

Source: the ATLAS `J4G1-max2W1` program and the witness file
`LowerBound/source/lower_candidate.json`; attribution is in
`TwoCoreCentralizer/source/README.md`. All numerical claims are
checked by Lean kernel reduction.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem conjugate_product_2 :
    packedMul w14Rows (factorRows 2) = packedMul (factorRows 1) w14Rows := by
  apply Vector.ext
  intro k hk
  change (packedMul w14Rows (factorRows 2)).get ⟨k, hk⟩ =
    (packedMul (factorRows 1) w14Rows).get ⟨k, hk⟩
  simp only [packedMul, get_ofFn]
  exact (show ∀ k : Fin 112,
    packedRow (w14Rows.get k) (factorRows 2) =
      packedRow ((factorRows 1).get k) w14Rows from by
      simp only [packedRow, factorRows, get_ofFn]
      decide +kernel) ⟨k, hk⟩

theorem conjugate_product_3 :
    packedMul w14Rows (factorRows 3) = packedMul (factorRows 2) w14Rows := by
  apply Vector.ext
  intro k hk
  change (packedMul w14Rows (factorRows 3)).get ⟨k, hk⟩ =
    (packedMul (factorRows 2) w14Rows).get ⟨k, hk⟩
  simp only [packedMul, get_ofFn]
  exact (show ∀ k : Fin 112,
    packedRow (w14Rows.get k) (factorRows 3) =
      packedRow ((factorRows 2).get k) w14Rows from by
      simp only [packedRow, factorRows, get_ofFn]
      decide +kernel) ⟨k, hk⟩

theorem conjugate_product_4 :
    packedMul w10Rows (factorRows 4) = packedMul (factorRows 3) w10Rows := by
  apply Vector.ext
  intro k hk
  change (packedMul w10Rows (factorRows 4)).get ⟨k, hk⟩ =
    (packedMul (factorRows 3) w10Rows).get ⟨k, hk⟩
  simp only [packedMul, get_ofFn]
  exact (show ∀ k : Fin 112,
    packedRow (w10Rows.get k) (factorRows 4) =
      packedRow ((factorRows 3).get k) w10Rows from by
      simp only [packedRow, factorRows, get_ofFn]
      decide +kernel) ⟨k, hk⟩

theorem conjugate_product_5 :
    packedMul w14Rows (factorRows 5) = packedMul (factorRows 4) w14Rows := by
  apply Vector.ext
  intro k hk
  change (packedMul w14Rows (factorRows 5)).get ⟨k, hk⟩ =
    (packedMul (factorRows 4) w14Rows).get ⟨k, hk⟩
  simp only [packedMul, get_ofFn]
  exact (show ∀ k : Fin 112,
    packedRow (w14Rows.get k) (factorRows 5) =
      packedRow ((factorRows 4).get k) w14Rows from by
      simp only [packedRow, factorRows, get_ofFn]
      decide +kernel) ⟨k, hk⟩


end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.KernelSeparation
