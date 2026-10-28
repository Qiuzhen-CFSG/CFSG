module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.Blocks

/-! Closed binary arithmetic for the scalar certificate. The direction products
are checked in four blocks to limit kernel memory. The resulting row products,
Gram matrix, and linear coefficients are interpreted in Directions.
Source and witness conventions: ScalarCertificate/source/README.md. -/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate

private instance finForall {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) := Nat.decidableForallFin P

private theorem first_j_block0 : ∀ t : Fin 31,
    let k : Fin 124 := ⟨t.val, by omega⟩;
    ∀ i : Fin 50,
    rowProduct (jRows.get i) (rows (m := 50) (n := 50) (affineDirectionRows.get k)) =
      (rows (m := 50) (n := 50) (firstFactorsJ.get k)).get i := by
  dsimp only
  simp only [rowProduct, rows, get_ofFn]
  decide +kernel


private theorem first_j_block1 : ∀ t : Fin 31,
    let k : Fin 124 := ⟨31 + t.val, by omega⟩;
    ∀ i : Fin 50,
    rowProduct (jRows.get i) (rows (m := 50) (n := 50) (affineDirectionRows.get k)) =
      (rows (m := 50) (n := 50) (firstFactorsJ.get k)).get i := by
  dsimp only
  simp only [rowProduct, rows, get_ofFn]
  decide +kernel


private theorem first_j_block2 : ∀ t : Fin 31,
    let k : Fin 124 := ⟨62 + t.val, by omega⟩;
    ∀ i : Fin 50,
    rowProduct (jRows.get i) (rows (m := 50) (n := 50) (affineDirectionRows.get k)) =
      (rows (m := 50) (n := 50) (firstFactorsJ.get k)).get i := by
  dsimp only
  simp only [rowProduct, rows, get_ofFn]
  decide +kernel


private theorem first_j_block3 : ∀ t : Fin 31,
    let k : Fin 124 := ⟨93 + t.val, by omega⟩;
    ∀ i : Fin 50,
    rowProduct (jRows.get i) (rows (m := 50) (n := 50) (affineDirectionRows.get k)) =
      (rows (m := 50) (n := 50) (firstFactorsJ.get k)).get i := by
  dsimp only
  simp only [rowProduct, rows, get_ofFn]
  decide +kernel


theorem first_j_check : ∀ k : Fin 124, ∀ i : Fin 50,
    rowProduct (jRows.get i) (rows (m := 50) (n := 50) (affineDirectionRows.get k)) =
      (rows (m := 50) (n := 50) (firstFactorsJ.get k)).get i :=
  all_direction_blocks first_j_block0 first_j_block1 first_j_block2 first_j_block3



end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
