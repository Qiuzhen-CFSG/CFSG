module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.Words
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.ComparisonMap
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.FiniteRelations
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.AmbientRelations.FullMatrixComparison

/-!
# Transport of the certified 52-dimensional word identities

The tabulated binary matrices satisfy the A₅ Coxeter relations and all four
generator-recovery identities. The complete coordinate bijection identifies
these tables with the actual Geck root matrices. Transport through this
bijection proves the identities in the split Levi: its map to the ambient
matrix units forgets only subgroup proofs.

The two unconditional ambient identities discharge the word-relation premises
of the full-Levi four-space kernel reduction.

Source context: Aschbacher–Smith F.1.12(I)(5), printed pp.263–264
(PDF pp.274–275) of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof
open Theory.AlgebraicGroup AmbientComputation

private def ambientMatrix : splitLevi →*
    Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex (CoefficientField 0) :=
  (Units.coeHom _).comp ambientLeviHom

private theorem ambientMatrix_injective : Function.Injective ambientMatrix :=
  Units.val_injective.comp ambientLeviHom_injective

private theorem ambientChain_matrix (e : Fin 52 ≃ F4Chevalley.BasisIndex)
    (hgen : ∀ i : Fin 4, (ambientLeviHom (splitGenerator i)).val =
      fullMatrixMap e (generator i)) (i : Fin 5) :
    ambientMatrix (ambientChain i) = fullMatrixMap e (chain i) := by
  rw [← chain_word]
  change ambientMatrix (((chainWord i).map splitGenerator).prod) = _
  simp only [map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro j _
  exact hgen j

/-- Full generator comparisons transfer all the certified Coxeter equations
from the 52-dimensional tables to the actual split Levi. -/
theorem ambientChain_liftable_of_fullMatrixComparison
    (e : Fin 52 ≃ F4Chevalley.BasisIndex)
    (hgen : ∀ i : Fin 4, (ambientLeviHom (splitGenerator i)).val =
      fullMatrixMap e (generator i)) :
    (CoxeterMatrix.A 5).IsLiftable ambientChain := by
  intro i j
  apply ambientMatrix_injective
  rw [map_pow, map_mul, ambientChain_matrix e hgen, ambientChain_matrix e hgen,
    ← map_mul, ← map_pow, chain_liftable i j, map_one, map_one]

/-- Full generator comparisons also transfer the certified recovery words. -/
theorem ambientChain_recovery_of_fullMatrixComparison
    (e : Fin 52 ≃ F4Chevalley.BasisIndex)
    (hgen : ∀ i : Fin 4, (ambientLeviHom (splitGenerator i)).val =
      fullMatrixMap e (generator i)) (i : Fin 4) :
    ((recoveryWord i).map ambientChain).prod = splitGenerator i := by
  apply ambientMatrix_injective
  calc
    ambientMatrix (((recoveryWord i).map ambientChain).prod) =
        fullMatrixMap e (((recoveryWord i).map chain).prod) := by
      simp only [map_list_prod, List.map_map, Function.comp_def,
        ambientChain_matrix e hgen]
    _ = fullMatrixMap e (generator i) := congrArg (fullMatrixMap e) (chain_recovery i)
    _ = ambientMatrix (splitGenerator i) := (hgen i).symm

/-- The five explicit words satisfy the A₅ Coxeter relations in the actual
binary F₄ Levi. -/
theorem ambientChain_liftable : (CoxeterMatrix.A 5).IsLiftable ambientChain :=
  ambientChain_liftable_of_fullMatrixComparison basisEquiv
    ambientGenerator_fullMatrixComparison

/-- The published recovery words recover every signed middle-root generator
in the actual binary F₄ Levi. -/
theorem ambientChain_recovery (i : Fin 4) :
    ((recoveryWord i).map ambientChain).prod = splitGenerator i :=
  ambientChain_recovery_of_fullMatrixComparison basisEquiv
    ambientGenerator_fullMatrixComparison i

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof
