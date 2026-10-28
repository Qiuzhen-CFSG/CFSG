module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Centralizer.CommutantFlag.Basis
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Centralizer.CommutantFlag.Words
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Centralizer.CommutantFlag.RowReconstruction

/-!
# Assembly of the third-commutator commutant flag for J₄

The fixed unit B has a kernel-checked inverse, and the ten literal triple
commutators belong to the actual subgroup D = [T,[T,T]]. Two independent
finite certificates remain: their matrices in the B basis, and triangularity
of the common matrix commutant of the explicit ten decoded matrices.
The theorem below transfers these certificates to the exact ambient flag
contract. It does not assert either missing numerical certificate.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`). This is the matrix route to the
centralizer bound used in `QuotientExclusion.Centralizer.Reduction`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

private theorem conjugate_commute (X Y : Janko4.BinaryMatrix) (h : Commute X Y) :
    Commute
      ((ThirdFlag.basisUnit : Janko4.BinaryMatrix) * X * (↑ThirdFlag.basisUnit⁻¹ : Janko4.BinaryMatrix))
      ((ThirdFlag.basisUnit : Janko4.BinaryMatrix) * Y * (↑ThirdFlag.basisUnit⁻¹ : Janko4.BinaryMatrix)) := by
  change _ * _ = _ * _
  simpa only [mul_assoc, Units.inv_mul_cancel_left] using
    congrArg (fun A : Janko4.BinaryMatrix =>
      (ThirdFlag.basisUnit : Janko4.BinaryMatrix) * A *
        (↑ThirdFlag.basisUnit⁻¹ : Janko4.BinaryMatrix)) h.eq

/-- The two independent finite certificates suffice for the actual D-commutant flag. -/
theorem fixedTwoThirdCommutantFlag_of_certificates
    (hwords : ∀ a : Fin 10,
      (ThirdFlag.basisUnit : Janko4.BinaryMatrix) * Janko4.toMatrix (ThirdFlag.tripleWord a) *
        (↑ThirdFlag.basisUnit⁻¹ : Janko4.BinaryMatrix) = ThirdFlag.tripleMatrix a)
    (hlinear : ∀ M : Janko4.BinaryMatrix,
      (∀ a : Fin 10, Commute M (ThirdFlag.tripleMatrix a)) → M.IsLowerTriangular) :
    FixedTwoThirdCommutantFlag := by
  refine ⟨ThirdFlag.basisUnit, fun M hM => hlinear _ ?_⟩
  intro a
  rw [← hwords a]
  exact conjugate_commute M _ (hM _ (ThirdFlag.tripleWord_mem a))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
