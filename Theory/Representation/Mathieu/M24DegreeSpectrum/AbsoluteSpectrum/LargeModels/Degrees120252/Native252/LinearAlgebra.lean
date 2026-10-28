module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Certificate

/-!
# Decoding the sextet embedding certificates

A left inverse to the selected 252-row submatrix proves injectivity of the
full 1771-row embedding. The packed row traversal decodes into exactly the
forward-index generator identity used by the native permutation transport.
These implications retain the finite equalities as explicit premises.

Source: the saved sextet construction in `Degrees120252/source/README.md`;
James, J. Algebra 27 (1973), 57–111; GM02, Proposition 5.1.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks

theorem embedding_injective_of_inverse
    (hs : ∀ i k, embeddingMatrix (selectedIndex i) k = selectedMatrix i k)
    (hi : inverseMatrix * selectedMatrix = 1) : Function.Injective embedding := by
  intro v w h
  have he : selectedMatrix.mulVec v = selectedMatrix.mulVec w := by
    funext i
    have ht := congrFun h (selectedIndex i)
    change (∑ k, embeddingMatrix (selectedIndex i) k * v k) =
      ∑ k, embeddingMatrix (selectedIndex i) k * w k at ht
    change (∑ k, selectedMatrix i k * v k) = ∑ k, selectedMatrix i k * w k
    simpa only [hs] using ht
  have ht := congrArg inverseMatrix.mulVec he
  simpa only [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec] using ht

theorem intertwining_of_rows
    (hlen : ∀ j, (rows252 j).length = 252)
    (h : ∀ j i, combineList (rows252 j) (entry covectorRows (forward j i).val) =
      entry covectorRows i.val) :
    ∀ j i k, (embeddingMatrix * matrix252 j) (forward j i) k = embeddingMatrix i k := by
  intro j i k
  have ht := congrArg (fun n => bit n k.val) (h j i)
  rw [bit_combineList (rows252 j) 252 (hlen j)] at ht
  change (∑ l : Fin 252, bit (entry covectorRows (forward j i).val) l.val *
    bit (entry (rows252 j) l.val) k.val) = bit (entry covectorRows i.val) k.val
  simpa only [mul_comm, entry] using ht

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252
