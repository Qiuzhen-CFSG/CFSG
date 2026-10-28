module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices.Certificate

/-!
# Small certificates for the large-prime displacement bound

An identity minor in a checked row combination certifies a lower bound on
matrix rank. Only 101 independent rows are required to rule out the product
of two conjugates of the standard J₄ involution, whose displacement rank is 50.
The packed convention and ATLAS attribution are in `Janko4.Model.Data`.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.LargePrimeRanks
open Janko4 Janko4.GeneratorCertificates
open Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.RepresentativeMatrices

theorem rank_ge_certificate {r : ℕ} (rows : Vector ℕ 112) (basis : Fin r → ℕ)
    (fromRows : Fin r → ℕ) (pivots : Fin r → Fin 112)
    (he : ∀ i, combine rows.get (fromRows i) = basis i)
    (hp : ∀ i j, bit (basis i) (pivots j).val = if i = j then 1 else 0) :
    r ≤ (decodeRows rows).rank := by
  let E : Matrix (Fin r) (Fin 112) (ZMod 2) := decode basis
  have he' : E = decode fromRows * decodeRows rows := by
    change decode basis = decode fromRows * decode rows.get
    rw [← decode_combine]
    exact congrArg decode (funext fun i => (he i).symm)
  have hp' : E.submatrix id pivots = 1 := by
    funext i j
    exact (hp i j).trans (Matrix.one_apply (i := i) (j := j)).symm
  calc
    r = (1 : Matrix (Fin r) (Fin r) (ZMod 2)).rank := by simp
    _ = (E.submatrix id pivots).rank := by rw [hp']
    _ ≤ E.rank := Matrix.rank_submatrix_le _ _ _
    _ = (decode fromRows * decodeRows rows).rank := by rw [he']
    _ ≤ (decodeRows rows).rank := Matrix.rank_mul_le_right _ _

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.LargePrimeRanks
