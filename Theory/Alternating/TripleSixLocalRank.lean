module

public import Theory.Alternating.OddCentralCovers
public import Theory.Representation.HexacodeAction.LocalThreeRank
public import Theory.Quasithin.LocalRankEmbedding

/-!
# Local cubic rank of every genuine triple cover of A₆

Uniqueness of the perfect triple cover transports the concrete hexacode
normalizer calculation and its absence of order-nine elements to the
original group with its specified central quotient.

Source: Aschbacher–Smith A.2.12(I.i), printed p.36, using GLS3 5.2.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace GLS3.Chapter5.OddCentralCovers
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

theorem triple_six_cube_eq_one_of_ninth
    (e : L ⧸ center L ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center L) = 3) (x : L) (hx : x ^ 9 = 1) : x ^ 3 = 1 := by
  obtain ⟨j⟩ := triple_six_equiv_hexacode e hc
  apply j.injective
  rw [map_pow, map_one]
  exact HexacodeTheta.cube_eq_one_of_ninth (by rw [← map_pow, hx, map_one])

theorem triple_six_twoLocalThreeRank_ge_two
    (e : L ⧸ center L ≃* alternatingGroup (Fin 6))
    (hc : Nat.card (center L) = 3) : 2 ≤ twoLocalPrimeRank 3 L := by
  obtain ⟨j⟩ := triple_six_equiv_hexacode e hc
  exact Representation.Hexacode.LocalThreeRank.hex_even_local_three_rank_ge_two.trans
    (twoLocalPrimeRank_le_of_injective 3 j.symm.toMonoidHom j.symm.injective)

end GLS3.Chapter5.OddCentralCovers
