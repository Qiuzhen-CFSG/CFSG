module

public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.LocalRankSieve.Classical
public import Theory.Alternating.TripleSixLocalRank
public import Theory.Alternating.TripleSevenLocalRank
public import Theory.Mathieu.M22.TripleCoverLocalRank

/-!+# The full cubic-cover local-rank sieve

Every model in the actual three-cover list is considered. The alternating and
Mathieu covers contain an actual two-local of cubic rank at least two; the
classical calculation leaves precisely the odd-degree binary unitary models.
Thus a local-rank bound of one supplies the literal unitary identification
needed in the central-product exception of Theorem A.

Source: Aschbacher–Smith A.2.12(I.i), printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
open Chapter1.Section02.LocalModels

theorem unitary_model_of_threeCover_local_rank_le_one
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (hm : ThreeCoverModel L) (hz : Nat.card (center L) = 3)
    (hl : twoLocalPrimeRank 3 L ≤ 1) :
    ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧ IsSpecialUnitaryModel L 3 (2 ^ n) := by
  cases hm with
  | classical unitary q hq iso =>
      exact LocalRankSieve.classical_of_local_rank_le_one unitary q hq iso hz hl
  | alternating_six iso =>
      obtain ⟨e⟩ := iso.2.2
      have := GLS3.Chapter5.OddCentralCovers.triple_six_twoLocalThreeRank_ge_two e hz
      omega
  | alternating_seven iso =>
      obtain ⟨e⟩ := iso.2.2
      have := GLS3.Chapter5.OddCentralCovers.triple_seven_twoLocalThreeRank_ge_two e hz
      omega
  | mathieu iso =>
      obtain ⟨e⟩ := iso.2.2
      have := Sporadic.Mathieu.triple_cover_twoLocalThreeRank_ge_two e hz
      omega

end CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
