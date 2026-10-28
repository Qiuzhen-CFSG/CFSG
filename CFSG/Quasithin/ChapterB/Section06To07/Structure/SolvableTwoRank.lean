module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import CFSG.Quasithin.ChapterA.Section01.RankActions.OddResidualTwoRank
public import CFSG.Quasithin.Defs

/-!
# Two-rank of a solvable strongly quasithin minimal parabolic

B.6.8 identifies O²(H/O₂(H)) with an odd prime core. Its prime rank is at
most two because odd-prime rank descends through the normal two-kernel.
The small odd-residual action theorem bounds the binary rank of H/O₂(H).
Neither movement of a chosen module nor a nonsolvable classification is used.

Source: Aschbacher--Smith, B.6.8(2), pp.113--114, and 12.2.18, p.801.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {H : Type*} [Group H] [Finite H]

theorem solvable_minimalParabolic_twoCoreQuotient_rank_le_two
    (hH : IsStronglyQuasithin H) (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2 := by
  obtain ⟨p, hp, ho, hR, _⟩ := minimalParabolic_solvable_structure T hP hs
  let : Fact p.Prime := ⟨hp⟩
  apply ChapterA.RankActions.odd_residual_twoRank_le_two ho
    (pCore_quotient_pCore_eq_bot (G := H) 2) hR
  exact (primeRank_subgroup_le p (pCore p (H ⧸ pCore 2 H))).trans
    ((primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
      (hH p hp ho))

end CFSG.Quasithin.ChapterB
