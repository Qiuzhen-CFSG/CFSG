module

public import CFSG.Quasithin.ChapterA.Section03.RankThreeSylow
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.SylowCoprimeEquivalence

/-!
# Cyclic centers of projective degree-three Sylow subgroups

The SL₃-to-PSL₃ projection has odd kernel. Its restriction to a Sylow
two-subgroup is injective, and its image is Sylow. An actual Sylow
isomorphism therefore transports the proved cyclic-center theorem from
SL₃ to PSL₃. This concerns Sylow subgroups of PSL₃ itself; it makes no
claim about the center of a Sylow subgroup of an almost-simple overgroup.

Source: Aschbacher–Smith, A.3.21(b), printed p.55, as used in the proof of
1.3.4, printed pp.510–511 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan

/-- Every Sylow two-subgroup of the actual PSL₃(q) has cyclic center. -/
theorem psl3_sylow_center_cyclic (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (S : Sylow 2 PSL(3, ZMod q)) : IsCyclic (center S) := by
  let T : Sylow 2 SL(3, ZMod q) := Classical.choice inferInstance
  let e := Sylow.equivOfSurjectiveCoprime (Matrix.PSL3.projection (ZMod q))
    (Matrix.PSL3.projection_surjective (ZMod q))
    (by rw [Matrix.PSL3.projection_ker]
        exact Nat.coprime_two_left.mpr (Matrix.SL3.odd_card_center (ZMod q))) T S
  let _ := CFSG.Quasithin.ChapterA.Section03.sl3_sylow_center_cyclic q hq T
  exact (centerCongr e).isCyclic.mp inferInstance

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
