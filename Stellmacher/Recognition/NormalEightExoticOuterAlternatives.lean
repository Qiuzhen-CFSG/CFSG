module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Stellmacher.Recognition.NormalEightExoticSylowModels
public import Stellmacher.Recognition.HallJankoTrivialSylowAutomizer

/-!
# The nontrivial Sylow automizer alternative in exotic recognition

In the marked central-omega-two configuration, a nontrivial Sylow automizer
gives the Hall–Janko or unitary Sylow model. The marked Hall–Janko model is
excluded by the fusion and transfer theorem. The elementary sixteen excludes
the unitary model, which has only three involutions. Thus the actual consumer
hypotheses contradict either model and imply the required outer alternative.

This assembly uses the lower recognition and exclusion results directly so
that the exotic recognition owner can import it without a dependency cycle.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.3 and 1.5, printed p.386,
and the final paragraph of p.395,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Stellmacher.Recognition.NormalEightExoticOuterAlternatives

open Subgroup

/-- The nontrivial-automizer branch of the marked exotic recognition problem.
The available model exclusions actually contradict these hypotheses. -/
public theorem outer_alternatives
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G) (_hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 →
      orderOf v = 2 → IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16)
    (_hWB : W ≤ B)
    (hnorm : normalizer (S : Set G) ≠
      (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    Nat.card {x : (S : Subgroup G) // orderOf x = 2} ≤ 3 ∨
      ∃ z : G, orderOf z = 2 ∧ ¬ Group.IsSolvable (centralizer ({z} : Set G)) := by
  rcases NormalEightExoticSylowModels.models_of_central_two
      hns hN S hnorm hZ hno W hW hunique hfused B hB with hHall | hUnitary
  · exact (HallJankoTrivialSylowAutomizer.false_of_marked_hallJanko
      hns hN S hHall hZ hno W hW hunique hfused B hB).elim
  · exact (NormalEightExoticSylowModels.not_unitary_of_elementary_sixteen
      B hB hUnitary).elim

end Stellmacher.Recognition.NormalEightExoticOuterAlternatives
