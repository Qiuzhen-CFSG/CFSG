module

public import Theory.SpecificGroups.SymplecticSix.Simplicity
public import Theory.SpecificGroups.SymplecticSix.BinaryThreeRank
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Binary simple targets for exceptional parabolic sections

The literal projective carriers Sp₆(2), Ω₈⁺(2), and Ω₆⁻(2) are quasisimple
and have ordinary three-rank greater than two. The imported matrix and
permutation-action proofs establish their simplicity and the rank witnesses.
Here simplicity and noncommutativity give perfectness and trivial center,
hence quasisimplicity and applicability of the semisimple-section induction.

Source: Aschbacher–Smith A.2.15(2), A.2.18, printed pp.37–40, together with
GLS3 §2.6. A map from one of these groups into a Levi subgroup must still be
constructed; the intrinsic facts here imply no exceptional-family embedding.
-/

public section

namespace Theory.SpecificGroups.LieType.BinarySectionTargets
open Subgroup Theory.GroupTheory

private theorem quasisimple_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hn : ¬ IsMulCommutative S) : IsQuasisimple S := by
  have hc : center S = ⊥ :=
    (inferInstance : (center S).Normal).eq_bot_or_eq_top.resolve_right
      (fun h => hn (center_eq_top_iff.mp h))
  have hp : commutator S = ⊤ :=
    (inferInstance : (commutator S).Normal).eq_bot_or_eq_top.resolve_left
      (fun h => hn ((commutator_eq_bot_iff S).mp h))
  exact { toIsPerfect := ⟨hp⟩
          simple := ((QuotientGroup.quotientMulEquivOfEq hc).trans
            QuotientGroup.quotientBot).isSimpleGroup }

theorem symplectic_quasisimple : IsQuasisimple (SymplecticSix.PSp (ZMod 2)) := by
  let := SymplecticSix.isSimpleGroup_binary
  exact quasisimple_of_simple SymplecticSix.not_isMulCommutative_binary

theorem symplectic_rank : 2 < primeRank 3 (SymplecticSix.PSp (ZMod 2)) :=
  lt_of_lt_of_le (by decide) SymplecticSix.BinaryThreeRank.primeRank_three_ge

theorem splitEight_quasisimple :
    IsQuasisimple (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) := by
  let := ClassicalOrthogonal.BinaryEightObstruction.isSimpleGroup
  exact quasisimple_of_simple ClassicalOrthogonal.BinaryEightObstruction.not_isMulCommutative

theorem splitEight_rank : 2 < primeRank 3 (ClassicalOrthogonal.POmegaPlus 4 (ZMod 2)) :=
  ClassicalOrthogonal.BinaryEightObstruction.primeRank_three_gt_two

theorem minusSix_quasisimple : IsQuasisimple (ClassicalGroup.POmegaMinus 3 (ZMod 2)) := by
  let := ClassicalOrthogonal.Minus.BinarySixObstruction.isSimpleGroup
  exact quasisimple_of_simple ClassicalOrthogonal.Minus.BinarySixObstruction.not_isMulCommutative

theorem minusSix_rank : 2 < primeRank 3 (ClassicalGroup.POmegaMinus 3 (ZMod 2)) :=
  ClassicalOrthogonal.Minus.BinarySixObstruction.two_lt_primeRank_three

end Theory.SpecificGroups.LieType.BinarySectionTargets
