module

public import Theory.SpecificGroups.Janko4.Model.TwoRank.Reduction
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite

/-!
# Two-rank bounds for the actual J₄ carrier and its automorphisms

The checked elementary fixed-mask inequality bounds elementary subgroups of
the actual max1 Sylow group by 2¹¹. The Sylow reduction then bounds the
repository's prime rank on the binary ATLAS carrier. Full innerness identifies
its automorphism group with the model under the inherited simple and perfect
hypotheses. No finite-action or local-structure premise remains.

These are the upper bounds needed in the discarded J₄ case of Aschbacher–Smith
G.7.3(2), printed pp.347–348 (PDF pp.358–359), which cites Asc82a and
GLS98 5.2.10/5.6.1. The literal quotient alignment and direct eleven-coordinate
action are retained by `TwoRank.Reduction` and `TwoRank.Finite`.
-/

public section
namespace Janko4.TwoRank
open Subgroup Theory.GroupTheory
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] modelGroup matrixA matrixB

/-- The actual binary ATLAS carrier has two-rank at most eleven. -/
theorem model_twoRank_le_eleven : primeRank 2 Model ≤ 11 :=
  model_twoRank_le_eleven_of_fixedBound elementaryFixedBound

/-- Full innerness transfers the bound to all automorphisms of the model. -/
theorem automorphism_twoRank_le_eleven
    [IsSimpleGroup Model] [Group.IsPerfect Model] :
    primeRank 2 (MulAut Model) ≤ 11 := by
  let e : Model ≃* MulAut Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect,
      AdequateLocal.conj_surjective⟩
  rw [← primeRank_equiv 2 e]
  exact model_twoRank_le_eleven

end Janko4.TwoRank
