module
public import Theory.GroupTheory.Amalgam.AutomorphismGroup

/-!
# Transport of compatible amalgam automorphisms

Conjugating all three component maps by a fixed marked amalgam isomorphism
transports the compatible automorphism group.  This is the reusable interface
for moving a finite automorphism bound between a concrete marked pair and a
source pair.
-/

@[expose] public section
namespace Theory.GroupTheory.RankTwoAmalgam

def automorphismConjEquiv {L B R L' B' R' : Type*}
    [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (e : RankTwoAmalgam.Iso α β) :
    RankTwoAmalgam.Iso α α ≃* RankTwoAmalgam.Iso β β where
  toFun a := (e.symm.trans a).trans e
  invFun b := (e.trans b).trans e.symm
  left_inv a := by
    apply RankTwoAmalgam.Iso.ext
    all_goals
      apply MulEquiv.ext
      intro x
      simp only [RankTwoAmalgam.Iso.trans, RankTwoAmalgam.Iso.symm,
        RankTwoAmalgam.ParabolicEquiv.trans, RankTwoAmalgam.ParabolicEquiv.symm,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  right_inv b := by
    apply RankTwoAmalgam.Iso.ext
    all_goals
      apply MulEquiv.ext
      intro x
      simp only [RankTwoAmalgam.Iso.trans, RankTwoAmalgam.Iso.symm,
        RankTwoAmalgam.ParabolicEquiv.trans, RankTwoAmalgam.ParabolicEquiv.symm,
        MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  map_mul' a b := by
    apply RankTwoAmalgam.Iso.ext
    all_goals
      apply MulEquiv.ext
      intro x
      simp only [RankTwoAmalgam.Iso.mul_left, RankTwoAmalgam.Iso.mul_middle,
        RankTwoAmalgam.Iso.mul_right, RankTwoAmalgam.Iso.trans, RankTwoAmalgam.Iso.symm,
        RankTwoAmalgam.ParabolicEquiv.trans, RankTwoAmalgam.ParabolicEquiv.symm,
        MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.symm_apply_apply]

end Theory.GroupTheory.RankTwoAmalgam
