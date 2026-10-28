module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
/-!
# The field size of a perfect natural rank-one actor

A nontrivial perfect group acting as the full natural SL₂ group over a binary
field cannot be defined over the two-element field: that group is S₃ and is
solvable. This is the field-size step in the rank-one branch of B.6.9.
-/
public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
theorem perfect_linear_two_field_large {A : Type*} [Group A] [Group.IsPerfect A]
    [Nontrivial A] (F : BinaryField) (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    2 < Nat.card F.Carrier := by
  by_contra hn
  have hd : F.degree = 1 := by
    have hdpos := F.degree_pos
    have hn' : 2^F.degree ≤ 2 := by simpa only [F.card_eq] using Nat.le_of_not_gt hn
    by_contra h
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ F.degree by omega)
    norm_num at hpow
    omega
  let c := e.trans ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
    ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  exact Group.IsPerfect.not_isSolvable A
    (Group.isSolvable_of_surjective (f := c.symm.toMonoidHom) c.symm.surjective)

end CFSG.Quasithin.ChapterB.QuasisimpleSource
