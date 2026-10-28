module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels

/-!
# A quasisimple binary linear-two group has a larger defining field

The degree-one field gives SL₂(2) ≅ S₃, which is solvable. A quasisimple group
is nontrivial and perfect, so this case is impossible. The defining binary
field therefore has at least four elements. This discharges the size premise
in the single natural Borel exclusion in Aschbacher–Smith3.1.9(5), p.578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource

theorem quasisimple_linear_two_card_ge_four {A : Type*} [Group A] [IsQuasisimple A]
    (F : BinaryField) (e : A ≃* SL(2,F.Carrier)) : 4 ≤ Nat.card F.Carrier := by
  have hd : F.degree ≠ 1 := by
    intro hd
    let e₃ := e.trans ((ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
      ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
        BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      apply Group.isSolvable_of_ker_le_range
        (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Nontrivial A := Function.Injective.nontrivial e₃.symm.injective
    exact Group.IsPerfect.not_isSolvable A
      (Group.isSolvable_of_isSolvable_injective (f := e₃.toMonoidHom) e₃.injective)
  have hn : 2 ≤ F.degree := by have := F.degree_pos; omega
  rw [F.card_eq]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
end CFSG.Quasithin.ChapterB.QuasisimpleSource
