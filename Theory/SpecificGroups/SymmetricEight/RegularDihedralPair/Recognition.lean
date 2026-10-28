module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.Order168Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168

/-! Identify the concrete subgroup through the faithful PSL₂(7) action. -/

@[expose] public section
open Equiv Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
open Atlas.Comparisons.Exceptional

def sevenMarking : P8 where
  toFun := ![0,1,2,7,4,3,6,5]
  invFun := ![0,1,2,5,4,7,6,3]
  left_inv := by decide
  right_inv := by decide

private def sevenWords : Fin 4 → List (Fin 2) :=
  ![[0,0,0,1,0,0,1,0,0,0,1],[0,1,0,0,0,1,0,0,1],[0,0,0,0,0,1,0,0,0],[0,0,0,1,0,0,0,0,0]]

private theorem seven_generator_words (i : Fin 4) :
    (MulAut.conj sevenMarking) (modelGenerators i) =
      eval ![Seven.translation, Seven.inversion] (sevenWords i) := by
  decide +revert +kernel

private theorem model_map_seven :
    modelGroup.map (MulAut.conj sevenMarking).toMonoidHom = Seven.permutation.range := by
  have hle : modelGroup.map (MulAut.conj sevenMarking).toMonoidHom ≤
      Seven.permutation.range := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change (MulAut.conj sevenMarking) (modelGenerators i) ∈ Seven.permutation.range
    rw [seven_generator_words]
    apply eval_mem
    intro j
    fin_cases j
    · exact ⟨_, Seven.permutation_upper⟩
    · exact ⟨_, Seven.permutation_inversion⟩
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective (MulAut.conj sevenMarking).injective, model_card]
  have hc : Nat.card Seven.permutation.range = 168 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective Seven.permutation_injective).toEquiv]
    exact psl2Seven_card
  exact hc.le

/-- The actual eight-point representations identify the two matrix groups. -/
noncomputable def modelEquivPsl3 : modelGroup ≃* PSL(3, ZMod 2) :=
  (modelGroup.equivMapOfInjective (MulAut.conj sevenMarking).toMonoidHom
    (MulAut.conj sevenMarking).injective).trans
    ((MulEquiv.subgroupCongr (by exact model_map_seven)).trans
      ((MonoidHom.ofInjective Seven.permutation_injective).symm.trans psl2SevenEquivPsl3Two))

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
