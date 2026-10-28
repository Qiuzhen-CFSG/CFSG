module
public import Theory.GroupTheory.Amalgam.SymmetricFourPair
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.BinaryLinear
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores

/-!
# Rigidity of the binary linear flag amalgam

The actual point and line stabilizers in PSL₃(2) are S₄ and their full overlap
is a Sylow D₈. The trivial ambient two-core supplies faithfulness. The square
pair calculation therefore identifies this literal matrix model with every
faithful S₄--D₈--S₄ amalgam, preserving both overlap embeddings.

Source: Aschbacher–Smith F.1.12(I)(1), binary case, printed p.262.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.BinaryLinear
open Subgroup Theory.GroupTheory RankTwoAmalgam Matrix.PSL3Two

theorem sylow_embedded : SylowEmbedded 2 amalgam :=
  sylowEmbedded_ofSubgroups borelSylow _ _ _ borel_le_point borel_le_line rfl

theorem faithful : Faithful amalgam := by
  apply faithful_ofSubgroups_of_completion _ _ _ _ _ parabolics_generate
  intro N hn hN
  have hp := borelSylow.isPGroup'.to_le hN
  apply le_bot_iff.mp
  rw [←pCore_two_PSL_eq_bot]
  exact le_sSup ⟨hn,hp⟩

private theorem middle_dihedral : Nonempty (borel≃*DihedralGroup 4) := by
  obtain ⟨P,hP⟩ := sylow_embedded.left_sylow
  obtain ⟨f,u,hu⟩ := exists_normalized_endpoint amalgam.left MixedEight.square
    left_injective MixedEight.square_injective P hP MixedEight.squareSylow rfl pointParabolicEquivS4
  exact ⟨u⟩

/-- The concrete PSL₃(2) inclusion pair agrees with the explicit square pair. -/
theorem iso_symmetricFourPair : Nonempty (Iso amalgam SymmetricFourPair.amalgam) := by
  obtain ⟨eB⟩ := middle_dihedral
  exact SymmetricFourPair.iso_of_parabolic_equiv amalgam left_injective right_injective faithful
    pointParabolicEquivS4 eB lineParabolicEquivS4

/-- An arbitrary faithful pair with the three binary linear local groups is
isomorphic to the actual binary linear flag amalgam, including both maps. -/
theorem iso_of_faithful_symmetric_four_pair
    {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R) (hi : Function.Injective α.left)
    (hj : Function.Injective α.right) (hf : Faithful α)
    (eL : L≃*Equiv.Perm (Fin 4)) (eB : B≃*DihedralGroup 4)
    (eR : R≃*Equiv.Perm (Fin 4)) : Nonempty (Iso α amalgam) := by
  obtain ⟨e⟩ := SymmetricFourPair.iso_of_parabolic_equiv α hi hj hf eL eB eR
  obtain ⟨f⟩ := iso_symmetricFourPair
  exact ⟨e.trans f.symm⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.BinaryLinear
