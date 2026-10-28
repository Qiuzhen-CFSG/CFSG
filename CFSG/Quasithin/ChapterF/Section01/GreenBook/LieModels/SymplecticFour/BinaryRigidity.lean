module
public import Theory.GroupTheory.Amalgam.SplitSymmetricFourPair.Rigidity
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Ambient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Compatible recognition of the binary symplectic flag

The actual point and plane parabolics in Sp₄(2) are C₂×S₄. Their common
flag stabilizer is Sylow of order sixteen, and their generated completion has
trivial two-core via its actual S₆ equivalence. The faithful split symmetric-four
calculation therefore identifies any faithful pair with these local groups
with the original matrix flag amalgam, including both embeddings.

Source: Aschbacher–Smith F.1.12(I)(2), printed p.262.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour
open Subgroup Theory.GroupTheory RankTwoAmalgam Theory.SpecificGroups.SymplecticFour
namespace BinaryRigidity

private def centralEquiv : Equiv.Perm (Fin 2)≃*ℤˣ :=
  mulEquivOfPrimeCardEq (p := 2)
    (by simp [Nat.card_eq_fintype_card,Fintype.card_perm])
    (by rw [Nat.card_eq_fintype_card];decide)

private def leftEquiv : pointParabolic (F := ZMod 2)≃*SplitSymmetricFourPair.L :=
  (Binary.pointParabolicEquivProd (by simp)).trans
    (MulEquiv.prodCongr centralEquiv (MulEquiv.refl _))
private def rightEquiv : planeParabolic (F := ZMod 2)≃*SplitSymmetricFourPair.L :=
  (Binary.planeParabolicEquivProd (by simp)).trans
    (MulEquiv.prodCongr centralEquiv (MulEquiv.refl _))

private def flagSylow : Sylow 2 (Sp (ZMod 2)) := Sylow.ofCard borel (by
  rw [card_borel,Binary.card_sp_two]
  norm_num
  decide +kernel)

/-- The literal two flag inclusions have Sylow image. -/
theorem sylow_embedded : SylowEmbedded 2 (amalgam (ZMod 2)) :=
  sylowEmbedded_ofSubgroups flagSylow _ _ _ inf_le_left inf_le_right rfl

/-- Faithfulness follows in the actual symplectic completion. -/
theorem faithful : Faithful (amalgam (ZMod 2)) := by
  have hcore : pCore 2 (Sp (ZMod 2))=⊥ := by
    have hh := pCore_map_iso 2 Binary.symmetricSixEquiv
    rw [Theory.SpecificGroups.SymmetricSix.s6_twoCore_eq_bot,Subgroup.map_bot] at hh
    exact hh.symm
  apply faithful_ofSubgroups_of_completion _ _ _ _ _ parabolics_sup_eq_top
  intro N hn hN
  apply le_bot_iff.mp
  rw [←hcore]
  exact le_sSup ⟨hn,flagSylow.isPGroup'.to_le hN⟩

private theorem middle_split : Nonempty (borel (F := ZMod 2)≃*SplitSymmetricFourPair.B) := by
  obtain ⟨P,hP⟩ := sylow_embedded.left_sylow
  obtain ⟨_,u,_⟩ := exists_normalized_endpoint (amalgam (ZMod 2)).left MixedSixteen.left
    (left_injective (F := ZMod 2)) MixedSixteen.left_injective P hP
    MixedSixteen.leftSylow rfl leftEquiv
  exact ⟨u⟩

/-- Both binary matrix embeddings agree with the canonical split pair. -/
theorem iso_splitSymmetricFourPair :
    Nonempty (Iso (amalgam (ZMod 2)) SplitSymmetricFourPair.amalgam) := by
  obtain ⟨eB⟩ := middle_split
  exact SplitSymmetricFourPair.iso_of_parabolic_equiv _ left_injective right_injective
    faithful leftEquiv eB rightEquiv

/-- Recognition of the whole marked binary symplectic pair. -/
theorem iso_of_faithful_split_symmetric_four_pair
    {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R) (hi : Function.Injective α.left)
    (hj : Function.Injective α.right) (hf : Faithful α)
    (eL : L≃*SplitSymmetricFourPair.L) (eB : B≃*SplitSymmetricFourPair.B)
    (eR : R≃*SplitSymmetricFourPair.L) : Nonempty (Iso α (amalgam (ZMod 2))) := by
  obtain ⟨e⟩ := SplitSymmetricFourPair.iso_of_parabolic_equiv α hi hj hf eL eB eR
  obtain ⟨f⟩ := iso_splitSymmetricFourPair
  exact ⟨e.trans f.symm⟩

end BinaryRigidity
end CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour
