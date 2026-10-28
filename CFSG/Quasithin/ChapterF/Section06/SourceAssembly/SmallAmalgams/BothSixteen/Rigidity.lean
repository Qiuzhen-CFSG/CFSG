module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.BothSixteen.Vertices
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour.BinaryRigidity

/-!
# The original order-sixteen Goldschmidt pair is the binary symplectic pair

The original core-free pair with two characteristic-two vertices supplies its
individual vertex and overlap models. Faithfulness then forces their compatible
Sp₄(2) marking. Both inclusion maps of the original common Sylow are retained;
no model recognition premise is introduced.

Source: Aschbacher–Smith F.1.12(I)(2) and F.6.5, printed pp.262,305.
-/

public section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.BothSixteen
open Subgroup Theory.GroupTheory RankTwoAmalgam
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

/-- The actual two vertices and their original overlap embeddings form the
binary symplectic flag amalgam. -/
theorem symplectic_four_amalgam (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (hT : Nat.card (A⊓B : Subgroup G)=16) :
    Nonempty (Iso (ofSubgroups A (A⊓B) B inf_le_left inf_le_right)
      (GreenBook.LieModels.SymplecticFour.amalgam (ZMod 2))) := by
  obtain ⟨eA⟩ := left_vertex h hcore hA hB hT
  obtain ⟨eB⟩ := left_vertex h.symm hcore hB hA (by simpa only [inf_comm B A] using hT)
  obtain ⟨eT⟩ := common_sylow_split h hcore hA hB hT
  let eZ : Multiplicative (ZMod 2)≃*ℤˣ := mulEquivOfPrimeCardEq (p := 2)
    (by simp [Nat.card_eq_fintype_card]) (by rw [Nat.card_eq_fintype_card];decide)
  exact GreenBook.LieModels.SymplecticFour.BinaryRigidity.iso_of_faithful_split_symmetric_four_pair
    (ofSubgroups A (A⊓B) B inf_le_left inf_le_right)
    (inclusion_injective inf_le_left) (inclusion_injective inf_le_right) (h.amalgam_faithful hcore)
    (eA.trans (MulEquiv.prodCongr eZ (MulEquiv.refl _)))
    (eT.trans (MulEquiv.prodCongr eZ (MulEquiv.refl _)))
    (eB.trans (MulEquiv.prodCongr eZ (MulEquiv.refl _)))

end CFSG.Quasithin.ChapterF.SourceAssembly.BothSixteen
