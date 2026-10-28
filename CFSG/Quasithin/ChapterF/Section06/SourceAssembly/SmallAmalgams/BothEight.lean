module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CharacteristicVertex
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.BinaryLinear.Rigidity

/-!
# The smallest characteristic-two Goldschmidt pair

When the common Sylow group has order eight, both characteristic-two vertices
are S₄. Their literal inclusion amalgam is faithful because the ambient two-core
is trivial. The binary linear rigidity theorem supplies a compatible
isomorphism to the actual PSL₃(2) flag amalgam. The second theorem retains the
original overlap image under the quotient G → G/O₂(G).

Source: Aschbacher–Smith F.1.12(I)(1) and F.6.5(2)(vi), printed pp.262,305.
This proves the complete binary linear branch, not the larger enumeration.
-/

public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

/-- The two original characteristic-two vertices over a Sylow group of order
eight form the actual PSL₃(2) amalgam, with both inclusion squares. -/
theorem IsGoldschmidtTriple.binary_linear_amalgam_of_intersection_card_eight
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    (hT : Nat.card (A⊓B : Subgroup G)=8) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups A (A⊓B) B inf_le_left inf_le_right)
      GreenBook.LieModels.BinaryLinear.amalgam) := by
  obtain ⟨eA⟩ := h.local_equiv_symmetric_four_of_intersection_card_eight hA hT
  obtain ⟨eB⟩ := h.symm.local_equiv_symmetric_four_of_intersection_card_eight hB
    (by simpa only [inf_comm B A] using hT)
  obtain ⟨eT⟩ := h.intersection_equiv_dihedral_four_of_characteristic_two hA hT
  exact GreenBook.LieModels.BinaryLinear.iso_of_faithful_symmetric_four_pair _
    (inclusion_injective inf_le_left) (inclusion_injective inf_le_right)
    (h.amalgam_faithful hcore) eA eT eB

/-- Literal quotient-image application of the binary F.1.12 case. -/
theorem IsGoldschmidtTriple.quotient_binary_linear_amalgam_of_intersection_card_eight
    (h : IsGoldschmidtTriple A B)
    (hA : generalizedFitting (A.map (QuotientGroup.mk' (pCore 2 G)))=
      pCore 2 (A.map (QuotientGroup.mk' (pCore 2 G))))
    (hB : generalizedFitting (B.map (QuotientGroup.mk' (pCore 2 G)))=
      pCore 2 (B.map (QuotientGroup.mk' (pCore 2 G))))
    (hT : Nat.card ((A⊓B).map (QuotientGroup.mk' (pCore 2 G)))=8) :
    let q := QuotientGroup.mk' (pCore 2 G)
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (A.map q) ((A⊓B).map q) (B.map q)
        (map_mono inf_le_left) (map_mono inf_le_right))
      GreenBook.LieModels.BinaryLinear.amalgam) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hT' : Nat.card (A.map q⊓B.map q : Subgroup (G⧸pCore 2 G))=8 := by
    rw [←h.quotient_twoCore_intersection]
    exact hT
  obtain ⟨e⟩ := h.quotient_twoCore.binary_linear_amalgam_of_intersection_card_eight
    h.quotient_twoCore_eq_bot hA hB hT'
  let j : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (A.map q) ((A⊓B).map q) (B.map q)
        (map_mono inf_le_left) (map_mono inf_le_right))
      (RankTwoAmalgam.ofSubgroups (A.map q) (A.map q⊓B.map q) (B.map q)
        inf_le_left inf_le_right) := {
    left := MulEquiv.refl _
    middle := MulEquiv.subgroupCongr h.quotient_twoCore_intersection
    right := MulEquiv.refl _
    left_commutes := fun _ => rfl
    right_commutes := fun _ => rfl }
  exact ⟨j.trans e⟩
end CFSG.Quasithin.ChapterF
