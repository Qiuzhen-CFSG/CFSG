module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.AlternatingSevenLocals
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.OddCentralCover
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# The compatible row-seven amalgam in odd central covers of A₇

Two characteristic-two vertices would both be S₄ and cannot generate the
central cover. Two other vertices force an overlap of order at most four.
The mixed case has two compatible models; the dihedral vertex in the
reflection model is excluded by its order-twelve rotation. The remaining
rotation model is exactly row (iv), with both original inclusion squares
retained, allowing interchange of the vertices.

Source: Aschbacher--Smith F.6.18(7), printed p.310, and F.6.5(2)(iv), p.305.
-/

public section
open Subgroup Equiv Theory.GroupTheory Theory.GroupTheory.RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem mixed_rotation_of_alternatingSeven_central_quotient
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (eQ : (G ⧸ center G) ≃* alternatingGroup (Fin 7))
    (hZ : Odd (Nat.card (center G))) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      (MixedEight.amalgam MixedEight.rotationCharacter)) := by
  rcases h.mixed_eight_cases hcore hgood hbad hT with he | he
  · obtain ⟨e⟩ := he
    exact (AlternatingSeven.DihedralLocals.not_dihedralTwentyFour_subgroup_of_odd_center
      eQ hZ G₂ (e.right.trans MixedEight.reflectionVertexEquiv)).elim
  · exact he

/-- The original A₇ or triple-A₇ local amalgam is row (iv), up to swapping
its vertices. The conclusion includes the two commuting inclusion squares. -/
theorem alternatingSeven_row_seven_amalgam
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8)
    (eQ : (G ⧸ center G) ≃* alternatingGroup (Fin 7))
    (hZ : Odd (Nat.card (center G))) :
    let α := RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.rotationCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α.reverse
        (MixedEight.amalgam MixedEight.rotationCharacter)) := by
  classical
  have hT' : Nat.card (G₂ ⊓ G₁ : Subgroup G) = 8 := by simpa only [inf_comm] using hT
  by_cases h₁ : generalizedFitting G₁ = pCore 2 G₁
  · by_cases h₂ : generalizedFitting G₂ = pCore 2 G₂
    · obtain ⟨e₁⟩ := h.local_equiv_symmetric_four_of_intersection_card_eight h₁ hT
      obtain ⟨e₂⟩ := h.symm.local_equiv_symmetric_four_of_intersection_card_eight h₂ hT'
      exact (not_alternatingSeven_central_quotient_symmetricFour_pair h eQ e₁ e₂).elim
    · exact Or.inl (mixed_rotation_of_alternatingSeven_central_quotient h hcore h₁ h₂ hT eQ hZ)
  · by_cases h₂ : generalizedFitting G₂ = pCore 2 G₂
    · obtain ⟨e⟩ := mixed_rotation_of_alternatingSeven_central_quotient h.symm hcore h₂ h₁ hT' eQ hZ
      let swap : RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right).reverse
          (RankTwoAmalgam.ofSubgroups G₂ (G₂ ⊓ G₁) G₁ inf_le_left inf_le_right) := {
        left := MulEquiv.refl _
        middle := MulEquiv.subgroupCongr (inf_comm G₁ G₂)
        right := MulEquiv.refl _
        left_commutes := fun _ => rfl
        right_commutes := fun _ => rfl }
      exact Or.inr ⟨swap.trans e⟩
    · have hsmall := h.intersection_card_of_neither_characteristic_two hcore h₁ h₂
      omega

end CFSG.Quasithin.ChapterF.SourceAssembly
