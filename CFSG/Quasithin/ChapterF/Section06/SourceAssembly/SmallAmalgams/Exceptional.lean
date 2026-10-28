module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedSixteen
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# All five exceptional Goldschmidt amalgams

A failure of local characteristic two gives exactly the five concrete
exceptional rows, with compatible isomorphisms and with vertex interchange
allowed. Both bad vertices give the first two rows; a mixed pair gives
the other three. The final theorem keeps the original intrinsic quotient
maps and the whole quotient of the overlap.

Source: Aschbacher–Smith F.6.5(2)(i–v), printed p.305. The six weak BN-pair
rows are a separate source branch.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF

/-- The five explicit exceptional rows of the source table. -/
def ExceptionalAmalgam {L B R : Type*} [Group L] [Group B] [Group R]
    (α : RankTwoAmalgam L B R) : Prop :=
  Nonempty (RankTwoAmalgam.Iso α symmetricThreePair) ∨
  Nonempty (RankTwoAmalgam.Iso α dihedralTwelvePair) ∨
  Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.reflectionCharacter)) ∨
  Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.rotationCharacter)) ∨
  Nonempty (RankTwoAmalgam.Iso α MixedSixteen.standard)

theorem ExceptionalAmalgam.of_iso
    {L B R L' B' R' : Type*} [Group L] [Group B] [Group R]
    [Group L'] [Group B'] [Group R']
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (h : ExceptionalAmalgam β) (e : RankTwoAmalgam.Iso α β) : ExceptionalAmalgam α := by
  rcases h with h | h | h | h | h
  · exact Or.inl ⟨e.trans h.some⟩
  · exact Or.inr (Or.inl ⟨e.trans h.some⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans h.some⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans h.some⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans h.some⟩)))

variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- Exhaustion of the exceptional branch, including compatible vertex interchange. -/
theorem IsGoldschmidtTriple.exceptional_amalgam_cases
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁ ∨ generalizedFitting G₂ ≠ pCore 2 G₂) :
    let α := RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    ExceptionalAmalgam α ∨ ExceptionalAmalgam α.reverse := by
  by_cases hgood₁ : generalizedFitting G₁ = pCore 2 G₁
  · have hb₂ : generalizedFitting G₂ ≠ pCore 2 G₂ := hbad.resolve_left (not_not.mpr hgood₁)
    exact Or.inl (Or.inr (Or.inr (h.mixed_cases hcore hgood₁ hb₂)))
  · by_cases hgood₂ : generalizedFitting G₂ = pCore 2 G₂
    · let e : RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right).reverse
          (RankTwoAmalgam.ofSubgroups G₂ (G₂ ⊓ G₁) G₁ inf_le_left inf_le_right) := {
        left := MulEquiv.refl _
        middle := MulEquiv.subgroupCongr (inf_comm G₁ G₂)
        right := MulEquiv.refl _
        left_commutes := fun _ => rfl
        right_commutes := fun _ => rfl }
      have hh : ExceptionalAmalgam
          (RankTwoAmalgam.ofSubgroups G₂ (G₂ ⊓ G₁) G₁ inf_le_left inf_le_right) :=
        Or.inr (Or.inr (h.symm.mixed_cases hcore hgood₂ hgood₁))
      exact Or.inr (hh.of_iso e)
    · rcases h.first_two_cases_of_neither_characteristic_two hcore hgood₁ hgood₂ with hh | hh
      · exact Or.inl (Or.inl hh)
      · exact Or.inl (Or.inr (Or.inl hh))

/-- Exceptional recognition on the actual images in the literal ambient quotient. -/
theorem IsGoldschmidtTriple.quotient_exceptional_amalgam_cases
    (h : IsGoldschmidtTriple G₁ G₂)
    (hbad : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) ≠
        pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))) ∨
      generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) ≠
        pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G)))) :
    let q := QuotientGroup.mk' (pCore 2 G)
    let α := RankTwoAmalgam.ofSubgroups (G₁.map q) (G₁.map q ⊓ G₂.map q)
      (G₂.map q) inf_le_left inf_le_right
    ExceptionalAmalgam α ∨ ExceptionalAmalgam α.reverse :=
  h.quotient_twoCore.exceptional_amalgam_cases h.quotient_twoCore_eq_bot hbad

/-- Exceptional recognition retains all three original intrinsic quotient maps. -/
theorem IsGoldschmidtTriple.intrinsic_quotient_exceptional_amalgam_cases
    (h : IsGoldschmidtTriple G₁ G₂)
    (hbad : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) ≠
        pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))) ∨
      generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) ≠
        pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G)))) :
    let α := RankTwoAmalgam.ofSubgroupQuotients (QuotientGroup.mk' (pCore 2 G))
      G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    ExceptionalAmalgam α ∨ ExceptionalAmalgam α.reverse := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let eMiddle : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (G₁.map q) ((G₁ ⊓ G₂).map q)
        (G₂.map q) (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right))
      (RankTwoAmalgam.ofSubgroups (G₁.map q) (G₁.map q ⊓ G₂.map q)
        (G₂.map q) inf_le_left inf_le_right) := {
    left := MulEquiv.refl _
    middle := MulEquiv.subgroupCongr h.quotient_twoCore_intersection
    right := MulEquiv.refl _
    left_commutes := fun _ => rfl
    right_commutes := fun _ => rfl }
  let e0 := h.quotientTwoCoreAmalgamIso.trans eMiddle
  rcases h.quotient_exceptional_amalgam_cases hbad with hh | hh
  · exact Or.inl (hh.of_iso e0)
  · exact Or.inr (hh.of_iso e0.reverse)

end CFSG.Quasithin.ChapterF
