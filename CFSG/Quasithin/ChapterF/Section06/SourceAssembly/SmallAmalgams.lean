module

public import CFSG.Quasithin.ChapterF.Section06.Amalgams.CaseOne
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Quotient
public import Theory.GroupTheory.Amalgam.DihedralTwelvePair.Models

/-!
# Both exceptional vertices in a Goldschmidt amalgam

If both vertices fail characteristic two, their normal cubic residuals
centralize their two-cores. The common normal core is trivial, so the local
cores meet trivially. The common Sylow group has order two or four.
In the four-group case its two quotient coordinates extend across the normal
cubic residuals, giving the compatible `(D₁₂,E₄,D₁₂)` amalgam.

Source: Aschbacher–Smith F.6.5(2)(i–ii), printed p.305.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem local_core_card_two (h : IsGoldschmidtTriple G₁ G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) : Nat.card (pCore 2 G₁) = 2 := by
  let Q := (pCore 2 G₁).map G₁.subtype
  let K := Q.subgroupOf (G₁ ⊓ G₂)
  have hi : K.index = 2 := h.left_core_index
  have hc := K.index_mul_card
  rw [hi, hT] at hc
  have hK : Nat.card K = 2 := by omega
  rw [Nat.card_congr ((pCore 2 G₁).equivMapOfInjective G₁.subtype
    G₁.subtype_injective).toEquiv]
  rw [← Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv]
  exact hK

omit [Finite G] in
private theorem local_quotient_middle_card
    (e : (G₁ ⧸ pCore 2 G₁) ≃* SymmetricThree)
    (T : Subgroup G) (hT : T ≤ G₁)
    (hind : ((pCore 2 G₁).map G₁.subtype).relIndex T = 2) :
    Nat.card ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G₁))).comp
      (inclusion hT)).range = 2 := by
  rw [← index_ker]
  have hk : ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G₁))).comp
      (inclusion hT)).ker = ((pCore 2 G₁).map G₁.subtype).subgroupOf T := by
    ext x
    change e (QuotientGroup.mk' _ (inclusion hT x)) = 1 ↔ _
    rw [← e.map_one, e.injective.eq_iff]
    change (QuotientGroup.mk (inclusion hT x) : G₁ ⧸ pCore 2 G₁) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact ⟨inclusion hT x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      have : y = inclusion hT x := Subtype.ext he
      exact this ▸ hy
  rw [hk]
  exact hind

/-- The entire order-four exceptional amalgam, with both embedding squares. -/
theorem IsGoldschmidtTriple.case_two_of_intersection_card_four
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (h₁ : generalizedFitting G₁ ≠ pCore 2 G₁)
    (h₂ : generalizedFitting G₂ ≠ pCore 2 G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      RankTwoAmalgam.dihedralTwelvePair) := by
  let α := RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
  let e₁ := h.quotient_left.some
  let e₂ := h.quotient_right.some
  let f₁ := e₁.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G₁))
  let f₂ := e₂.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G₂))
  have hTs : Nat.card (G₂ ⊓ G₁ : Subgroup G) = 4 := by
    simpa only [inf_comm G₂ G₁] using hT
  have hc₁ : Nat.card G₁ = 12 := by
    rw [SymmetricThreeTwoCore.card_eq e₁, local_core_card_two h hT]
  have hc₂ : Nat.card G₂ = 12 := by
    rw [SymmetricThreeTwoCore.card_eq e₂, local_core_card_two h.symm hTs]
  have hk₁ : f₁.ker = pCore 2 G₁ := by
    rw [MonoidHom.ker_comp_of_injective _ _ e₁.injective, QuotientGroup.ker_mk']
  have hk₂ : f₂.ker = pCore 2 G₂ := by
    rw [MonoidHom.ker_comp_of_injective _ _ e₂.injective, QuotientGroup.ker_mk']
  obtain ⟨r₁, hr₁⟩ := retraction_of_normal_complement_card α.left
    (inclusion_injective inf_le_left) (pResidual 2 G₁)
    (by rw [h.local_residual_order_three h₁, hT]; decide)
    (by rw [hc₁, h.local_residual_order_three h₁, hT])
  obtain ⟨r₂, hr₂⟩ := retraction_of_normal_complement_card α.right
    (inclusion_injective inf_le_right) (pResidual 2 G₂)
    (by rw [h.symm.local_residual_order_three h₂, hT]; decide)
    (by rw [hc₂, h.symm.local_residual_order_three h₂, hT])
  apply iso_dihedralTwelvePair α f₁ f₂ hc₁ hT hc₂
    (local_quotient_middle_card e₁ _ inf_le_left h.left_core_index) ?_ ?_ ?_ ?_ r₁ hr₁ r₂ hr₂
  · apply local_quotient_middle_card e₂ _ inf_le_right
    simpa only [inf_comm G₂ G₁] using h.symm.left_core_index
  · rw [hk₁]
    intro x hx
    have hm := h.local_twoCore_le_intersection (mem_map_of_mem G₁.subtype hx)
    exact ⟨⟨x, hm⟩, rfl⟩
  · rw [hk₂]
    intro x hx
    have hm := h.symm.local_twoCore_le_intersection (mem_map_of_mem G₂.subtype hx)
    exact ⟨⟨x, hm.2, hm.1⟩, rfl⟩
  · apply le_antisymm _ bot_le
    intro b hb
    have hb₁ : α.left b ∈ pCore 2 G₁ := hk₁ ▸ hb.1
    have hb₂ : α.right b ∈ pCore 2 G₂ := hk₂ ▸ hb.2
    have hm : (b : G) ∈ (pCore 2 G₁).map G₁.subtype ⊓
        (pCore 2 G₂).map G₂.subtype :=
      ⟨mem_map_of_mem G₁.subtype hb₁, mem_map_of_mem G₂.subtype hb₂⟩
    rw [h.core_intersection_eq_bot_of_neither_characteristic_two hcore h₁ h₂] at hm
    exact Subtype.ext hm

/-- Both exceptional vertices give exactly the first two source rows. -/
theorem IsGoldschmidtTriple.first_two_cases_of_neither_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (h₁ : generalizedFitting G₁ ≠ pCore 2 G₁)
    (h₂ : generalizedFitting G₂ ≠ pCore 2 G₂) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      RankTwoAmalgam.symmetricThreePair) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      RankTwoAmalgam.dihedralTwelvePair) := by
  rcases h.intersection_card_of_neither_characteristic_two hcore h₁ h₂ with hT | hT
  · exact Or.inl (h.case_one_of_intersection_card_two hT)
  · exact Or.inr (h.case_two_of_intersection_card_four hcore h₁ h₂ hT)

/-- Application to the original images in the literal quotient by `O₂(G)`. -/
theorem IsGoldschmidtTriple.quotient_first_two_cases_of_neither_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂)
    (h₁ : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) ≠
      pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))))
    (h₂ : generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) ≠
      pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G)))) :
    let q := QuotientGroup.mk' (pCore 2 G)
    let α := RankTwoAmalgam.ofSubgroups (G₁.map q) (G₁.map q ⊓ G₂.map q)
      (G₂.map q) inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α RankTwoAmalgam.symmetricThreePair) ∨
      Nonempty (RankTwoAmalgam.Iso α RankTwoAmalgam.dihedralTwelvePair) := by
  exact h.quotient_twoCore.first_two_cases_of_neither_characteristic_two
    h.quotient_twoCore_eq_bot h₁ h₂
/-- The corresponding intrinsic three quotients, using the literal quotient
maps and their original compatible amalgam isomorphism. -/
theorem IsGoldschmidtTriple.intrinsic_quotient_first_two_cases_of_neither_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂)
    (h₁ : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) ≠
      pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))))
    (h₂ : generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) ≠
      pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G)))) :
    let α := RankTwoAmalgam.ofSubgroupQuotients (QuotientGroup.mk' (pCore 2 G))
      G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α RankTwoAmalgam.symmetricThreePair) ∨
      Nonempty (RankTwoAmalgam.Iso α RankTwoAmalgam.dihedralTwelvePair) := by
  have hh := h.quotient_first_two_cases_of_neither_characteristic_two h₁ h₂
  dsimp only at hh ⊢
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
  rcases hh with hh | hh
  · obtain ⟨e⟩ := hh
    exact Or.inl ⟨e0.trans e⟩
  · obtain ⟨e⟩ := hh
    exact Or.inr ⟨e0.trans e⟩

end CFSG.Quasithin.ChapterF
