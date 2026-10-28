module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.CharacteristicVertex
public import Theory.GroupTheory.Amalgam.MixedDihedralEight.Concrete

/-!
# Compatible mixed Goldschmidt amalgams over D₈

The characteristic-two vertex is marked as S₄ on its actual Sylow subgroup.
The other vertex has normal cubic residual, so its quotient by that residual
retracts onto the same overlap. Its S₃ quotient reconstructs a cubic fiber
product with the overlap character. Faithfulness excludes the normal-four
character, leaving the two source rows, with both squares commuting.

Source: Aschbacher–Smith F.6.5(2)(iii–iv), printed p.305.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- Every vertex has three times the order of the original common Sylow. -/
theorem IsGoldschmidtTriple.local_card_eq_three_mul_intersection
    (h : IsGoldschmidtTriple G₁ G₂) :
    Nat.card G₁ = 3 * Nat.card (G₁ ⊓ G₂ : Subgroup G) := by
  let Q := (pCore 2 G₁).map G₁.subtype
  let K := Q.subgroupOf (G₁ ⊓ G₂)
  have hi : K.index = 2 := h.left_core_index
  have hc := K.index_mul_card
  have hK : Nat.card K = Nat.card (pCore 2 G₁) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv]
    exact (Nat.card_congr ((pCore 2 G₁).equivMapOfInjective G₁.subtype
      G₁.subtype_injective).toEquiv).symm
  rw [hi, hK] at hc
  rw [SymmetricThreeTwoCore.card_eq h.quotient_left.some, ← hc]
  omega

/-- The literal inclusion amalgam is faithful when the ambient two-core is trivial. -/
theorem IsGoldschmidtTriple.amalgam_faithful
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥) :
    Faithful (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right) := by
  apply faithful_ofSubgroups_of_completion _ _ _ _ _ h.generated
  intro N hn hN
  obtain ⟨T, hT⟩ := h.intersection_sylow
  have hp := T.isPGroup'.to_le (hN.trans hT.le)
  apply le_bot_iff.mp
  rw [← hcore]
  exact le_sSup ⟨hn, hp⟩

private theorem quotient_middle_card (h : IsGoldschmidtTriple G₁ G₂)
    (e : (G₁ ⧸ pCore 2 G₁) ≃* CubicFiber.S3) :
    Nat.card ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G₁))).comp
      (inclusion (show G₁ ⊓ G₂ ≤ G₁ from inf_le_left))).range = 2 := by
  rw [← index_ker]
  have hk : ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G₁))).comp
      (inclusion (show G₁ ⊓ G₂ ≤ G₁ from inf_le_left))).ker =
      ((pCore 2 G₁).map G₁.subtype).subgroupOf (G₁ ⊓ G₂) := by
    ext x
    change e (QuotientGroup.mk' _ (inclusion inf_le_left x)) = 1 ↔ _
    rw [← e.map_one, e.injective.eq_iff]
    change (QuotientGroup.mk (inclusion inf_le_left x) : G₁ ⧸ pCore 2 G₁) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx; exact ⟨inclusion inf_le_left x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      have : y = inclusion inf_le_left x := Subtype.ext he
      exact this ▸ hy
  rw [hk]
  exact h.left_core_index

/-- A bad endpoint is the cubic fiber product on its original whole overlap. -/
theorem IsGoldschmidtTriple.local_fiber_of_not_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    ∃ χ : (G₁ ⊓ G₂ : Subgroup G) →* ℤˣ, χ ≠ 1 ∧
      ∃ e : G₁ ≃* CubicFiber.group χ,
        ∀ b, e (inclusion (show G₁ ⊓ G₂ ≤ G₁ from inf_le_left) b) =
          CubicFiber.inclusion χ b := by
  let i := inclusion (show G₁ ⊓ G₂ ≤ G₁ from inf_le_left)
  let e := h.quotient_left.some
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G₁))
  have hk : f.ker = pCore 2 G₁ := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hle : f.ker ≤ i.range := by
    rw [hk]
    intro x hx
    exact ⟨⟨x, h.local_twoCore_le_intersection (mem_map_of_mem G₁.subtype hx)⟩, rfl⟩
  have hcop : (Nat.card (pResidual 2 G₁)).Coprime (Nat.card (G₁ ⊓ G₂ : Subgroup G)) := by
    obtain ⟨T,hT⟩ := h.intersection_sylow
    rw [h.local_residual_order_three hbad,hT]
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨r, hr⟩ := retraction_of_normal_complement_card i (inclusion_injective inf_le_left)
    (pResidual 2 G₁) hcop
    (by rw [h.local_card_eq_three_mul_intersection, h.local_residual_order_three hbad])
  obtain ⟨χ, hχ, a, ha⟩ := CubicFiber.exists_equiv i f
    h.local_card_eq_three_mul_intersection (quotient_middle_card h e) hle r hr
  refine ⟨χ, ?_, a, ha⟩
  intro hχone
  have hh := quotient_middle_card h e
  rw [← index_ker, ← hχ, hχone, MonoidHom.ker_one, index_top] at hh
  omega

/-- Both mixed rows at overlap order eight, as actual compatible amalgams.
The reflection character is row (iii), with its vertices interchanged. -/
theorem IsGoldschmidtTriple.mixed_eight_cases
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      (MixedEight.amalgam MixedEight.reflectionCharacter)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      (MixedEight.amalgam MixedEight.rotationCharacter)) := by
  obtain ⟨a, uS, ha⟩ :=
    h.local_marked_symmetric_four_of_intersection_card_eight hgood hT MixedEight.squareSylow
  let u : (G₁ ⊓ G₂ : Subgroup G) ≃* MixedEight.D8 :=
    uS.trans (MonoidHom.ofInjective MixedEight.square_injective).symm
  have hau (b : (G₁ ⊓ G₂ : Subgroup G)) :
      a (inclusion inf_le_left b) = MixedEight.square (u b) := by
    exact (ha b).trans (MonoidHom.apply_ofInjective_symm MixedEight.square_injective (uS b)).symm
  obtain ⟨χ₀, hχ₀, c₀, hc₀⟩ := h.symm.local_fiber_of_not_characteristic_two hbad
  let v : (G₂ ⊓ G₁ : Subgroup G) ≃* MixedEight.D8 :=
    (MulEquiv.subgroupCongr (inf_comm G₂ G₁)).trans u
  let χ := χ₀.comp v.symm.toMonoidHom
  let c := c₀.trans (CubicFiber.congr χ₀ v)
  let iso : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      (MixedEight.amalgam χ) := {
    left := a
    middle := u
    right := c
    left_commutes := hau
    right_commutes := fun b => by
      change CubicFiber.congr χ₀ v (c₀ (inclusion inf_le_right b)) = CubicFiber.inclusion χ (u b)
      let b' : (G₂ ⊓ G₁ : Subgroup G) := ⟨b.val, b.property.2, b.property.1⟩
      have hh : c₀ (inclusion inf_le_right b) = CubicFiber.inclusion χ₀ b' := hc₀ b'
      rw [hh]
      exact (CubicFiber.congr_inclusion χ₀ v b').trans
        (congrArg (CubicFiber.inclusion χ) (congrArg u (Subtype.ext rfl))) }
  have hχ : χ ≠ 1 := by
    intro hh
    apply hχ₀
    apply MonoidHom.ext
    intro b
    have he := DFunLike.congr_fun hh (v b)
    simpa only [χ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, v.symm_apply_apply,
      MonoidHom.one_apply] using he
  rcases MixedEight.character_cases_of_faithful χ hχ (iso.faithful (h.amalgam_faithful hcore)) with he | he
  · exact Or.inl ⟨he ▸ iso⟩
  · exact Or.inr ⟨he ▸ iso⟩

/-- The mixed classification on the original images in the literal quotient. -/
theorem IsGoldschmidtTriple.quotient_mixed_eight_cases
    (h : IsGoldschmidtTriple G₁ G₂)
    (hgood : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) =
      pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))))
    (hbad : generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) ≠
      pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G))))
    (hT : Nat.card ((G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 G))) = 8) :
    let q := QuotientGroup.mk' (pCore 2 G)
    let α := RankTwoAmalgam.ofSubgroups (G₁.map q) (G₁.map q ⊓ G₂.map q)
      (G₂.map q) inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.reflectionCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.rotationCharacter)) := by
  apply h.quotient_twoCore.mixed_eight_cases h.quotient_twoCore_eq_bot hgood hbad
  rw [← h.quotient_twoCore_intersection]
  exact hT

/-- The intrinsic vertex quotients and the whole intrinsic overlap quotient
inherit the same commuting squares through the original quotient map. -/
theorem IsGoldschmidtTriple.intrinsic_quotient_mixed_eight_cases
    (h : IsGoldschmidtTriple G₁ G₂)
    (hgood : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) =
      pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))))
    (hbad : generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) ≠
      pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G))))
    (hT : Nat.card ((G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 G))) = 8) :
    let α := RankTwoAmalgam.ofSubgroupQuotients (QuotientGroup.mk' (pCore 2 G))
      G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.reflectionCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.rotationCharacter)) := by
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
  rcases h.quotient_mixed_eight_cases hgood hbad hT with hh | hh
  · obtain ⟨e⟩ := hh
    exact Or.inl ⟨e0.trans e⟩
  · obtain ⟨e⟩ := hh
    exact Or.inr ⟨e0.trans e⟩

end CFSG.Quasithin.ChapterF
