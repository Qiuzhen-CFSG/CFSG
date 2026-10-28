module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.MixedEight
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.CosetBound
public import Theory.GroupTheory.ElementaryEightSymmetricThreeCenter
public import Theory.GroupTheory.CentralTwoSymmetricFourRecognition
public import Theory.GroupTheory.SelfCentralizingTwoSubgroupSize
public import Theory.GroupTheory.Amalgam.MixedSixteen.Models
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.CosetBound.Exceptional

/-!
# The characteristic-two vertex at overlap order sixteen

The opposite cubic residual forces the local core to be elementary abelian.
Its faithful S₃ action fixes a central line. The opposite core is core-free
in this vertex, hence complements that line in the common Sylow. Gaschütz
extends the complement, identifying the vertex with C₂×S₄.

Source: Aschbacher–Smith F.6.5(2)(v), printed p.305.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.RankTwoAmalgam
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The cubic residual at the opposite vertex makes the actual local core elementary. -/
theorem IsGoldschmidtTriple.local_core_elementary_of_opposite_not_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂) :
    IsElementaryAbelian 2 (pCore 2 G₁) := by
  let e := (pCore 2 G₁).equivMapOfInjective G₁.subtype G₁.subtype_injective
  let : IsElementaryAbelian 2 ((pCore 2 G₁).map G₁.subtype) :=
    SourceAssembly.right_core_elementary_of_left_residual_card_three h.symm hcore (by
      rw [← Nat.card_congr ((pResidual 2 G₂).equivMapOfInjective
        G₂.subtype G₂.subtype_injective).toEquiv]
      exact h.symm.local_residual_order_three hbad)
  refine { toIsMulCommutative := ⟨⟨fun a b => e.injective (by simp only [map_mul,mul_comm'])⟩⟩
           exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  apply e.injective
  rw [map_pow,map_one]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 _) (e x)

/-- Recognition of the actual characteristic-two vertex in row (v). -/
theorem IsGoldschmidtTriple.local_equiv_c2_symmetric_four_of_intersection_card_sixteen
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 16) :
    Nonempty (G₁ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  let Q := pCore 2 G₁
  let H := (G₁ ⊓ G₂).subgroupOf G₁
  let R := ((pCore 2 G₂).map G₂.subtype).subgroupOf G₁
  let : IsElementaryAbelian 2 Q :=
    h.local_core_elementary_of_opposite_not_characteristic_two hcore hbad
  have hGcard : Nat.card G₁ = 48 := by rw [h.local_card_eq_three_mul_intersection,hT]
  have hQcard : Nat.card Q = 8 := by
    have hc := SymmetricThreeTwoCore.card_eq h.quotient_left.some
    rw [hGcard] at hc
    change 48 = 6 * Nat.card Q at hc
    omega
  obtain ⟨Z,hZcard,hZQ,hZ⟩ := exists_central_card_two_of_elementary_eight_symmetric_three
    Q hQcard (h.local_core_selfCentralizing hgood) h.quotient_left
  have hQH : Q ≤ H := fun x hx =>
    h.local_twoCore_le_intersection (mem_map_of_mem G₁.subtype hx)
  have hRle : (pCore 2 G₂).map G₂.subtype ≤ G₁ ⊓ G₂ := by
    simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection
  have hRH : R ≤ H := fun x hx => hRle hx
  have hHcard : Nat.card H = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show G₁ ⊓ G₂ ≤ G₁ from inf_le_left)).toEquiv).trans hT
  have hRcard : Nat.card R = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hRle.trans inf_le_left)).toEquiv,
      ← Nat.card_congr ((pCore 2 G₂).equivMapOfInjective G₂.subtype G₂.subtype_injective).toEquiv]
    have hg : Nat.card G₂ = 48 := by
      rw [h.symm.local_card_eq_three_mul_intersection,inf_comm G₂ G₁,hT]
    have hc := SymmetricThreeTwoCore.card_eq h.quotient_right.some
    omega
  have hRcore : R.normalCore = ⊥ :=
    h.symm.opposite_core_normalCore_eq_bot hcore (h.symm.local_core_centralizes_residual hbad)
  obtain ⟨K,hK⟩ := central_two_complement_of_corefree_half Z H R hZ (hZQ.trans hQH)
    hZcard hHcard hRcard hGcard hRH hRcore
  exact c2_symmetric_four_of_central_complement Q Z K hQcard
    (h.local_core_selfCentralizing hgood) hZ hZQ hZcard hGcard hK

/-- The characteristic-two branch cannot have overlap order two or four. -/
theorem IsGoldschmidtTriple.intersection_card_ge_eight_of_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hgood : generalizedFitting G₁ = pCore 2 G₁) :
    8 ≤ Nat.card (G₁ ⊓ G₂ : Subgroup G) := by
  have hc := SymmetricThreeTwoCore.card_eq h.quotient_left.some
  have hmin := card_ge_four_of_selfCentralizing_normal_two_subgroup (pCore 2 G₁)
    pCore_isPGroup (h.local_core_selfCentralizing hgood) (by rw [hc]; omega)
  have ht := h.local_card_eq_three_mul_intersection
  omega

/-- The two genuine mixed overlap orders; no extra size premise remains. -/
theorem IsGoldschmidtTriple.intersection_card_eight_or_sixteen_of_mixed
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂) :
    Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8 ∨ Nat.card (G₁ ⊓ G₂ : Subgroup G) = 16 := by
  have hdiv : Nat.card (G₁ ⊓ G₂ : Subgroup G) ∣ 16 := by
    simpa only [inf_comm G₂ G₁] using
      h.symm.intersection_card_dvd_sixteen_of_not_characteristic_two hcore hbad
  have hmin := h.intersection_card_ge_eight_of_characteristic_two hgood
  have hm := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  have hs : (16 : ℕ).divisors = {1,2,4,8,16} := by decide
  rw [hs] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  omega

/-- Mark the whole original common Sylow inside a chosen Sylow of C₂×S₄. -/
theorem IsGoldschmidtTriple.local_marked_c2_symmetric_four_of_intersection_card_sixteen
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 16)
    (S : Sylow 2 (ℤˣ × Equiv.Perm (Fin 4))) :
    ∃ e : G₁ ≃* ℤˣ × Equiv.Perm (Fin 4), ∃ u : (G₁ ⊓ G₂ : Subgroup G) ≃* S,
      ∀ t, e (inclusion (show G₁ ⊓ G₂ ≤ G₁ from inf_le_left) t) = u t := by
  obtain ⟨e₀⟩ := h.local_equiv_c2_symmetric_four_of_intersection_card_sixteen hcore hgood hbad hT
  let eZ : Multiplicative (ZMod 2) ≃* ℤˣ :=
    mulEquivOfPrimeCardEq (p := 2) (by simp [Nat.card_eq_fintype_card]) (by rw [Nat.card_eq_fintype_card]; decide)
  let e := e₀.trans (MulEquiv.prodCongr eZ (MulEquiv.refl _))
  obtain ⟨T,hTs⟩ := h.intersection_sylow
  have hTG : (T : Subgroup G) ≤ G₁ := hTs.symm.le.trans inf_le_left
  let P := T.subtype hTG
  have hp : (P : Subgroup G₁) = (inclusion (show G₁ ⊓ G₂ ≤ G₁ from inf_le_left)).range := by
    ext x
    change (x : G) ∈ (T : Subgroup G) ↔ _
    rw [←hTs]
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ => hy ▸ y.property⟩
  exact exists_normalized_endpoint (inclusion inf_le_left) S.toSubgroup.subtype
    (inclusion_injective inf_le_left) S.toSubgroup.subtype_injective P hp S
    (by rw [range_subtype]) e

/-- Row (v), with the original whole overlap and both literal inclusions. -/
theorem IsGoldschmidtTriple.mixed_sixteen_case
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 16) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      MixedSixteen.standard) := by
  obtain ⟨a,uS,ha⟩ := h.local_marked_c2_symmetric_four_of_intersection_card_sixteen
    hcore hgood hbad hT MixedSixteen.leftSylow
  let u : (G₁ ⊓ G₂ : Subgroup G) ≃* MixedSixteen.Middle :=
    uS.trans (MonoidHom.ofInjective MixedSixteen.left_injective).symm
  have hau (b : (G₁ ⊓ G₂ : Subgroup G)) :
      a (inclusion inf_le_left b) = MixedSixteen.left (u b) := by
    exact (ha b).trans (MonoidHom.apply_ofInjective_symm MixedSixteen.left_injective (uS b)).symm
  obtain ⟨χ₀,_hχ₀,c₀,hc₀⟩ := h.symm.local_fiber_of_not_characteristic_two hbad
  let v : (G₂ ⊓ G₁ : Subgroup G) ≃* MixedSixteen.Middle :=
    (MulEquiv.subgroupCongr (inf_comm G₂ G₁)).trans u
  let χ := χ₀.comp v.symm.toMonoidHom
  let c := c₀.trans (CubicFiber.congr χ₀ v)
  let iso : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      (MixedSixteen.amalgam χ) := {
    left := a
    middle := u
    right := c
    left_commutes := hau
    right_commutes := fun b => by
      change CubicFiber.congr χ₀ v (c₀ (inclusion inf_le_right b)) = CubicFiber.inclusion χ (u b)
      let b' : (G₂ ⊓ G₁ : Subgroup G) := ⟨b.val,b.property.2,b.property.1⟩
      have hh : c₀ (inclusion inf_le_right b) = CubicFiber.inclusion χ₀ b' := hc₀ b'
      rw [hh]
      exact (CubicFiber.congr_inclusion χ₀ v b').trans
        (congrArg (CubicFiber.inclusion χ) (congrArg u (Subtype.ext rfl))) }
  obtain ⟨e⟩ := MixedSixteen.iso_standard_of_faithful χ (iso.faithful (h.amalgam_faithful hcore))
  exact ⟨iso.trans e⟩

/-- All three mixed source rows, without a size or recognition premise. -/
theorem IsGoldschmidtTriple.mixed_cases
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting G₁ = pCore 2 G₁)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂) :
    let α := RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.reflectionCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.rotationCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α MixedSixteen.standard) := by
  rcases h.intersection_card_eight_or_sixteen_of_mixed hcore hgood hbad with hT | hT
  · rcases h.mixed_eight_cases hcore hgood hbad hT with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr (h.mixed_sixteen_case hcore hgood hbad hT))

/-- All mixed rows on the literal images in G/O₂(G). -/
theorem IsGoldschmidtTriple.quotient_mixed_cases
    (h : IsGoldschmidtTriple G₁ G₂)
    (hgood : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) =
      pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))))
    (hbad : generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) ≠
      pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G)))) :
    let q := QuotientGroup.mk' (pCore 2 G)
    let α := RankTwoAmalgam.ofSubgroups (G₁.map q) (G₁.map q ⊓ G₂.map q)
      (G₂.map q) inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.reflectionCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.rotationCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α MixedSixteen.standard) :=
  h.quotient_twoCore.mixed_cases h.quotient_twoCore_eq_bot hgood hbad

/-- All mixed rows on the intrinsic vertex and whole overlap quotients. -/
theorem IsGoldschmidtTriple.intrinsic_quotient_mixed_cases
    (h : IsGoldschmidtTriple G₁ G₂)
    (hgood : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) =
      pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))))
    (hbad : generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) ≠
      pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G)))) :
    let α := RankTwoAmalgam.ofSubgroupQuotients (QuotientGroup.mk' (pCore 2 G))
      G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right
    Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.reflectionCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α (MixedEight.amalgam MixedEight.rotationCharacter)) ∨
      Nonempty (RankTwoAmalgam.Iso α MixedSixteen.standard) := by
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
  rcases h.quotient_mixed_cases hgood hbad with hh | hh | hh
  · obtain ⟨e⟩ := hh
    exact Or.inl ⟨e0.trans e⟩
  · obtain ⟨e⟩ := hh
    exact Or.inr (Or.inl ⟨e0.trans e⟩)
  · obtain ⟨e⟩ := hh
    exact Or.inr (Or.inr ⟨e0.trans e⟩)

end CFSG.Quasithin.ChapterF
