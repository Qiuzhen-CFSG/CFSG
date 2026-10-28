module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSpanDisplacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointA7Inner
public import Theory.GroupAction.AlternatingSevenSmallSuborbits

/-!
# The actual A7 point centralizer normalizes the original four

The original quotient action on U/<z> has B-displacement of order at most
eight, by the literal image of [U,L]. Every element of H/<z> is fixed by B.
The fifteen-point A7 action forces these elements to be fixed by the whole
containing carrier: a moved point would have a B-orbit of fourteen other
points. Pullback gives normalization of H by the carrier preimage. The
previous inner-action theorem supplies its literal supplement, which also
normalizes H, and hence the whole point centralizer normalizes H.

Source: Aschbacher--Smith15.3.23, pp.1128--1129, using B.4.12(2), p.97,
and the original center decomposition of MS93(4.5), p.895.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_of_displacement_of_equiv
    {A W : Type*} [Group A] [Group W] [Finite W]
    (a : A ≃* alternatingGroup (Fin 7)) (ρ : A →* MulAut W)
    (B : Subgroup A) (e : B ≃* PSL(3,ZMod 2))
    (D : Subgroup W) (hD : Nat.card D ≤ 8)
    (hdisp : ∀ (b : B) (w : W), ρ b w * w⁻¹ ∈ D)
    (x : W) (hfix : ∀ b : B, ρ b x = x) : ∀ g : A, ρ g x = x := by
  let B₇ := B.map a.toMonoidHom
  let e₇ : B₇ ≃* PSL(3,ZMod 2) := (a.subgroupMap B).symm.trans e
  let ρ₇ := ρ.comp a.symm.toMonoidHom
  have hd (b₇ : B₇) (w : W) : ρ₇ b₇ w * w⁻¹ ∈ D := by
    rcases b₇ with ⟨b₇,b,hb,rfl⟩
    simpa only [ρ₇,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,a.symm_apply_apply]
      using hdisp ⟨b,hb⟩ w
  have hx (b₇ : B₇) : ρ₇ b₇ x = x := by
    rcases b₇ with ⟨b₇,b,hb,rfl⟩
    simpa only [ρ₇,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,a.symm_apply_apply]
      using hfix ⟨b,hb⟩
  intro g
  simpa only [ρ₇,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,a.symm_apply_apply] using
    Theory.GroupAction.alternatingSeven_fixed_of_displacement_card_le_eight
      ρ₇ B₇ e₇ D hD hd x hx (a g)

private theorem carrier_normalizes_four_of_quotient_action
    (C L H U Z : Subgroup G) (hLC : L ≤ C) (hHU : H ≤ U) (hZH : Z ≤ H)
    (hCU : C ≤ normalizer U) (hHL : H ≤ centralizer (L : Set G))
    (hsmall : Nat.card (⁅U,L⁆ : Subgroup G) ≤ 8)
    (hn : (Z.subgroupOf U).Normal)
    (K : Subgroup (C ⧸ pCore 2 C))
    (hBK : (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) ≤ K)
    (eB : ((L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))) ≃* PSL(3,ZMod 2))
    (a : K ≃* alternatingGroup (Fin 7)) :
    letI := hn
    ∀ ρ : (C ⧸ pCore 2 C) →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ (x : C) (u v : U), (v : G) = x*(u : G)*(x : G)⁻¹ →
        ρ (QuotientGroup.mk' (pCore 2 C) x) (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U) v) →
      (K.comap (QuotientGroup.mk' (pCore 2 C))).map C.subtype ≤ normalizer H := by
  let := hn
  intro ρ hρ
  let q := QuotientGroup.mk' (pCore 2 C)
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  let B := (L.subgroupOf C).map q
  let B₀ := B.subgroupOf K
  let ρK := ρ.comp K.subtype
  let D₀ := (⁅U,L⁆ : Subgroup G).subgroupOf U
  let D := D₀.map π
  have hcommU : ⁅U,L⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp (hLC.trans hCU)
  have hD : Nat.card D ≤ 8 := by
    have hh := Nat.card_le_card_of_surjective (π.subgroupMap D₀) (π.subgroupMap_surjective D₀)
    have he : Nat.card D₀ = Nat.card (⁅U,L⁆ : Subgroup G) :=
      Nat.card_congr (subgroupOfEquivOfLe hcommU).toEquiv
    exact hh.trans (he ▸ hsmall)
  have hdisp (b₀ : B₀) (w : U ⧸ Z.subgroupOf U) : ρK b₀ w * w⁻¹ ∈ D := by
    obtain ⟨l,hl,he⟩ := b₀.property
    change q l = ((b₀ : K) : C ⧸ pCore 2 C) at he
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
    let v : U := ⟨(l : G)*(u : G)*(l : G)⁻¹,
      (mem_normalizer_iff.mp (hCU l.property) u).mp u.property⟩
    change ρ ((b₀ : K) : C ⧸ pCore 2 C) (π u) * (π u)⁻¹ ∈ D
    rw [←he,hρ l u v rfl,←map_inv,←map_mul]
    apply mem_map_of_mem π
    change (l : G)*(u : G)*(l : G)⁻¹*(u : G)⁻¹ ∈ ⁅U,L⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hl u.property
  have hfix (h : H) : ∀ k : K, ρ k (π ⟨h,hHU h.property⟩) = π ⟨h,hHU h.property⟩ := by
    apply fixed_of_displacement_of_equiv a ρK B₀
      ((subgroupOfEquivOfLe hBK).trans eB) D hD hdisp
    intro b₀
    obtain ⟨l,hl,he⟩ := b₀.property
    change q l = ((b₀ : K) : C ⧸ pCore 2 C) at he
    change ρ ((b₀ : K) : C ⧸ pCore 2 C) (π ⟨h,hHU h.property⟩) = _
    rw [←he]
    apply hρ l _ _
    have hh := hHL h.property l hl
    change (l : G)*(h : G) = (h : G)*(l : G) at hh
    rw [hh,mul_inv_cancel_right]
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  rintro g ⟨g,hg,rfl⟩ h hh
  let u : U := ⟨h,hHU hh⟩
  let v : U := ⟨(g : G)*h*(g : G)⁻¹,
    (mem_normalizer_iff.mp (hCU g.property) h).mp (hHU hh)⟩
  have hv : π v = π u := (hρ g u v rfl).symm.trans (hfix ⟨h,hh⟩ ⟨q g,hg⟩)
  have hz : (g : G)*h*(g : G)⁻¹/h ∈ Z :=
    (QuotientGroup.eq_iff_div_mem (N := Z.subgroupOf U)).mp hv
  change ⁅(g : G),h⁆ ∈ H
  exact hZH (by simpa only [commutatorElement_def,div_eq_mul_inv] using hz)

/-- The original source, its full Sylow and the actual A7 carrier force
the point centralizer to normalize the unchanged intrinsic four. -/
theorem binary_three_source_a7_four_invariant
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (a : K ≃* alternatingGroup (Fin 7)) :
    centralizer ({z} : Set G) ≤ normalizer (intrinsicFour c.L) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let L₀ := c.L.subgroupOf C
  let B := L₀.map q
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  obtain ⟨hZH,_,hHU,_,hCU,_,hn,_,ρ,hρ⟩ := binary_three_source_a7_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK a
  let := hn
  have hsmall := (binary_three_source_a7_span_displacement_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK a).2.2
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hHL : H ≤ centralizer (c.L : Set G) :=
    (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2.trans inf_le_right
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkL : IsPGroup 2 (q.subgroupMap L₀).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eL := subgroupOfEquivOfLe hLC
  let e₀ := (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).trans e
  let eB₀ := ((q.subgroupMap L₀).pCoreQuotientEquiv
    (q.subgroupMap_surjective L₀) hkL).symm.trans e₀
  have hbot := (binary_three_alternating_seven_placement hBK eB₀ a).1
  let eB : B ≃* PSL(3,ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans eB₀
  have hA := carrier_normalizes_four_of_quotient_action C c.L H U Z hLC hHU hZH
    hCU hHL hsmall hn K hBK eB a ρ hρ
  obtain ⟨_,_,_,hcover,_,hD⟩ := binary_three_point_a7_inner_control d c.L e b z hLS P hP K hBK a
  rw [←hcover]
  exact sup_le hA hD

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
