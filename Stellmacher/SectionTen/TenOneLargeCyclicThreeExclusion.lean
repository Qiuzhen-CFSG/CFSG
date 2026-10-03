module
public import Stellmacher.SectionNine.NineResidualOddCoreEquality
public import Stellmacher.SectionTen.TenOneSmallCommutatorActor
public import Stellmacher.TwoResidualSylowSupplement
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# Exclude the cyclic-three terminal residual

For the actual Section Ten terminal quotient action, an odd core of order three
would force a Sylow-two subgroup of index three in the terminal stabilizer.
The resulting three-conjugate middle-center bound puts the terminal quotient
module at order at most eight, while the selected nontransvection actor has
displacement order four. The action's exact conjugation formula then gives a
square-card contradiction. This route uses the supplied action and kernel
literally and needs no source (13) equality or extra local model assumption.

Source: Stellmacher (10.1), printed p.63 after (13); the order-eight bound is
the three-conjugate local center argument, and the contradiction is the
no-transvection displacement alternative.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionEight
open scoped IsMulCommutative
universe u

private theorem index_three_of_normal_three_supplement
    {X : Type*} [Group X] [Finite X] (O S : Subgroup X) [O.Normal]
    (hO : Nat.card O = 3) (hS : IsPGroup 2 S) (hgen : O ⊔ S = ⊤) : S.index = 3 := by
  have hdisjoint : Disjoint O S := by
    apply disjoint_iff_inf_le.mpr
    have htwo : IsPGroup 2 (O ⊓ S : Subgroup X) := hS.to_le inf_le_right
    have hdiv := Subgroup.card_dvd_of_le (inf_le_left : O ⊓ S ≤ O)
    rw [hO] at hdiv
    rcases htwo.card_eq_or_dvd with hone | htwo
    · exact (Subgroup.eq_bot_of_card_eq _ hone).le
    · exact False.elim (by have := htwo.trans hdiv; norm_num at this)
  have hcard := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint O S
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hdisjoint
  rw [hgen, Nat.card_congr Subgroup.topEquiv.toEquiv, hO] at hcard
  have hcount := S.index_mul_card
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcount.trans hcard)

private theorem relative_index_of_card
    {G : Type*} [Group G] [Finite G] (U Z C : Subgroup G)
    (hZU : Z ≤ U) (hCU : C ≤ U) [(Z.subgroupOf U).Normal]
    (hcard : QuotientCardEq (C ⊔ Z) Z 4) : Z.relIndex C = 4 := by
  have hsup : C ⊔ Z ≤ U := sup_le hCU hZU
  have hindex : Z.relIndex (C ⊔ Z) = 4 := by
    have hmul := (Z.subgroupOf (C ⊔ Z)).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show Z ≤ C ⊔ Z from le_sup_right)).toEquiv] at hmul
    change Z.relIndex (C ⊔ Z) * Nat.card Z = Nat.card (C ⊔ Z : Subgroup G) at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hmul.trans hcard)
  have heq := Subgroup.relIndex_sup_right (C.subgroupOf U) (Z.subgroupOf U)
  rw [← Subgroup.subgroupOf_sup hCU hZU, Subgroup.relIndex_subgroupOf hsup,
    Subgroup.relIndex_subgroupOf hCU] at heq
  exact heq ▸ hindex

public theorem ten_one_large_oddCore_card_ne_three
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    [hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (VAt ctx.Γ ctx.criticalPath.a')).Normal]
    [hW : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))]
    (action : GAt ctx.Γ ctx.criticalPath.a' →* MulAut
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')))
    (hformula : ∀ mover : GAt ctx.Γ ctx.criticalPath.a',
      ∀ point : VAt ctx.Γ ctx.criticalPath.a',
      action mover (QuotientGroup.mk'
        ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')) point) =
        QuotientGroup.mk'
          ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))
          ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp
              (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                point).mp point.property⟩)
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a')) :
    Nat.card (SectionOne.oddCore action.range) ≠ 3 := by
  intro hthree
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let W := U ⧸ Z.subgroupOf U
  let X := action.range
  let O := SectionOne.oddCore X
  let f := action.rangeRestrict
  let _ : O.Normal := pPrimeCore_normal
  have hshort : 1 < cp.length := by have := ctx.critical_length; change 1 < ctx.criticalPath.length; omega
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  let edge := P ⊓ GAt Γ middle
  let edgeSylow : Sylow 2 edge := default
  let ambientSylow := sylowTwoAmbient edge edgeSylow
  have hdata := edge_sectionThree_data ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal)) edgeSylow
  obtain ⟨sylow,hsylow⟩ := hdata.2.1.1.2.1
  have hcore : pCore 2 P ≤ f.ker := by rw [MonoidHom.ker_rangeRestrict,hkernel]
  have hresimage := nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
    cp.a' middle (Γ.adjacent_symm hterminal) f action.rangeRestrict_surjective hcore
  have hnative : (EAt Γ cp.a').subgroupOf P = twoResidualAmbient (⊤ : Subgroup P) := by
    have hn : (EAt Γ cp.a').subgroupOf P = twoResidualSubgroup P := by
      rw [EAt,CosetGraphContext.e,Γ.twoResidualAt_def]
      exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    rw [hn,SectionThree.twoResidualSubgroup_eq_hktPResidual',
      SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  change ((EAt Γ cp.a').subgroupOf P).map f = O at hresimage
  rw [hnative] at hresimage
  let imageSylow := (sylow : Subgroup P).map f
  have hgen : O ⊔ imageSylow = ⊤ := by
    rw [← hresimage, ← Subgroup.map_sup, twoResidualAmbient_top_sup_sylow]
    exact Subgroup.map_top_of_surjective f action.rangeRestrict_surjective
  have hindexImage := index_three_of_normal_three_supplement O imageSylow hthree
    (sylow.isPGroup'.map f) hgen
  have hindexSylow : (sylow : Subgroup P).index = 3 := by
    have hkerS : f.ker ≤ sylow := by
      rw [MonoidHom.ker_rangeRestrict,hkernel]
      exact pCore_isPGroup.le_sylow_of_normal sylow
    rw [← Subgroup.index_map_eq (sylow : Subgroup P) action.rangeRestrict_surjective hkerS]
    exact hindexImage
  have hSylowMiddle : (sylow : Subgroup P).map P.subtype ≤ GAt Γ middle := by
    rw [hsylow]
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  obtain ⟨a,b,c,hconjugates⟩ := eight_six_three_conjugates_of_index_three
    (ZAt Γ middle) P sylow
      (hSylowMiddle.trans (stabilizer_le_normalizer_z Γ middle)) hindexSylow
  have hclosure : U = conjugateClosure (ZAt Γ middle) P :=
    eight_six_neighbor_join_eq_conjugate_closure ctx.sectionSeven Γ cp.a' middle
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal))
  have hmiddleCard : Nat.card (ZAt Γ middle) = 4 :=
    (sectionTenOpeningData ctx middle hpath).center_card
  have hline : Z ≤ ZAt Γ middle := by
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_right
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hcenterData := nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort cp.a' ⟨alignment,halignment⟩
  have htwo : Nat.card Z = 2 := hcenterData.1
  have hderived : ⁅U,U⁆ ≤ Z := by
    change ⁅U,U⁆ ≤ ZAt ctx.Γ cp.a'
    rw [← hcenterData.2.1]
    exact Subgroup.commutator_mono le_rfl
      (neighbor_join_le_core_of_length_gt_one Γ cp hshort cp.a')
  have hcommon (mover : P) : Z ≤ conjugateBy (ZAt Γ middle) mover :=
    eight_six_common_line_le_conjugate _ _ _ hline
      (stabilizer_le_normalizer_z Γ cp.a') mover
  have hUbound : Nat.card U ≤ 16 := by
    rw [hclosure] at hderived ⊢
    exact eight_six_three_conjugates_card_le _ _ _ a b c hmiddleCard htwo
      (hcommon a) (hcommon b) (hcommon c) hconjugates hderived
  have hmiddleU : ZAt Γ middle ≤ U := by
    change ZAt Γ middle ≤ VAt Γ cp.a'
    rw [VAt,v,Γ.vAt_def]
    exact le_sSup ⟨middle,(mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal),rfl⟩
  have hZU : Z ≤ U := hline.trans hmiddleU
  have hWbound : Nat.card W ≤ 8 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,htwo] at hcount
    change Nat.card U = Nat.card W * 2 at hcount
    omega
  obtain ⟨actor,hactor,hout,hcases⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  have hindex := (hcases.resolve_left (hno actor hactor hout)).1
  let actorP : P :=
    ⟨actor,(lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2 hactor⟩
  let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
  have hpow : (action actorP) ^ 2 = 1 := by
    rw [← map_pow, show actorP ^ 2 = 1 from
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian actor hactor), map_one]
  let D := Subgroup.zpowers actor
  have hDP : D ≤ P := Subgroup.zpowers_le.mpr actorP.property
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hcommU : ⁅U,D⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hDP.trans hPU)
  have hrelative := relative_index_of_card U Z ⁅U,D⁆ hZU hcommU hindex
  have hDnative : D.subgroupOf P = Subgroup.zpowers actorP := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hDP,MonoidHom.map_zpowers]
    rfl
  have hrank := Subgroup.quotient_conjugation_commutatorAction_card P U Z D hPU hDP
    hN action hformula
  rw [hDnative,MonoidHom.map_zpowers] at hrank
  have hfour : Nat.card (commutatorAction (Subgroup.zpowers (action actorP)) W) = 4 :=
    hrank.trans hrelative
  have hlarge := MulAut.displacement_card_sq_le_card (action actorP) hpow
  change Nat.card (commutatorAction (Subgroup.zpowers (action actorP)) W) ^ 2 ≤ Nat.card W at hlarge
  rw [hfour] at hlarge
  omega

end Stellmacher.SectionTen
