module
public import Stellmacher.SectionNine.NineFourNoncentralSupportContainment
public import Stellmacher.SectionNine.NineFourActorClosureImage
public import Stellmacher.SectionNine.NineFourConjugatedActorImage
public import Stellmacher.SectionNine.NineFourAuxiliaryIndex
public import Stellmacher.SectionOne.OneSevenSmallFixedIntersectionNormalizer
public import Theory.GroupAction.ActorSubtypeCommutator

/-!
# Equality with the selected support in the noncentral case

In the normalized setup of Stellmacher (9.4), a noncentral auxiliary
subgroup V_y is exactly the lift of the canonical transvection factor's
four-element quotient support. It therefore has order eight and is
normalized by the next vertex's two-residual. The core-intersection image
normalizes the selected factor; this conclusion is retained for the
following geometric intersection argument. The theorem uses the actual
quotient action, normality witness, elementary-module instance, kernel,
involution, and canonical-factor data without replacing any of them.

The earlier containment theorem puts the selected support inside V_y.
The auxiliary intersection estimate gives index at most two for
V_y intersect V_remote. The literal actor closure fixes that intersection
and moves the selected support. The small-fixed-intersection normalizer
criterion then forces the image of Q_a intersect Q_remote to normalize
the selected factor. Consequently the auxiliary residual image, already
identified as the conjugate closure of its derived subgroup, lies in that
factor. The actual residual-support bound gives the reverse inclusion
after passing through the same quotient map.

This is relation (5) on printed p.51/PDF p.41 of Stellmacher's
`2-local structure of N-groups`. The following geometric intersection
identity and contradiction are handled separately.
-/

open scoped commutatorElement IsMulCommutative
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem factor_nonidentity_moves_support
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : SectionOne.Hypotheses K V) (D : Subgroup K)
    (hD : SectionOne.IsOneSevenFactor (V:=V) D)
    (a : K) (ha : a ∈ D) (hne : a ≠ 1) :
    ∃ v ∈ commutatorAction D V, a • v ≠ v := by
  by_contra hn
  push Not at hn
  let C := FixedPoints.subgroup ((commutator D).map D.subtype) V
  let S := commutatorAction D V
  have hcop : Nat.Coprime (Nat.card ((commutator D).map D.subtype)) (Nat.card V) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hD.2.1.2.1,hk]
    exact (show Nat.Coprime 3 2 by decide).pow_right k
  have hcompl : IsCompl C S := by
    dsimp [C,S]
    rw [SectionOne.oneSevenFactor_full_commutator_eq_derived D hD]
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G:=V) (A:=((commutator D).map D.subtype))
      (Group.isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M:=V)).comm x y)
      hcop inferInstance
  have hfix : a ∈ fixingSubgroup K (Set.univ : Set V) := by
    apply (mem_fixingSubgroup_iff K).mpr
    intro v _
    have hv : v ∈ C⊔S := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨c,hc,s,hs,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hv
    rw [smul_mul',SectionOne.oneSevenFactor_fixes_derived_fixedPoints D hD a ha c hc,hn s hs]
  rw [hyp.action_faithful] at hfix
  exact hne hfix

public theorem nine_four_noncentral_support_equality
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B0 : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B0)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2)
    (actor : G)
    (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∈ Subgroup.centralizer (VAt ctx.Γ remote : Set G))
    (conjugator : G)
    (hconjugator : conjugator ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers actor⁆)
    (hremote : ctx.Γ.act conjugator remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act conjugator remote ≠ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ ctx.criticalPath.a) ⊔
      Subgroup.zpowers actor = GAt ctx.Γ ctx.criticalPath.firstStep)
    (A : Subgroup G) (hA : A ≤ VAt ctx.Γ (ctx.Γ.act conjugator remote))
    (hcomm : ⁅A, Subgroup.zpowers actor⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (y : G) (hy : y ∈ A)
    (hnoncentral :
      let F := (QAt ctx.Γ ctx.criticalPath.a ⊓
        QAt ctx.Γ (ctx.Γ.act conjugator remote)) ⊔ Subgroup.zpowers actor
      let Q := twoCoreIn (twoResidualIn F)
      ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,Q⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep ≠ ZAt ctx.Γ ctx.criticalPath.firstStep)
    (hN : ((ZAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (VAt ctx.Γ ctx.criticalPath.firstStep)).Normal) :
    let _ := hN
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let U := VAt ctx.Γ ctx.criticalPath.firstStep
    let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
    ∀ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
    let _ := hW
    ∀ action : P →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ mover : P, ∀ point : U,
        action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
          QuotientGroup.mk' (Z.subgroupOf U)
            ⟨(mover:G)*(point:G)*(mover:G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp
                (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep mover.property)
                point).mp point.property⟩) →
      action.ker = pCore 2 P →
      _root_.IsInvolution (action ⟨actor,hactor.1⟩) →
      SectionOne.Hypotheses action.range (U ⧸ Z.subgroupOf U) →
      let D := ⁅SectionOne.oddCore action.range,
        Subgroup.zpowers (action.rangeRestrict ⟨actor,hactor.1⟩)⁆ ⊔
          Subgroup.zpowers (action.rangeRestrict ⟨actor,hactor.1⟩)
      SectionOne.IsOneSevenFactor (V := U ⧸ Z.subgroupOf U) D →
      let F := (QAt ctx.Γ ctx.criticalPath.a ⊓
        QAt ctx.Γ (ctx.Γ.act conjugator remote)) ⊔ Subgroup.zpowers actor
      let Q := twoCoreIn (twoResidualIn F)
      let V_y := ⁅Subgroup.zpowers y ⊔ U,Q⁆ ⊔ Z
      let support := ((commutatorAction D (U ⧸ Z.subgroupOf U)).comap
        (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype
      V_y = support ∧ Nat.card V_y = 8 ∧
        EAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (V_y : Set G) ∧
        (((QAt ctx.Γ ctx.criticalPath.a ⊓
          QAt ctx.Γ (ctx.Γ.act conjugator remote)).subgroupOf P).map
            action.rangeRestrict) ≤ Subgroup.normalizer D := by
  let _ := hN
  dsimp only
  intro hW
  let _ := hW
  intro action hact hkernel hinvolution hyp hfactor
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let U := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let d := Γ.act conjugator remote
  let R0 := QAt Γ cp.a ⊓ QAt Γ d
  let F := R0 ⊔ Subgroup.zpowers actor
  let Q := twoCoreIn (twoResidualIn F)
  let W := ⁅Subgroup.zpowers y ⊔ U,Q⁆ ⊔ Z
  let f := action.rangeRestrict
  let D := ⁅SectionOne.oddCore action.range,Subgroup.zpowers (f ⟨actor,hactor.1⟩)⁆ ⊔
    Subgroup.zpowers (f ⟨actor,hactor.1⟩)
  let Rbar := (R0.subgroupOf P).map f
  let V := U ⧸ Z.subgroupOf U
  let q : U →* V := QuotientGroup.mk' (Z.subgroupOf U)
  let supportBar := commutatorAction D V
  let support := (supportBar.comap q).map U.subtype
  let I := W ⊓ VAt Γ d
  let M := (W.subgroupOf U).map q
  let Ibar := (I.subgroupOf U).map q
  let T0 := conjugateClosure (Subgroup.zpowers (conjugator⁻¹*actor*conjugator)) (QAt Γ cp.a)
  let Tbar := (T0.subgroupOf P).map f
  have hseed := nine_four_noncentral_support_containment ctx hb remote hdistance actor hactor
    conjugator hconjugator hremote hne hgenerate A hA hcomm y hy hnoncentral hN hW
      action hact hkernel hinvolution hfactor
  have hgeom := nine_four_auxiliary_core_geometry ctx hb d actor hactor.1
  have hFP : F ≤ P := hgeom.1
  have hPU : P ≤ Subgroup.normalizer U := stabilizer_le_normalizer_v Γ cp.firstStep
  have hnorm := nine_four_auxiliary_normalization ctx hb d hremote actor hactor.1
    (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr (hA hy))
    ((Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hy) le_rfl).trans hcomm)
  have hnextZa : Z ≤ ZAt Γ cp.a :=
    ((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2 cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2
  have hZU : Z ≤ U := hnextZa.trans (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hZD : Z ≤ VAt Γ d := hnextZa.trans
    (nine_seven_neighbor_center_le_module Γ
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)))
  have hZW : Z ≤ W := le_sup_right
  have hZI : Z ≤ I := le_inf hZW hZD
  have hWU : W ≤ U := sup_le
    ((Subgroup.commutator_mono le_rfl ((twoCoreIn_le _).trans (twoResidualIn_le F))).trans
      hnorm.2) hZU
  have hSM : supportBar ≤ M := by
    have hh := Subgroup.map_mono (f:=q) (Subgroup.subgroupOf_mono U
      (show support ≤ W from hseed.2.1))
    rw [(Subgroup.lift_support_basic U Z hZU supportBar).2.2.2] at hh
    exact hh
  have hIM : Ibar ≤ M := Subgroup.map_mono (Subgroup.subgroupOf_mono U inf_le_left)
  have hidx : Ibar.relIndex M ≤ 2 := by
    have hbound := nine_four_auxiliary_intersection_index ctx hb d hremote
      (nine_four_moved_distance Γ cp.firstStep remote actor conjugator hactor.1 hconjugator hdistance)
      actor hactor.1 A hA hcomm y hy
    have hcount := (I.subgroupOf W).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show I ≤ W from inf_le_left)).toEquiv] at hcount
    change I.relIndex W * Nat.card I = Nat.card W at hcount
    have hi : I.relIndex W ≤ 2 := by
      change Nat.card W ≤ 2*Nat.card I at hbound
      have hpos : 0 < Nat.card I := Nat.card_pos
      nlinarith
    have hkerI : q.ker ≤ I.subgroupOf U := by
      rw [show q.ker = Z.subgroupOf U from QuotientGroup.ker_mk' _]
      exact Subgroup.subgroupOf_mono U hZI
    have hkerW : q.ker ≤ W.subgroupOf U := hkerI.trans (Subgroup.subgroupOf_mono U inf_le_left)
    change ((I.subgroupOf U).map q).relIndex ((W.subgroupOf U).map q) ≤ 2
    rw [Subgroup.relIndex_map_map,sup_eq_left.mpr hkerI,sup_eq_left.mpr hkerW,
      Subgroup.relIndex_subgroupOf hWU]
    exact hi
  have himage := nine_four_actor_closure_image ctx.toLocalContext remote actor hactor
    conjugator hconjugator hremote f hyp hfactor
  have hTD : Tbar ≤ Subgroup.normalizer D := himage.2.2
  have hRT : Rbar ≤ Subgroup.normalizer Tbar :=
    (Subgroup.map_mono (Subgroup.subgroupOf_mono P inf_le_left)).trans himage.2.1
  have hFW : F ≤ Subgroup.normalizer W :=
    (nine_four_auxiliary_residual_support ctx hb d hremote actor hactor.1 A hA hcomm y hy).1
  have hRM : ∀ r ∈ Rbar, ∀ v ∈ M, r • v ∈ M := by
    rintro r ⟨rP,hrP,rfl⟩ v ⟨wU,hwU,rfl⟩
    let moved : U := ⟨(rP:G)*(wU:G)*(rP:G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hPU rP.property) wU).mp wU.property⟩
    have hmoved : moved ∈ W.subgroupOf U :=
      (Subgroup.mem_normalizer_iff.mp (hFW (Subgroup.mem_sup_left hrP)) wU).mp hwU
    refine ⟨moved,hmoved,?_⟩
    change q moved = action rP (q wU)
    exact (hact rP wU).symm
  have hTfix : T0 ≤ Subgroup.centralizer (VAt Γ d : Set G) :=
    (nine_four_actor_closure_action ctx.toLocalContext remote actor hactor.2 conjugator hremote).1
  have hfix : ∀ t ∈ Tbar, ∀ v ∈ Ibar, t • v = v := by
    rintro t ⟨tP,htP,rfl⟩ v ⟨wU,hwU,rfl⟩
    change action tP (q wU) = q wU
    rw [hact]
    apply congrArg q
    apply Subtype.ext
    change (tP:G)*(wU:G)*(tP:G)⁻¹ = wU
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hTfix htP)) wU hwU.2
    change (wU:G)*(tP:G) = (tP:G)*(wU:G) at hcomm
    rw [← hcomm,mul_inv_cancel_right]
  have hkernelF : f.ker = pCore 2 P := (MonoidHom.ker_rangeRestrict action).trans hkernel
  have hinvF : _root_.IsInvolution (f ⟨actor,hactor.1⟩) :=
    ⟨fun heq => hinvolution.1 (congrArg Subtype.val heq),Subtype.ext hinvolution.2⟩
  have hactorImage := nine_four_conjugated_actor_image ctx.toLocalContext actor hactor.1
    conjugator hconjugator f action.rangeRestrict_surjective hkernelF hinvF
  obtain ⟨v,hv,hmove⟩ := factor_nonidentity_moves_support hyp D hfactor _ hactorImage.1 hactorImage.2.1.1
  have hRD : Rbar ≤ Subgroup.normalizer D :=
    SectionOne.oneSevenFactor_normalized_of_small_fixed_intersection hyp D Tbar Rbar hfactor
      M Ibar hSM hIM hidx hTD hRT hRM hfix ⟨_,hactorImage.2.2,v,hv,hmove⟩
  let derived := (commutator D).map D.subtype
  have hRDderived : Rbar ≤ Subgroup.normalizer derived := by
    intro r hr
    have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRD hr)
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    dsimp [derived]
    rw [Subgroup.map_subtype_commutator,Subgroup.map_commutator,hmap]
  let residual := twoResidualIn F
  have hresidualP : residual ≤ P := (twoResidualIn_le F).trans hFP
  have hresidualImage := nine_four_factor_residual_image ctx hb remote hdistance actor hactor
    conjugator hconjugator hremote hne hgenerate f action.rangeRestrict_surjective
      hkernelF hinvF hfactor
  have hresidualD : (residual.subgroupOf P).map f ≤ D := by
    rw [hresidualImage]
    apply (Subgroup.closure_le _).mpr
    rintro element ⟨r,d0,rfl⟩
    exact (Subgroup.map_subtype_le _) ((Subgroup.mem_normalizer_iff.mp
      (hRDderived r.property) d0).mp d0.property)
  have hsupportImage : commutatorAction ((residual.subgroupOf P).map f) V ≤ supportBar := by
    change commutatorAction ((residual.subgroupOf P).map f) V ≤ commutatorAction D V
    rw [commutatorAction_eq_closure,commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro element ⟨r,w,rfl⟩
    exact ⟨⟨r,hresidualD r.property⟩,w,rfl⟩
  have hcommImage : commutatorAction ((residual.subgroupOf P).map f) V =
      (⁅U,residual⁆.subgroupOf U).map q := by
    rw [← commutatorAction_map_actor_subtype action.range ((residual.subgroupOf P).map f),
      Subgroup.map_map]
    change commutatorAction ((residual.subgroupOf P).map action) V = _
    exact Subgroup.quotient_conjugation_commutatorAction_eq_image P U Z residual
      hPU hresidualP hN action hact
  have hcommLe : ⁅U,residual⁆ ≤ support := by
    have hcommU : ⁅U,residual⁆ ≤ U :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (hresidualP.trans hPU)
    rw [hcommImage] at hsupportImage
    have hh := Subgroup.map_le_iff_le_comap.mp hsupportImage
    have hm := Subgroup.map_mono (f:=U.subtype) hh
    rwa [Subgroup.map_subgroupOf_eq_of_le hcommU] at hm
  have hWsupport : W ≤ support :=
    (nine_four_auxiliary_residual_support ctx hb d hremote actor hactor.1 A hA hcomm y hy).2.trans
      (sup_le hcommLe hseed.1)
  have heq : W = support := le_antisymm hWsupport hseed.2.1
  change W = support ∧ Nat.card W = 8 ∧
    EAt Γ cp.firstStep ≤ Subgroup.normalizer W ∧ Rbar ≤ Subgroup.normalizer D
  exact ⟨heq,heq.symm ▸ hseed.2.2.1,heq.symm ▸ hseed.2.2.2,hRD⟩

end Stellmacher.SectionNine
