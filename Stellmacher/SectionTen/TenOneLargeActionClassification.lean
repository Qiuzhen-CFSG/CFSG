module
public import Stellmacher.SectionTen.GeneratedContext
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineResidualOddCoreEquality
public import Stellmacher.SectionOne.LemmaOneThree
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupAction.ActorSubtypeCommutator
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Theory.GroupAction.FourElementInvolutionLines

/-!
# Classify the actual terminal rank-two canonical odd action

Fix the supplied conjugation action on the terminal quotient V/Z in the
Section Ten context. A prescribed first-module actor outside the terminal
core whose quotient displacement has order four determines a canonical
subgroup F=[O₂′(range), actor]. The literal action range satisfies the
Section One hypotheses, F is an odd p-group, and the exact three-way
conclusion of (1.3) holds for this F and this same action.

Solvability descends from the actual terminal stabilizer. Its exact two-core
kernel makes the range two-core-free, evaluation is faithful, and the
prescribed nontrivial involution makes its order even. Local (3.3) makes the
actual residual image an odd p-group; the proved residual/odd-core equality
therefore gives that property to F. The actor has square one because the
first module is elementary abelian. The quotient commutator image formula
converts the source order-four displacement into fixed-point index four,
so the proved (1.3) applies.

Source: Stellmacher (10.1), printed p.63/PDF p.53 of
`refs/files/stellmacher-n-group.pdf`, the application of (1.3) after (13).
This bounded step classifies the canonical F without identifying it with
the whole geometric residual or assuming the separate source (13) equality.
The later cyclic-three and extraspecial exclusions are not conclusions here.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u

private theorem relative_index_of_card
    {G : Type*} [Group G] [Finite G] (U Z C : Subgroup G)
    (hZU : Z ≤ U) (hCU : C ≤ U) [hN : (Z.subgroupOf U).Normal]
    (hcard : QuotientCardEq (C ⊔ Z) Z 4) : Z.relIndex C = 4 := by
  have hsup : C ⊔ Z ≤ U := sup_le hCU hZU
  have hindex : Z.relIndex (C ⊔ Z) = 4 := by
    have hmul := (Z.subgroupOf (C ⊔ Z)).index_mul_card
    have hZcard : Nat.card (Z.subgroupOf (C ⊔ Z)) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ C ⊔ Z from le_sup_right)).toEquiv
    rw [hZcard] at hmul
    change Z.relIndex (C ⊔ Z) * Nat.card Z = Nat.card (C ⊔ Z : Subgroup G) at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hmul.trans hcard)
  have heq := Subgroup.relIndex_sup_right (C.subgroupOf U) (Z.subgroupOf U)
  rw [← Subgroup.subgroupOf_sup hCU hZU, Subgroup.relIndex_subgroupOf hsup,
    Subgroup.relIndex_subgroupOf hCU] at heq
  exact heq ▸ hindex

public theorem ten_one_large_action_classification
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
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
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactor : (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hout : (actor : G) ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers (actor : G)⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 4) :
    let W := VAt ctx.Γ ctx.criticalPath.a' ⧸
      (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a')
    let induced := action.rangeRestrict actor
    let F := SectionOne.involutionCommutator action.range induced
    SectionOne.Hypotheses action.range W ∧
      (∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p F) ∧
      SectionOne.LemmaOneThreeConclusion action.range W induced F := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let W := U ⧸ Z.subgroupOf U
  let X := action.range
  let induced := action.rangeRestrict actor
  let F := SectionOne.involutionCommutator X induced
  have hshort : 1 < cp.length := by have := ctx.critical_length; change 1 < ctx.criticalPath.length; omega
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hterminal : Γ.adjacent cp.a' penultimate := by
    apply Γ.adjacent_symm
    have hh := cp.path_adj ⟨cp.length-1,by omega⟩
    convert hh using 1
    · rfl
    · rw [← cp.path_end]
      apply congrArg cp.path
      apply Fin.ext
      simp
      omega
  let sylow : Sylow 2 (P ⊓ GAt Γ penultimate : Subgroup G) := default
  let edgeSylow := sylowTwoAmbient (P ⊓ GAt Γ penultimate) sylow
  have hdata := edge_sectionThree_data ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminal) sylow
  have hsolv : Group.IsSolvable P := hdata.2.2.2.1
  let _ := hsolv
  let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
  have hpow : actor ^ 2 = 1 :=
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (actor : G) hactor)
  have hinvolution : _root_.IsInvolution induced := by
    constructor
    · intro heq
      have hk : actor ∈ action.ker := congrArg Subtype.val heq
      rw [hkernel] at hk
      apply hout
      change (actor : G) ∈ Γ.twoCoreAt cp.a'
      rw [Γ.twoCoreAt_def]
      exact Subgroup.mem_map_of_mem P.subtype hk
    · rw [← map_pow,hpow,map_one]
  let Y := Subgroup.zpowers induced
  have hYcard : Nat.card Y = 2 := by
    rw [Nat.card_zpowers,orderOf_eq_prime hinvolution.2 hinvolution.1]
  have hfaith : fixingSubgroup X (Set.univ : Set W) = ⊥ := by
    apply bot_unique
    intro mover hmover
    apply Subtype.ext
    ext point
    exact ((mem_fixingSubgroup_iff X).mp hmover) point (Set.mem_univ point)
  have hyp : SectionOne.Hypotheses X W := {
    G_solvable := Group.isSolvable_of_surjective action.rangeRestrict_surjective
    G_even := even_iff_two_dvd.mpr (by rw [← hYcard]; exact Y.card_subgroup_dvd_card)
    action_faithful := hfaith
    twoCore_eq_bot := pCore_range_eq_bot_of_ker_eq_pCore 2 action hkernel }
  have hcorekernel : pCore 2 P ≤ action.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,hkernel]
  obtain ⟨p,hp,hodd,himage⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    edgeSylow hdata.1 P hdata.2.1 hsolv action.rangeRestrict hcorekernel
  have hnative : (EAt Γ cp.a').subgroupOf P = twoResidualSubgroup P := by
    rw [EAt,CosetGraphContext.e,Γ.twoResidualAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hoddCore : IsPGroup p (SectionOne.oddCore X) := by
    have heq := nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
      cp.a' penultimate hterminal action.rangeRestrict action.rangeRestrict_surjective hcorekernel
    change ((EAt Γ cp.a').subgroupOf P).map action.rangeRestrict = SectionOne.oddCore X at heq
    rw [← heq,hnative]
    exact himage
  let _ : (SectionOne.oddCore X).Normal := by
    change (pPrimeCore 2 X).Normal
    infer_instance
  have hFp : IsPGroup p F := hoddCore.to_le (by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mp
    rw [Subgroup.normalizer_eq_top]
    exact le_top)
  let C := Subgroup.zpowers (actor : G)
  have hCP : C ≤ P := Subgroup.zpowers_le.mpr actor.property
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  obtain ⟨alignment,_,hterminalOrbit⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hcomm := (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort cp.a' ⟨alignment,hterminalOrbit⟩).2.1
  change ⁅U,QAt Γ cp.a'⁆ = Z at hcomm
  have hQP : QAt Γ cp.a' ≤ P := by
    change Γ.twoCoreAt cp.a' ≤ P
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZU : Z ≤ U := by
    rw [← hcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU)
  have hCU : ⁅U,C⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hCP.trans hPU)
  have hrelative : Z.relIndex ⁅U,C⁆ = 4 :=
    relative_index_of_card U Z ⁅U,C⁆ hZU hCU hindex
  have hCnative : C.subgroupOf P = Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hCP, MonoidHom.map_zpowers]
    rfl
  have hrank := Subgroup.quotient_conjugation_commutatorAction_card
    P U Z C hPU hCP hN action hformula
  rw [hCnative,MonoidHom.map_zpowers] at hrank
  have hrankY : Nat.card (commutatorAction Y W) = 4 := by
    rw [← commutatorAction_map_actor_subtype X Y,MonoidHom.map_zpowers]
    exact hrank.trans hrelative
  let _ : Nontrivial W := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    have hh := Subgroup.card_le_card_group (commutatorAction Y W)
    rw [hrankY] at hh
    omega
  let generator : Y := ⟨induced,Subgroup.mem_zpowers induced⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
    ⟨fun heq => hinvolution.1 (congrArg Subtype.val heq),Subtype.ext hinvolution.2⟩
  have hcount := (card_two_action_fixed_commutator_card_data
    (U := W) generator hgenerator hYcard).1
  have hfixedIndex : Nat.card W ≤ 4 * Nat.card (FixedPoints.subgroup Y W) := by
    rw [hrankY,Nat.mul_comm] at hcount
    exact hcount.le
  let _ : Fact p.Prime := ⟨hp⟩
  exact ⟨hyp,⟨p,hp,hodd,hFp⟩,SectionOne.lemma_one_three hyp induced hinvolution p hFp hfixedIndex⟩

end Stellmacher.SectionTen
