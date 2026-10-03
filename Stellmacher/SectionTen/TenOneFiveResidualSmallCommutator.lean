module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineResidualOddCoreEquality
public import Stellmacher.SectionOne.RankOneOddPGroupCyclicThree
public import Theory.GroupAction.CardTwoDisplacementInvolution
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Theory.GroupAction.ActorSubtypeCommutator
public import Theory.GroupTheory.PCoreKernelRange
/-!
# Small opposite-center commutators in the five-residual case

Assume the image of the actual first residual in the canonical first core
quotient is cyclic of order five. Every element of the first stabilizer
whose commutators with the first module lie in the terminal center
centralizes that module. No neighborhood membership, involution condition,
or no-transvection hypothesis is required of the element.

The literal first module modulo its central line has the first two-core
as its conjugation-action kernel. Its displacement image has order at most
two. If nontrivial, it makes the induced element an involution, and the
rank-one form of (1.3) makes its canonical odd commutator cyclic of order
three. The exact kernel identifies the odd-core image order with the
supplied residual order five, contradicting subgroup-order divisibility.
The original element therefore belongs to the first core. Its ambient
commutators now lie in both disjoint endpoint centers and hence vanish.
The supplied quotient normality witness and action formula are retained
through the image, kernel, and rank-one comparisons.

Source: the first reduction in Stellmacher (10.1)(20), Journal of Algebra
190 (1997), printed p.65 of `refs/files/stellmacher-n-group.pdf`. The
subsequent centralizer argument supplies its actual subgroup and commutator
bound separately; this theorem assumes none of its final conclusions.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}
public theorem ten_one_five_residual_small_commutator_centralizes_first
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hfive : Nonempty (((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep))) ≃* C5))
    (actor : G) (hactor : actor∈GAt ctx.Γ ctx.criticalPath.firstStep)
    (hsmall : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,zpowers actor⁆≤
      ZAt ctx.Γ ctx.criticalPath.a') :
    actor∈centralizer (VAt ctx.Γ ctx.criticalPath.firstStep:Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let Q := QAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let Zend := ZAt Γ cp.a'
  let D := ⁅V,zpowers actor⁆
  have hb : 1<cp.length := by change 1<ctx.criticalPath.length; rw [ctx.critical_length]; decide
  obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hdata := nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hb cp.firstStep ⟨1,Γ.act_one _⟩
  have hVQ : ⁅V,Q⁆=Z := hdata.2.1
  have hZendCard : Nat.card Zend=2 := by
    obtain ⟨align,_,halign⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
    exact (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
      hb cp.a' ⟨align,halign⟩).1
  have hPV : P≤normalizer (V:Set G) := stabilizer_le_normalizer_v Γ cp.firstStep
  have hDP : zpowers actor≤P := zpowers_le.mpr hactor
  have hDV : D≤V := le_normalizer_iff_commutator_le_left.mp (hDP.trans hPV)
  have hDcard : Nat.card D≤2 := (card_le_of_le hsmall).trans_eq hZendCard
  obtain ⟨hN,hW,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hb cp.firstStep ⟨1,Γ.act_one _⟩
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  let q := QuotientGroup.mk' (Z.subgroupOf V)
  let a : P := ⟨actor,hactor⟩
  have hcyclic : (zpowers actor).subgroupOf P=zpowers a := by
    apply Subgroup.map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hDP,MonoidHom.map_zpowers]
    rfl
  have hdisp : commutatorAction (zpowers (action a)) W=(D.subgroupOf V).map q := by
    have hh := quotient_conjugation_commutatorAction_eq_image P V Z (zpowers actor)
      hPV hDP hN action hformula
    rw [hcyclic,MonoidHom.map_zpowers] at hh
    exact hh
  have hrank : Nat.card (commutatorAction (zpowers (action a)) W)≤2 := by
    rw [hdisp]
    have hh : Nat.card ((D.subgroupOf V).map q)≤Nat.card (D.subgroupOf V) :=
      Nat.le_of_dvd Nat.card_pos (card_map_dvd _ q)
    rw [Nat.card_congr (subgroupOfEquivOfLe hDV).toEquiv] at hh
    exact hh.trans hDcard
  have hactorQ : actor∈Q := by
    by_contra hout
    have hane : action a≠1 := by
      intro ha
      have hh : a∈pCore 2 P := hkernel.le ha
      apply hout
      change actor∈Γ.twoCoreAt cp.firstStep
      rw [Γ.twoCoreAt_def]
      exact mem_map_of_mem P.subtype hh
    have hnon : commutatorAction (zpowers (action a)) W≠⊥ := by
      intro hbot
      have htrivial := actsTrivially_of_commutatorAction_eq_bot hbot
      apply hane
      ext w
      exact htrivial ⟨action a,mem_zpowers _⟩ w
    have hrankTwo : Nat.card (commutatorAction (zpowers (action a)) W)=2 := by
      have hh := (one_lt_card_iff_ne_bot _).mpr hnon
      omega
    let K := action.range
    let induced := action.rangeRestrict a
    let O := SectionOne.oddCore K
    have hcore : pCore 2 P≤action.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict,hkernel]
    let _ : O.Normal := by
      change (pPrimeCore 2 K).Normal
      infer_instance
    have hOeq : ((E.subgroupOf P).map action.rangeRestrict)=O :=
      nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
        cp.firstStep middle (Γ.adjacent_symm hfirst) action.rangeRestrict
        action.rangeRestrict_surjective hcore
    have hOcard : Nat.card O=5 := by
      rw [←hOeq]
      have hh : Nat.card ((E.subgroupOf P).map action.rangeRestrict)=
          Nat.card ((E.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P))) := by
        rw [←relIndex_ker,←relIndex_ker,MonoidHom.ker_rangeRestrict,hkernel,QuotientGroup.ker_mk']
      rw [hh]
      obtain ⟨e⟩ := hfive
      exact (Nat.card_congr e.toEquiv).trans
        ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 5) ≃ ZMod 5)).trans (by norm_num))
    have hinvolution := isInvolution_of_card_two_displacement (action a) hrankTwo
    have hinduced : _root_.IsInvolution induced :=
      ⟨fun hh => hinvolution.1 (congrArg Subtype.val hh),Subtype.ext hinvolution.2⟩
    have hIcard : Nat.card (zpowers induced)=2 := by
      rw [Nat.card_zpowers,orderOf_eq_prime hinduced.2 hinduced.1]
    have hfaith : fixingSubgroup K (Set.univ:Set W)=⊥ := by
      apply bot_unique
      intro g hg
      apply Subtype.ext
      ext w
      exact ((mem_fixingSubgroup_iff K).mp hg) w (Set.mem_univ w)
    let _ : Group.IsSolvable P := stabilizer_solvable_of_neighbor ctx.sectionSeven Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirst))
    have hyp : SectionOne.Hypotheses K W := {
      G_solvable := Group.isSolvable_of_surjective action.rangeRestrict_surjective
      G_even := even_iff_two_dvd.mpr (by rw [←hIcard]; exact (zpowers induced).card_subgroup_dvd_card)
      action_faithful := hfaith
      twoCore_eq_bot := pCore_range_eq_bot_of_ker_eq_pCore 2 action hkernel }
    let F := SectionOne.involutionCommutator K induced
    have hFO : F≤O := by
      change ⁅O,zpowers induced⁆≤O
      exact commutator_le_left _ _
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hOp : IsPGroup 5 O := IsPGroup.of_card (p:=5) (n:=1) (by simpa using hOcard)
    have hrankK : Nat.card (commutatorAction (zpowers induced) W)=2 := by
      rw [←commutatorAction_map_actor_subtype K (zpowers induced),MonoidHom.map_zpowers]
      exact hrankTwo
    obtain ⟨e⟩ := SectionOne.involutionCommutator_isCyclicThree_of_displacement_card_two
      hyp induced hinduced 5 (hOp.to_le hFO) hrankK
    have hFcard : Nat.card F=3 := (Nat.card_congr e.toEquiv).trans
      ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)).trans (by norm_num))
    have hdiv := card_dvd_of_le hFO
    rw [hFcard,hOcard] at hdiv
    norm_num at hdiv
  have hcomm : D=⊥ := by
    apply bot_unique
    exact (le_inf ((commutator_mono le_rfl (zpowers_le.mpr hactorQ)).trans hVQ.le) hsmall).trans
      (sectionTenOpeningData ctx middle hpath).center_direct_product.2.1.eq_bot.le
  exact commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans hcomm) (mem_zpowers actor)
end Stellmacher.SectionTen
