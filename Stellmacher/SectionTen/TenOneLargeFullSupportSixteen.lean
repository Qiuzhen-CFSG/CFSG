module
public import Stellmacher.SectionTen.TenOneLargeChiefNoTransvection
public import Stellmacher.SectionTen.TenOneActorImageNontrivial
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# Order sixteen from full residual support and small first-actor displacement

For a finite nontrivial elementary-two action of the terminal stabilizer in
the large Section Ten branch, suppose its two-core is in the action kernel,
the residual has full support, and first-module actors outside that core
have displacement at most four. The acted-on group has order sixteen.
Irreducibility and faithfulness of the ambient stabilizer are unnecessary.

The canonical residual quotient has order five or nine by source (14).
The small residual-image theorem preserves that order in the supplied action.
The exact original terminal quotient action transports source-(13) commutator
generation to its range. Reduced (1.3), applied directly to this nontrivial
odd commutator in the faithful range action, gives support order four,
sixteen, or sixty-four. The residual orders exclude the cyclic-three and
extraspecial-twenty-seven cases. Full support gives the asserted group order.

This representation adapter proves the cardinal step in Stellmacher
(10.1)(18), printed p.64 of `refs/files/stellmacher-n-group.pdf`. Its caller
supplies the actual residual quotient and proves the displacement bound;
no desired quotient cardinality or irreducible model is assumed here.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_full_support_card_sixteen
    {X : Type u} [Group X] [Finite X] [IsElementaryAbelian 2 X] [Nontrivial X]
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (chief : GAt ctx.Γ ctx.criticalPath.a' →* MulAut X)
    (hcoreKernel : pCore 2 (GAt ctx.Γ ctx.criticalPath.a') ≤ chief.ker)
    (hfull : commutatorAction
      (((EAt ctx.Γ ctx.criticalPath.a').subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map chief) X = ⊤)
    (hdisp : ∀ actor : GAt ctx.Γ ctx.criticalPath.a',
      (actor:G)∈VAt ctx.Γ ctx.criticalPath.firstStep →
      (actor:G)∉QAt ctx.Γ ctx.criticalPath.a' →
      Nat.card (commutatorAction (Subgroup.zpowers (chief actor)) X) ≤ 4) :
    Nat.card X = 16 := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  have hres : ¬ E.subgroupOf P ≤ chief.ker := by
    intro htriv
    have hmap : (E.subgroupOf P).map chief = ⊥ := (Subgroup.map_eq_bot_iff _).mpr htriv
    have hbot : commutatorAction ((E.subgroupOf P).map chief) X = ⊥ := by
      apply bot_unique
      rw [commutatorAction_eq_closure,Subgroup.closure_le]
      rintro point ⟨a,v,rfl⟩
      have ha : (a:MulAut X)=1 := hmap.le a.property
      change v⁻¹ * (a:MulAut X) v ∈ (⊥:Subgroup X)
      rw [ha]
      simp only [MulAut.one_apply,inv_mul_cancel,Subgroup.one_mem]
    have hh : (⊤:Subgroup X)=⊥ := hfull.symm.trans hbot
    have hc := congrArg (fun L:Subgroup X=>Nat.card L) hh
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv,Subgroup.card_bot] at hc
    have : 1<Nat.card X := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    omega
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  obtain ⟨hN,hW,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halignment⟩
  let _ := hN
  let _ := hW
  obtain ⟨element,hactor,hout,hcases⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  obtain ⟨hcard,hselected⟩ := hcases.resolve_left (hno element hactor hout)
  let actor : P := ⟨element,
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 hactor⟩
  let q := QuotientGroup.mk' (pCore 2 P)
  let R0 := (twoResidualSubgroup P).map q
  let K := chief.range
  let f := chief.rangeRestrict
  let R := (twoResidualSubgroup P).map f
  have hnative : E.subgroupOf P=twoResidualSubgroup P := by
    dsimp only [E,P]
    rw [EAt,CosetGraphContext.e,ctx.Γ.twoResidualAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hcore : pCore 2 P ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hcoreKernel
  have hnot : ¬ twoResidualSubgroup P ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict,←hnative]
    exact hres
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  let edge := P ⊓ GAt ctx.Γ middle
  let sylow : Sylow 2 edge := default
  let Sedge := sylowTwoAmbient edge sylow
  have hlocal := edge_sectionThree_data ctx.sectionSeven ctx.Γ
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) sylow
  have hmodels : Nonempty (R0 ≃* (C3×C3)) ∨ Nonempty (R0 ≃* C5) := by
    have hh := (ten_one_large_terminal_structure ctx middle hpath hno).1
    change Nonempty (((E.subgroupOf P).map q) ≃* (C3×C3)) ∨
      Nonempty (((E.subgroupOf P).map q) ≃* C5) at hh
    rwa [hnative] at hh
  have hthree : Nat.card C3=3 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)).trans (by norm_num)
  have hfive : Nat.card C5=5 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 5) ≃ ZMod 5)).trans (by norm_num)
  have hnine : Nat.card (C3×C3)=9 := by rw [Nat.card_prod,hthree]
  have hsmall : Nat.card R0=5 ∨ IsElementaryAbelian 3 R0 := by
    rcases hmodels with ⟨e⟩ | ⟨e⟩
    · let e := e.some
      right
      refine { toIsMulCommutative := ⟨⟨fun a b => e.injective (by
        rw [map_mul,map_mul]; exact mul_comm _ _)⟩⟩, exponent_dvd_p := ?_ }
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro a
      apply e.injective
      rw [map_pow,map_one]
      exact (show ∀ z:C3×C3,z^3=1 from by decide) (e a)
    · exact Or.inl ((Nat.card_congr e.some.toEquiv).trans hfive)
  have hR0three : Nat.card R0≠3 := by
    intro hh
    rcases hmodels with ⟨e⟩ | ⟨e⟩
    · have hc := (Nat.card_congr e.some.toEquiv).trans hnine; omega
    · have hc := (Nat.card_congr e.some.toEquiv).trans hfive; omega
  have hRcard : Nat.card R=Nat.card R0 :=
    SectionThree.pSet_small_residual_image_card_eq Sedge hlocal.1 P hlocal.2.1 hlocal.2.2.2.1
      q (QuotientGroup.mk'_surjective _) f (by rw [QuotientGroup.ker_mk']; exact hcore) hnot hsmall
  have hodd : R=SectionOne.oddCore K := by
    have hh := nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.a' middle (ctx.Γ.adjacent_symm hterminal) f chief.rangeRestrict_surjective hcore
    change (E.subgroupOf P).map f = SectionOne.oddCore K at hh
    rwa [hnative] at hh
  have hkernelOld : action.rangeRestrict.ker ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict,hkernel]
    exact hcore
  let beta : action.range →* K := action.rangeRestrict.liftOfSurjective
    action.rangeRestrict_surjective ⟨f,hkernelOld⟩
  have hbeta (a:P) : beta (action.rangeRestrict a)=f a :=
    action.rangeRestrict.liftOfRightInverse_comp_apply (Function.surjInv action.rangeRestrict_surjective)
      (Function.rightInverse_surjInv action.rangeRestrict_surjective) ⟨f,hkernelOld⟩ a
  have hbetaHom : beta.comp action.rangeRestrict=f := MonoidHom.ext hbeta
  have hmapE : ((E.subgroupOf P).map action.rangeRestrict).map beta=R := by
    rw [Subgroup.map_map,hbetaHom,hnative]
  have hsource := (ten_one_large_residual_generation ctx middle hpath actor hactor
    action hformula hkernel hout hcard hselected hno).2.1
  have hgen : R=⁅R,Subgroup.zpowers (f actor)⁆ := by
    have hh := congrArg (Subgroup.map beta) hsource
    rw [Subgroup.map_commutator,MonoidHom.map_zpowers,hmapE,hbeta] at hh
    exact hh
  have hRsmall : Nat.card R=9 ∨ Nat.card R=5 := by
    rw [hRcard]
    rcases hmodels with ⟨e⟩ | ⟨e⟩
    · exact Or.inl ((Nat.card_congr e.some.toEquiv).trans hnine)
    · exact Or.inr ((Nat.card_congr e.some.toEquiv).trans hfive)
  have hRne : R ≠ ⊥ := by
    intro hb
    rw [hb,Subgroup.card_bot] at hRsmall
    omega
  have hRfull : commutatorAction R X=⊤ := by
    rw [←commutatorAction_map_actor_subtype K R]
    change commutatorAction (((twoResidualSubgroup P).map f).map K.subtype) X=⊤
    rw [Subgroup.map_map,show K.subtype.comp f=chief from rfl,←hnative]
    exact hfull
  have hnontriv : chief actor ≠ 1 :=
    ten_one_first_actor_image_ne_one ctx middle hpath actor hactor hout chief hres
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq).longer_case hshort).1
  have hactorSquare : actor ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (A:=VAt ctx.Γ ctx.criticalPath.firstStep) (actor:G) hactor)
  have hinv : _root_.IsInvolution (f actor) := ⟨
    fun hh => hnontriv (congrArg Subtype.val hh),by rw [←map_pow,hactorSquare,map_one]⟩
  have hcyclic : Nat.card (Subgroup.zpowers (f actor))=2 := by
    rw [Nat.card_zpowers,orderOf_eq_prime hinv.2 hinv.1]
  have hbound : Nat.card (commutatorAction (Subgroup.zpowers (f actor)) X)≤4 := by
    rw [←commutatorAction_map_actor_subtype K (Subgroup.zpowers (f actor)),MonoidHom.map_zpowers]
    exact hdisp actor hactor hout
  have hcount := (card_two_action_fixed_commutator_card_data (U:=X)
    (⟨f actor,Subgroup.mem_zpowers _⟩:Subgroup.zpowers (f actor))
    ⟨fun hh => hinv.1 (congrArg Subtype.val hh),Subtype.ext hinv.2⟩ hcyclic).1
  have hindex : Nat.card X≤4*Nat.card (FixedPoints.subgroup (Subgroup.zpowers (f actor)) X) := by
    rw [hcount,mul_comm 4]
    exact Nat.mul_le_mul_left _ hbound
  have hfaith : fixingSubgroup K (Set.univ:Set X)=⊥ := by
    apply bot_unique
    intro g hg
    apply Subtype.ext
    ext w
    exact ((mem_fixingSubgroup_iff K).mp hg) w (Set.mem_univ w)
  obtain ⟨prime,hprime,_,hpgroup⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    Sedge hlocal.1 P hlocal.2.1 hlocal.2.2.2.1 f hcore
  let _ : Fact prime.Prime := ⟨hprime⟩
  have hcop : Nat.Coprime 2 (Nat.card R) := by
    rw [hodd]
    exact pPrimeCore_coprime_card (G:=K) (p:=2)
  obtain hsmall | hsmall | hlarge :=
    SectionOne.involutionPGroup_smallIndex_classification_on_commutator
      R hRne prime hpgroup hcop (f actor) hinv hgen.symm hindex hfaith
  · obtain ⟨e⟩ := hsmall.2
    have hc := (Nat.card_congr e.toEquiv).trans hthree
    omega
  · have hc := hsmall.1
    rw [hRfull,Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
    exact hc
  · have hc := hlarge.2.2.2.2
    norm_num at hc
    omega
end Stellmacher.SectionTen
