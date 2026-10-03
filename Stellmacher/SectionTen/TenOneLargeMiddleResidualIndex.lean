module
public import Stellmacher.SectionTen.TenOneLargeMiddleResidualEscape
public import Stellmacher.SectionTen.TenOneLargeMiddleQuotientBound
public import Stellmacher.ResidualCoreCommutator
public import Stellmacher.SectionTen.TenOneLargeResidualQuotientElementary
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SmallTwoGroupCubicClassification

/-!
# The middle residual join has index four in the large branch

For the original Section Ten no-transvection context, adjoining the middle
residual two-core to the generated middle neighborhood enlarges that
neighborhood by exactly four. The statement retains the actual subgroups
and requires no chosen quotient model or additional action hypothesis.

Write Q for the middle core, N for its generated neighborhood, and U for
the middle residual two-core. The preceding native cardinal bound gives
|Q/N| at most eight. The proved escape U not contained in N and residual
perfection force a nontrivial cubic automorphism in the actual residual
conjugation image. The small two-group cubic classification makes Q/N
either elementary abelian or quaternion of order eight.

In the quaternion case the image of the terminal residual core intersected
with Q has exponent two, by the actual terminal residual quotient theorem,
and hence is central. Its commutator containment, transported (7.6) normal
closure, and the exact quotient action force the entire middle residual to
act trivially modulo the center. The quaternion cubic coset calculation
contradicts this. In the elementary case U/(N intersect U) embeds in Q/N.
Its full residual action factors through a three-group. Coprime splitting
makes its common fixed subgroup trivial, so orbit counting gives an order
congruent to one modulo three. Nontriviality and the two-power bound eight
force order four. The normalized join index formula returns the literal
ambient subgroup statement.

Source: Stellmacher (10.1)(b2), Journal of Algebra 190 (1997), printed
pp.60 and 65, `refs/files/stellmacher-n-group.pdf`. This supplies the detailed
residual-action argument behind the final displayed middle quotient index.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
open scoped commutatorElement
universe u

private theorem exists_cubic_residual_image
    {E X:Type*} [Group E] [Finite E] [Group X] [Finite X]
    (f:E→*X) (hperfect:BenderSuzuki.External.hktPResidual 2 E=⊤)
    (hthree:IsPGroup 3 (E⧸pCore 2 E)) (hnon:¬∀e:E,f e=1) :
    ∃e:E,(f e)^3=1 ∧ f e≠1 := by
  have hdiv:Nat.card f.range∣Nat.card E:=card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨a,ha⟩:=hthree.exists_card_eq
  obtain ⟨b,hb⟩:=(pCore_isPGroup (p:=2) (G:=E)).exists_card_eq
  have hcount:=card_eq_card_quotient_mul_card_subgroup (pCore 2 E)
  rw [ha,hb] at hcount
  have hthreeDiv:3∣Nat.card f.range:=by
    by_contra hnot
    have hcop:Nat.Coprime (Nat.card f.range) 3:=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hnot).symm
    have hd:Nat.card f.range∣2^b:=
      (hcop.pow_right a).dvd_of_dvd_mul_left (hcount ▸ hdiv)
    obtain ⟨n,_,hn⟩:=(Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hfTwo:IsPGroup 2 f.range:=IsPGroup.of_card hn
    have hquotTwo:IsPGroup 2 (E⧸f.ker):=
      hfTwo.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
    have hkernel:=BenderSuzuki.External.hktPResidual_le f.ker inferInstance hquotTwo
    rw [hperfect] at hkernel
    exact hnon (fun e=>hkernel (mem_top e))
  let _ : Fact (Nat.Prime 3):=⟨Nat.prime_three⟩
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=f.range) 3 hthreeDiv
  obtain ⟨e,he⟩:=x.property
  refine ⟨e,?_,?_⟩
  · rw [he]
    exact congrArg Subtype.val (hx ▸ pow_orderOf_eq_one x)
  · intro h
    have hxone:x=1:=Subtype.ext (he.symm.trans h)
    rw [hxone,orderOf_one] at hx
    omega

private theorem middle_quotient_exists_cubic
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
    [hN : ((GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)).Normal]
    (action : GAt ctx.Γ middle →* MulAut
      (QAt ctx.Γ middle ⧸ (GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)))
    (hformula : ∀ actor : GAt ctx.Γ middle, ∀ point : QAt ctx.Γ middle,
      action actor (QuotientGroup.mk' ((GeneratedNeighborhoodV ctx.Γ middle).subgroupOf
        (QAt ctx.Γ middle)) point) = QuotientGroup.mk'
        ((GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle))
        ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
          (mem_normalizer_iff.mp (stabilizer_le_normalizer_q ctx.Γ middle actor.property) point).mp
            point.property⟩) :
    ∃ actor : GAt ctx.Γ middle, actor ∈ (EAt ctx.Γ middle).subgroupOf (GAt ctx.Γ middle) ∧
      (action actor)^3=1 ∧ action actor≠1 := by
  let M:=GAt ctx.Γ middle
  let Q:=QAt ctx.Γ middle
  let N:=GeneratedNeighborhoodV ctx.Γ middle
  let E:=EAt ctx.Γ middle
  let U:=twoCoreIn E
  let X:=Q⧸N.subgroupOf Q
  let q:=QuotientGroup.mk' (N.subgroupOf Q)
  have hE:E=twoResidualIn M:=ctx.Γ.twoResidualAt_def _
  have hEM:E≤M:=hE ▸ twoResidualIn_le M
  have hUQ:U≤Q:=by
    change twoCoreIn (ctx.Γ.twoResidualAt middle)≤ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hperfect:BenderSuzuki.External.hktPResidual 2 E=⊤:=by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual M
  have hodd:Odd (Nat.card (E⧸pCore 2 E)):=by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ middle
      ctx.criticalPath.firstStep
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (sectionTenOpeningGeometry ctx middle hpath).2.1)
      M le_rfl
  have hfull:⁅U,E⁆=U:=by
    have hh:=congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh.symm
  let f:E→*MulAut X:=action.comp (inclusion hEM)
  have hnon:¬∀e:E,f e=1:=by
    intro hzero
    have hUE:⁅U,E⁆≤N:=by
      rw [Subgroup.commutator_comm]
      apply Subgroup.commutator_le.mpr
      intro actor hactor point hpoint
      have hfix:action ⟨actor,hEM hactor⟩ (q ⟨point,hUQ hpoint⟩)=q ⟨point,hUQ hpoint⟩:=by
        have hh:=congrArg (fun aut:MulAut X=>aut (q ⟨point,hUQ hpoint⟩)) (hzero ⟨actor,hactor⟩)
        exact hh
      rw [hformula] at hfix
      have hh:=QuotientGroup.eq_iff_div_mem.mp hfix
      change actor*point*actor⁻¹/point∈N at hh
      simpa only [commutatorElement_def,div_eq_mul_inv] using hh
    exact ten_one_large_middle_residual_core_not_le_neighborhood ctx middle hpath hno
      (hfull.symm.le.trans hUE)
  obtain ⟨actor,hcube,hne⟩:=exists_cubic_residual_image f hperfect
    (ten_one_middle_residual_quotient_isThreeGroup ctx middle hpath) hnon
  exact ⟨inclusion hEM actor,actor.property,hcube,hne⟩

private theorem middle_quotient_not_quaternion
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
    [hN : ((GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)).Normal]
    (action : GAt ctx.Γ middle →* MulAut
      (QAt ctx.Γ middle ⧸ (GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)))
    (hformula : ∀ actor : GAt ctx.Γ middle, ∀ point : QAt ctx.Γ middle,
      action actor (QuotientGroup.mk' ((GeneratedNeighborhoodV ctx.Γ middle).subgroupOf
        (QAt ctx.Γ middle)) point) = QuotientGroup.mk'
        ((GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle))
        ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
          (mem_normalizer_iff.mp (stabilizer_le_normalizer_q ctx.Γ middle actor.property) point).mp
            point.property⟩)
    (model : (QAt ctx.Γ middle ⧸ (GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)) ≃* QuaternionGroup 2) : False := by
  let Γ:=ctx.Γ
  let cp:=ctx.criticalPath
  let M:=GAt Γ middle
  let Q:=QAt Γ middle
  let N:=GeneratedNeighborhoodV Γ middle
  let E:=EAt Γ middle
  let P:=GAt Γ cp.a'
  let R:=twoCoreIn (EAt Γ cp.a')
  let V:=VAt Γ cp.a'
  let X:=Q⧸N.subgroupOf Q
  let q:=QuotientGroup.mk' (N.subgroupOf Q)
  let L:=((center X).comap q).map Q.subtype
  have hMQ:M≤normalizer (Q:Set G):=stabilizer_le_normalizer_q Γ middle
  obtain ⟨_,_,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hQP:Q≤P:=((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
    middle cp.a' ((mem_neighborhood_iff_adjacent Γ).mpr hterminal) default).2.2
  have hRcore:R≤QAt Γ cp.a':=by
    change twoCoreIn (Γ.twoResidualAt cp.a')≤Γ.twoCoreAt cp.a'
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hRP:R≤P:=hRcore.trans (by
    change Γ.twoCoreAt cp.a'≤P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le P)
  have hRM:R≤M:=hRcore.trans (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
    cp.a' middle ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hterminal)) default).2.2)
  have hPR:P≤normalizer (R:Set G):=by
    have hEdef:EAt Γ cp.a'=twoResidualIn P:=Γ.twoResidualAt_def _
    have hEP:EAt Γ cp.a'≤P:=hEdef ▸ twoResidualIn_le P
    exact (normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal _ P hEP (hEdef ▸ twoResidualIn_normal P))
  have hVN:V≤N:=le_sSup ⟨_,(mem_neighborhood_iff_adjacent Γ).mpr hterminal,rfl⟩
  have hLq (x:Q): (x:G)∈L ↔ q x∈center X:=by
    constructor
    · rintro ⟨y,hy,heq⟩
      exact (Subtype.ext heq : y=x) ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  have hML:M≤normalizer (L:Set G):=by
    apply subgroup_le_normalizer_of_conj_mem
    intro actor point hpoint
    obtain ⟨source,hsource,rfl⟩:=hpoint
    apply (hLq ⟨(actor:G)*(source:G)*(actor:G)⁻¹,
      (mem_normalizer_iff.mp (hMQ actor.property) source).mp source.property⟩).mpr
    rw [←hformula]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩:=(action actor).surjective y
    simpa only [map_mul] using congrArg (action actor) (mem_center_iff.mp hsource z)
  have hRQ:⁅R,Q⁆≤R⊓Q:=by
    apply le_inf
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp (hQP.trans hPR)
    · exact le_normalizer_iff_commutator_le_right.mp (hRM.trans hMQ)
  obtain ⟨hVnormal,hVelem,_⟩:=ten_one_large_residual_quotient_elementary ctx middle hpath hno
  let _:=hVnormal
  let _:=hVelem
  have hRQL:R⊓Q≤L:=by
    intro point hpoint
    change point∈R ∧ point∈Q at hpoint
    have hpow:point^2∈V:=by
      have hp:((QuotientGroup.mk' (V.subgroupOf R)) ⟨point,hpoint.1⟩)^2=1:=by
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (R⧸V.subgroupOf R)) _
      rw [←map_pow] at hp
      have hh : (⟨point,hpoint.1⟩:R)^2∈V.subgroupOf R := (QuotientGroup.eq_one_iff _).mp hp
      exact hh
    have hx:(q ⟨point,hpoint.2⟩)^2=1:=by
      rw [←map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact hVN hpow
    apply (hLq ⟨point,hpoint.2⟩).mpr
    have hmodel:(model (q ⟨point,hpoint.2⟩))^2=1:=by rw [←map_pow,hx,map_one]
    have hcentral:∀x:QuaternionGroup 2,x^2=1→x∈center (QuaternionGroup 2):=by decide
    apply mem_center_iff.mpr
    intro y
    apply model.injective
    simpa only [map_mul] using mem_center_iff.mp (hcentral _ hmodel) (model y)
  let K:=commutatorPreimage M Q L
  have hRK:R≤K:=le_commutatorPreimage hRM (hRQ.trans hRQL)
  have hMK:M≤normalizer (K:Set G):=commutatorPreimage_normalized M Q L M hML
    le_normalizer hMQ hML
  have hEK:E≤K:=by
    obtain ⟨actor,hleft,hright⟩:=lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
    have hpen:cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩=middle:=by
      obtain ⟨i,hi,hmid⟩:=hpath
      have hindex:(⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩:Fin (cp.length+1))=i:=by
        apply Fin.ext
        have hlen:cp.length=3:=ctx.critical_length
        change cp.length-1=i.val
        omega
      rw [hindex]
      exact hmid
    have hmiddle:Γ.act actor cp.a=middle:=hleft.trans hpen
    let f:=MulAut.conj actor⁻¹
    have hMmap:(GAt Γ cp.a).map f.toMonoidHom=M:=
      (stabilizer_act Γ actor cp.a).symm.trans (congrArg (GAt Γ) hmiddle)
    have hPmap:(GAt Γ cp.firstStep).map f.toMonoidHom=P:=
      (stabilizer_act Γ actor cp.firstStep).symm.trans (congrArg (GAt Γ) hright)
    have hEmap:(EAt Γ cp.a).map f.toMonoidHom=E:=by
      change (Γ.twoResidualAt cp.a).map f.toMonoidHom=Γ.twoResidualAt middle
      rw [Γ.twoResidualAt_def,Γ.twoResidualAt_def]
      exact map_twoResidualAmbient_of_subgroup_image _ f.toMonoidHom M hMmap
    have hEfmap:(EAt Γ cp.firstStep).map f.toMonoidHom=EAt Γ cp.a':=by
      change (Γ.twoResidualAt cp.firstStep).map f.toMonoidHom=Γ.twoResidualAt cp.a'
      rw [Γ.twoResidualAt_def,Γ.twoResidualAt_def]
      exact map_twoResidualAmbient_of_subgroup_image _ f.toMonoidHom _ hPmap
    have hRmap:(twoCoreIn (EAt Γ cp.firstStep)).map f.toMonoidHom=R:=by
      change _=twoCoreIn (EAt Γ cp.a')
      rw [←hEfmap,twoCoreIn_map_equiv]
    rw [←hEmap]
    apply (map_mono (f:=f.toMonoidHom)
      (lemma_seven_six ctx.sectionSeven Γ cp).next_residual_core.2).trans
    apply map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨m,r,rfl⟩
    change f ((m:G)*(r:G)*(m:G)⁻¹)∈K
    rw [map_mul,map_mul,map_inv]
    have hmM:f (m:G)∈M:=hMmap ▸ mem_map_of_mem f.toMonoidHom m.property
    have hrR:f (r:G)∈R:=hRmap ▸ mem_map_of_mem f.toMonoidHom r.property
    exact (mem_normalizer_iff.mp (hMK hmM) _).mp (hRK hrR)
  have hEQ:⁅E,Q⁆≤L:=(commutator_mono hEK le_rfl).trans
    (commutator_commutatorPreimage_le M Q L hML)
  obtain ⟨actor,hactor,hcube,hne⟩:=middle_quotient_exists_cubic ctx middle hpath hno action hformula
  have hall:∀x:X,x∈center X:=by
    intro x
    apply QuaternionGroup.mem_center_of_central_difference_of_cube_eq_one_ne_one_of_equiv
      model (action actor) hcube hne
    obtain ⟨point,rfl⟩:=QuotientGroup.mk'_surjective (N.subgroupOf Q) x
    have hpoint:⁅(actor:G),(point:G)⁆∈L:=hEQ (commutator_mem_commutator hactor point.property)
    have hcommQ:⁅(actor:G),(point:G)⁆∈Q:=
      le_normalizer_iff_commutator_le_right.mp hMQ (commutator_mem_commutator actor.property point.property)
    have hc:q ⟨⁅(actor:G),(point:G)⁆,hcommQ⟩∈center X:=(hLq _).mp hpoint
    have heq:q ⟨⁅(actor:G),(point:G)⁆,hcommQ⟩=action actor (q point)*(q point)⁻¹:=by
      rw [hformula,←map_inv,←map_mul]
      congr 1
    rw [heq] at hc
    have heq2:(q point)⁻¹*action actor (q point)=action actor (q point)*(q point)⁻¹:=by
      have hh:=mem_center_iff.mp hc (q point)⁻¹
      apply mul_right_cancel
      simpa only [mul_assoc] using hh
    rw [heq2]
    exact hc
  have hbad:¬(QuaternionGroup.a 1:QuaternionGroup 2)*QuaternionGroup.xa 0=
      QuaternionGroup.xa 0*QuaternionGroup.a 1:=by decide
  apply hbad
  have hh:=congrArg model (mem_center_iff.mp (hall (model.symm (QuaternionGroup.xa 0)))
    (model.symm (QuaternionGroup.a 1)))
  simpa only [map_mul,model.apply_symm_apply] using hh

private theorem middle_residual_index_of_elementary
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
    [hN : ((GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)).Normal]
    (hEA : IsElementaryAbelian 2 (QAt ctx.Γ middle ⧸
      (GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle)))
    (hsmall : Nat.card (QAt ctx.Γ middle ⧸
      (GeneratedNeighborhoodV ctx.Γ middle).subgroupOf (QAt ctx.Γ middle))≤8) :
    QuotientCardEq (twoCoreIn (EAt ctx.Γ middle) ⊔ GeneratedNeighborhoodV ctx.Γ middle)
      (GeneratedNeighborhoodV ctx.Γ middle) 4 := by
  let M:=GAt ctx.Γ middle
  let Q:=QAt ctx.Γ middle
  let N:=GeneratedNeighborhoodV ctx.Γ middle
  let E:=EAt ctx.Γ middle
  let U:=twoCoreIn E
  let X:=Q⧸N.subgroupOf Q
  let q:=QuotientGroup.mk' (N.subgroupOf Q)
  let _:=hEA
  have hE:E=twoResidualIn M:=ctx.Γ.twoResidualAt_def _
  have hEM:E≤M:=hE ▸ twoResidualIn_le M
  have hUQ:U≤Q:=by
    change twoCoreIn (ctx.Γ.twoResidualAt middle)≤ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hUE:U≤E:=twoCoreIn_le E
  have hMN:M≤normalizer (N:Set G):=nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle
  have hEU:E≤normalizer (U:Set G):=(normal_subgroupOf_iff_le_normalizer hUE).mp (twoCoreIn_normal E)
  have hperfect:BenderSuzuki.External.hktPResidual 2 E=⊤:=by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual M
  have hodd:Odd (Nat.card (E⧸pCore 2 E)):=by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ middle
      ctx.criticalPath.firstStep
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (sectionTenOpeningGeometry ctx middle hpath).2.1)
      M le_rfl
  have hfull:⁅U,E⁆=U:=by
    have hh:=congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh.symm
  have hNU:(N.subgroupOf U).Normal:=normal_subgroupOf_of_le_normalizer (hUE.trans (hEM.trans hMN))
  let _:=hNU
  let Y:=U⧸N.subgroupOf U
  let f:U→*X:=q.comp (inclusion hUQ)
  have hker:f.ker=N.subgroupOf U:=by
    ext point
    change q (inclusion hUQ point)=1 ↔ (point:G)∈N
    exact QuotientGroup.eq_one_iff _
  let j:Y→*X:=QuotientGroup.lift (N.subgroupOf U) f hker.ge
  have hj:Function.Injective j:=(QuotientGroup.injective_lift_iff _ _ _).mpr hker.symm
  have hsmallY:Nat.card Y≤8:=(Nat.card_le_card_of_injective j hj).trans hsmall
  let _ : IsMulCommutative Y:=⟨⟨fun a b=>hj (by
    rw [map_mul,map_mul]
    exact (IsMulCommutative.is_comm (M:=X)).comm _ _)⟩⟩
  have hUU:⁅U,U⁆≤N:=by
    apply commutator_le.mpr
    intro a ha b hb
    have hc:⁅a,b⁆∈Q:=hUQ ((le_normalizer_iff_commutator_le_left.mp U.le_normalizer)
      (commutator_mem_commutator ha hb))
    have hbot:q ⟨⁅a,b⁆,hc⟩=1:=by
      have heq:q ⟨⁅a,b⁆,hc⟩=⁅q ⟨a,hUQ ha⟩,q ⟨b,hUQ hb⟩⁆:=by
        rw [←map_commutatorElement]
        congr 1
      rw [heq]
      have hcomm : Commute (q ⟨a,hUQ ha⟩) (q ⟨b,hUQ hb⟩) :=
        (IsMulCommutative.is_comm (M:=X)).comm _ _
      exact hcomm.commutator_eq
    exact (show (⟨⁅a,b⁆,hc⟩:Q)∈N.subgroupOf Q from (QuotientGroup.eq_one_iff _).mp hbot)
  obtain ⟨action,hformula,hkernel,hfullAction⟩:=exists_quotient_conjugation_full_action
    E U N E U hEU (hEM.trans hMN) hNU le_rfl hfull hUU
  have hkerCore:pCore 2 E≤action.ker:=by
    intro actor hactor
    exact hkernel (mem_map_of_mem E.subtype hactor)
  let descended:(E⧸pCore 2 E)→*action.range:=QuotientGroup.lift _ action.rangeRestrict
    (by simpa only [MonoidHom.ker_rangeRestrict] using hkerCore)
  have hsurj:Function.Surjective descended:=by
    intro actor
    obtain ⟨native,rfl⟩:=action.rangeRestrict_surjective actor
    exact ⟨QuotientGroup.mk' (pCore 2 E) native,rfl⟩
  have hthree:IsPGroup 3 action.range:=
    (ten_one_middle_residual_quotient_isThreeGroup ctx middle hpath).of_surjective descended hsurj
  have hUtwo:IsPGroup 2 U:=(pCore_isPGroup (p:=2) (G:=E)).map E.subtype
  have htwo:IsPGroup 2 Y:=hUtwo.to_quotient (N.subgroupOf U)
  have hfullRange:commutatorAction action.range Y=⊤:=by
    have hself:E.subgroupOf E=⊤:=by ext point;exact iff_true_intro point.property
    rw [hself,←MonoidHom.range_eq_map] at hfullAction
    exact hfullAction
  have hcop:Nat.Coprime (Nat.card action.range) (Nat.card Y):=by
    obtain ⟨a,ha⟩:=hthree.exists_card_eq
    obtain ⟨b,hb⟩:=htwo.exists_card_eq
    rw [ha,hb]
    exact ((by decide:Nat.Coprime 3 2).pow_left a).pow_right b
  have hfixed:FixedPoints.subgroup action.range Y=⊥:=by
    have hcompl:=isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G:=Y) (A:=action.range)
      (Group.isSolvable_of_comm fun a b=>(IsMulCommutative.is_comm (M:=Y)).comm a b) hcop inferInstance
    have hh:=hcompl.disjoint
    rw [hfullRange] at hh
    exact disjoint_top.mp hh
  have hmod:=hthree.card_modEq_card_fixedPoints Y
  change Nat.ModEq 3 (Nat.card Y) (Nat.card (FixedPoints.subgroup action.range Y)) at hmod
  rw [hfixed,card_bot] at hmod
  have hne:Nat.card Y≠1:=by
    intro hc
    have hi:N.relIndex U=1:=hc
    exact ten_one_large_middle_residual_core_not_le_neighborhood ctx middle hpath hno
      (relIndex_eq_one.mp hi)
  have hcount:Nat.card Y=4:=by
    obtain ⟨n,hn⟩:=htwo.exists_card_eq
    have hpos:0<Nat.card Y:=Nat.card_pos
    have hnle:n≤3:=by
      by_contra hh
      have hl:2^4≤2^n:=Nat.pow_le_pow_right (by decide) (by omega)
      omega
    unfold Nat.ModEq at hmod
    interval_cases n <;> norm_num at hn <;> omega
  have hNQ:N≤Q:=nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext
    (by change 2<ctx.criticalPath.length;rw [ctx.critical_length];decide) middle
  have hjoin:U⊔N≤Q:=sup_le hUQ hNQ
  have hi:N.relIndex U=4:=hcount
  have hidx:=relIndex_sup_right (U.subgroupOf Q) (N.subgroupOf Q)
  rw [←subgroupOf_sup hUQ hNQ,relIndex_subgroupOf hjoin,relIndex_subgroupOf hUQ,hi] at hidx
  have hm:=(N.subgroupOf (U⊔N)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show N≤U⊔N from le_sup_right)).toEquiv] at hm
  change N.relIndex (U⊔N)*Nat.card N=Nat.card (U⊔N:Subgroup G) at hm
  rw [hidx] at hm
  exact hm.symm

public theorem ten_one_large_middle_residual_join_index
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
    :
    QuotientCardEq (twoCoreIn (EAt ctx.Γ middle) ⊔ GeneratedNeighborhoodV ctx.Γ middle)
      (GeneratedNeighborhoodV ctx.Γ middle) 4 := by
  have hbound:=ten_one_large_middle_quotient_card_bound ctx middle hpath hno
  let M:=GAt ctx.Γ middle
  let Q:=QAt ctx.Γ middle
  let N:=GeneratedNeighborhoodV ctx.Γ middle
  have hQM:Q≤M:=by
    change ctx.Γ.twoCoreAt middle≤M
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le M
  have hMQ:M≤normalizer (Q:Set G):=stabilizer_le_normalizer_q ctx.Γ middle
  have hMN:M≤normalizer (N:Set G):=nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle
  have hNQ:N≤Q:=nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext
    (by change 2<ctx.criticalPath.length;rw [ctx.critical_length];decide) middle
  have hN:(N.subgroupOf Q).Normal:=normal_subgroupOf_of_le_normalizer (hQM.trans hMN)
  let _:=hN
  let X:=Q⧸N.subgroupOf Q
  have hsmall:Nat.card X≤8:=by
    have hh:=card_eq_card_quotient_mul_card_subgroup (N.subgroupOf Q)
    rw [Nat.card_congr (subgroupOfEquivOfLe hNQ).toEquiv] at hh
    change Nat.card Q=Nat.card X*Nat.card N at hh
    have hmul:Nat.card X*Nat.card N≤8*Nat.card N:=hh ▸ hbound
    exact Nat.le_of_mul_le_mul_right hmul Nat.card_pos
  obtain ⟨action,hformula⟩:=exists_quotient_conjugation_action M Q N hMQ hMN hN
  obtain ⟨actor,_,hcube,hne⟩:=middle_quotient_exists_cubic ctx middle hpath hno action hformula
  have htwo:IsPGroup 2 X:=(nine_seven_subgroup_isTwoGroup_of_le_vertex_core ctx.Γ middle Q le_rfl).to_quotient _
  rcases elementary_or_quaternion_of_small_two_group_cubic htwo hsmall (action actor) hcube hne with hEA | hmodel
  · exact middle_residual_index_of_elementary ctx middle hpath hno hEA hsmall
  · obtain ⟨model⟩ := hmodel
    exact (middle_quotient_not_quaternion ctx middle hpath hno action hformula model).elim

end Stellmacher.SectionTen
