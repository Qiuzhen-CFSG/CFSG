module
public import Stellmacher.SectionTen.TenOneLargeMutualCentralizers
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Theory.GroupAction.CyclicQuotientSmallLayer


/-!
# Small neighborhood displacement forces centralization

In the no-transvection Section Ten configuration, an element of the middle
neighborhood group whose commutators with the first module lie in the
terminal center centralizes that first module. The original ambient context,
critical path and absence of first-module transvections are the only
geometric assumptions. The element need not be an involution.

The first core acts transitively on the other two middle neighbors, putting
the neighborhood group in the product of the terminal module and first core.
Write the element as vq in that product. The commutator identity and
[Vfirst,Qfirst]=Zfirst bound the displacement of v by the middle center of
order four. If v is outside the first core, the faithful quotient kernel
makes that displacement have quotient order two. An actual middle-stabilizer
swap contradicts the original no-transvection hypothesis. The element
therefore lies in the first core, and its commutators lie in both disjoint
endpoint centers, so they vanish.

Source: Stellmacher (10.1), printed pp.63–64, the use of (12) in the proof
of (16). This explicit transfer supplies the fixed-component centralization
needed by the source-(16) argument without assuming its final conclusion.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem neighborhood_le_terminal_sup_first_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    GeneratedNeighborhoodV ctx.Γ middle ≤
      VAt ctx.Γ ctx.criticalPath.a' ⊔ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  let V := VAt ctx.Γ ctx.criticalPath.a'
  obtain ⟨_,hfirst,hterminal,hends⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hQP : Q ≤ GAt ctx.Γ ctx.criticalPath.firstStep := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQmid : Q ≤ GAt ctx.Γ middle :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst)) default).2.2
  have hescape : ¬ Q ≤ QAt ctx.Γ middle := by
    intro hle
    apply nine_seven_residual_core_escapes_neighbor
      ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.firstStep middle
      ⟨1,ctx.Γ.act_one _⟩ (ctx.Γ.adjacent_symm hfirst)
    apply le_trans ?_ hle
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.firstStep) ≤
      ctx.Γ.twoCoreAt ctx.criticalPath.firstStep
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have htrans := (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
    (sectionTenOpeningData ctx middle hpath).quotient_model).punctured_transitivity
      ctx.criticalPath.firstStep hfirst Q (le_inf hQmid hQP) hescape
  apply sSup_le
  rintro D ⟨neighbor,hneighbor,rfl⟩
  by_cases heq : neighbor=ctx.criticalPath.firstStep
  · subst neighbor
    exact (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hshort _).trans le_sup_right
  obtain ⟨actor,hmove⟩ := htrans
    ⟨(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,hends.symm⟩ ⟨hneighbor,heq⟩
  change ctx.Γ.act (actor:G) ctx.criticalPath.a'=neighbor at hmove
  change v ctx.Γ neighbor ≤ V ⊔ Q
  rw [←hmove,v_act]
  rintro point ⟨v,hv,rfl⟩
  change (actor:G)⁻¹*v*((actor:G)⁻¹)⁻¹ ∈ V⊔Q
  exact (V⊔Q).mul_mem ((V⊔Q).mul_mem
    (Subgroup.mem_sup_right (Q.inv_mem actor.property)) (Subgroup.mem_sup_left hv))
    (by simpa using (show (actor:G) ∈ V⊔Q from Subgroup.mem_sup_right actor.property))

public theorem ten_one_neighborhood_actor_centralizes_first_of_small_commutator
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (actor : G) (hactor : actor ∈ GeneratedNeighborhoodV ctx.Γ middle)
    (hsmall : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers actor⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a') :
    actor ∈ Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep:Set G) := by
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  let A := VAt ctx.Γ ctx.criticalPath.firstStep
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
  let Zend := ZAt ctx.Γ ctx.criticalPath.a'
  let Zm := ZAt ctx.Γ middle
  let W := GeneratedNeighborhoodV ctx.Γ middle
  obtain ⟨_,hfirst,hterminal,hends⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hlong : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hWP : W ≤ P :=
    (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hlong middle).trans
      (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2)
  have hVW : V ≤ W := le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩
  have hVP : V ≤ P := hVW.trans hWP
  have hactorP : actor ∈ P := hWP hactor
  have hdata := nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext
    hshort ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩
  have hZcard : Nat.card Z=2 := hdata.1
  have hAQ : ⁅A,Q⁆=Z := hdata.2.1
  have hsplit := (sectionTenOpeningData ctx middle hpath).center_direct_product
  have hZmid : Z ≤ Zm := by change Z ≤ ZAt ctx.Γ middle; rw [hsplit.1]; exact le_sup_left
  have hZendmid : Zend ≤ Zm := by change Zend ≤ ZAt ctx.Γ middle; rw [hsplit.1]; exact le_sup_right
  let _ : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr (stabilizer_le_normalizer_q ctx.Γ _)
  have hfactor : (⟨actor,hactorP⟩:P) ∈ V.subgroupOf P ⊔ Q.subgroupOf P := by
    rw [←Subgroup.subgroupOf_sup hVP hQP]
    exact neighborhood_le_terminal_sup_first_core ctx middle hpath hactor
  obtain ⟨element,hv,coactor,hq,hvq⟩ := Subgroup.mem_sup_of_normal_right.mp hfactor
  have hvV : (element:G) ∈ V := hv
  have hqQ : (coactor:G) ∈ Q := hq
  have hveq : (element:G)=actor*(coactor:G)⁻¹ := by
    have hh : (element:G)*(coactor:G)=actor := congrArg Subtype.val hvq
    exact (eq_mul_inv_iff_mul_eq).mpr hh
  have hbound : ⁅A,Subgroup.zpowers (element:G)⁆ ≤ Zm := by
    apply Subgroup.commutator_zpowers_le_of_generator_normalizes A Zm (element:G)
      (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep element.property)
    intro point hpoint
    have hfirstComm : ⁅point,actor⁆ ∈ Zend :=
      hsmall (Subgroup.commutator_mem_commutator hpoint (Subgroup.mem_zpowers actor))
    have hcoreComm : ⁅point,(coactor:G)⁻¹⁆ ∈ Z := by
      rw [←hAQ]
      exact Subgroup.commutator_mem_commutator hpoint (Q.inv_mem hqQ)
    have hconj : actor*⁅point,(coactor:G)⁻¹⁆*actor⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp
        (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.firstStep hactorP) _).mp hcoreComm
    rw [hveq,commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using Zm.mul_mem (hZendmid hfirstComm) (hZmid hconj)
  have hvQ : (element:G) ∈ Q := by
    by_contra hout
    let D := ⁅A,Subgroup.zpowers (element:G)⁆ ⊔ Z
    have hDmid : D ≤ Zm := sup_le hbound hZmid
    have hDcard : Nat.card D=4 := by
      have hdiv : Nat.card D ∣ 2^2 := by
        norm_num
        rw [←(sectionTenOpeningData ctx middle hpath).center_card]
        exact Subgroup.card_dvd_of_le hDmid
      have hlarge : 2 < Nat.card D := by
        by_contra hn
        have heq : Z=D := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hZcard]; omega)
        exact hout ((hdata.2.2 element element.property).mp (le_sup_left.trans heq.symm.le))
      obtain ⟨n,hn,heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
      interval_cases n
      · norm_num only [Nat.pow_zero] at heq; omega
      · norm_num only [Nat.pow_one] at heq; omega
      · exact heq
    obtain ⟨mover,_,hmoveA,hmoveV⟩ := ten_one_neighbor_pair_alignment
      ctx middle hpath hterminal hfirst hends.symm
    let e := MulAut.conj mover⁻¹
    have hAmap : A.map e.toMonoidHom=V := by
      change (v ctx.Γ ctx.criticalPath.firstStep).map _=v ctx.Γ ctx.criticalPath.a'
      rw [←v_act,hmoveA]
    have hVmap : V.map e.toMonoidHom=A := by
      change (v ctx.Γ ctx.criticalPath.a').map _=v ctx.Γ ctx.criticalPath.firstStep
      rw [←v_act,hmoveV]
    have hZmap : Z.map e.toMonoidHom=Zend := by
      change (z ctx.Γ ctx.criticalPath.firstStep).map _=z ctx.Γ ctx.criticalPath.a'
      rw [←z_act,hmoveA]
    have hQmap : Q.map e.toMonoidHom=QAt ctx.Γ ctx.criticalPath.a' := by
      change (q ctx.Γ ctx.criticalPath.firstStep).map _=q ctx.Γ ctx.criticalPath.a'
      rw [←q_act,hmoveA]
    have hnewA : e (element:G) ∈ A := hVmap ▸ Subgroup.mem_map_of_mem e.toMonoidHom hvV
    have hnewOut : e (element:G) ∉ QAt ctx.Γ ctx.criticalPath.a' := by
      rw [←hQmap]
      intro hh
      obtain ⟨other,hother,heq⟩ := hh
      exact hout (e.injective heq ▸ hother)
    apply hno (e (element:G)) hnewA hnewOut
    have hDmap : D.map e.toMonoidHom=⁅V,Subgroup.zpowers (e (element:G))⁆⊔Zend := by
      rw [Subgroup.map_sup,Subgroup.map_commutator,hAmap,MonoidHom.map_zpowers,hZmap]
      rfl
    change Nat.card (⁅V,Subgroup.zpowers (e (element:G))⁆⊔Zend:Subgroup G)=2*Nat.card Zend
    rw [←hDmap,←hZmap,Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective e.injective,hDcard,hZcard]
  have hactorQ : actor ∈ Q := by
    have hh := Q.mul_mem hvQ hqQ
    have heq : (element:G)*(coactor:G)=actor := congrArg Subtype.val hvq
    rwa [heq] at hh
  have hcomm : ⁅A,Subgroup.zpowers actor⁆=⊥ := by
    apply bot_unique
    exact (le_inf ((Subgroup.commutator_mono le_rfl
      (Subgroup.zpowers_le.mpr hactorQ)).trans hAQ.le) hsmall).trans hsplit.2.1.eq_bot.le
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((Subgroup.commutator_comm _ _).trans hcomm) (Subgroup.mem_zpowers actor)

end Stellmacher.SectionTen
