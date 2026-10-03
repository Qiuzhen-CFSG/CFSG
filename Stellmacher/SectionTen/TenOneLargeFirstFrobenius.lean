module
public import Stellmacher.SectionTen.TenOneLargeFirstQuotientFour
public import Theory.GroupTheory.FrobeniusTwentyRecognition
public import Stellmacher.SectionTen.TenOneLargeNineResidualExclusion
public import Stellmacher.SectionTen.TenOneLargeResidualJoinIndex

/-!
# The first residual is C₅ and the first core quotient is Frobenius of order twenty

In the actual large Section Ten branch, the literal image of E_first in
G_first/O₂(G_first) is cyclic of order five, and the quotient is a faithful
semidirect product C₅ ⋊ C₄. Both public theorems retain only the original
ambient context, offset-two middle vertex, and no-transvection hypothesis.

The actual source-(18) elementary quotient and its order sixteen supply the
normality, action and cardinal inputs to the elementary-nine exclusion.
The source-(14) alternatives therefore leave the terminal residual image C₅.
Its identification with the odd core of the literal terminal core quotient
transports along a single middle-stabilizer conjugation to the first quotient.
This transports both endpoint stabilizers and their two-cores together.

The first quotient is solvable and has trivial two-core. The separate
geometric four-divisibility theorem and the odd-core-five recognition theorem
produce its faithful C₅ ⋊ C₄ model. Composing the model isomorphism with the
canonical projection gives the exact native first-core kernel required by
QuotientIsFrobenius20. Prime-order cyclic recognition also supplies the actual
first residual-image model used in the subsequent source-(20) centralizer proof.

Source: Stellmacher (10.1)(19), Journal of Algebra 190 (1997), printed p.64.
No residual model, quotient order, or final core-index bound is an assumption.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}


private theorem first_oddCore_card_five_of_terminal
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hfive : Nat.card
      (((EAt ctx.Γ ctx.criticalPath.a').subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))))=5) :
    Nat.card (pPrimeCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep ⧸
      pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)))=5 := by
  let Pe:=GAt ctx.Γ ctx.criticalPath.a'
  let Pf:=GAt ctx.Γ ctx.criticalPath.firstStep
  let _ : (pCore 2 Pe).Normal := pCore_normal
  let _ : (pCore 2 Pf).Normal := pCore_normal
  let Xe:=Pe⧸pCore 2 Pe
  let Xf:=Pf⧸pCore 2 Pf
  let q:Pe→*Xe:=QuotientGroup.mk' (pCore 2 Pe)
  obtain ⟨_,hfirst,hterminal,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hcore : pCore 2 Pe ≤ q.ker := by
    change pCore 2 Pe ≤ (QuotientGroup.mk' (pCore 2 Pe)).ker
    rw [QuotientGroup.ker_mk']
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective (pCore 2 Pe)
  have hodd := nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
    ctx.criticalPath.a' middle (ctx.Γ.adjacent_symm hterminal) q
    hsurj hcore
  have hEnd : Nat.card (pPrimeCore 2 Xe)=5:=by
    change Nat.card (SectionOne.oddCore Xe)=5
    rw [←hodd]
    exact hfive
  obtain ⟨mover,hmove⟩:=(lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
  let aut:=MulAut.conj (mover:G)⁻¹
  have hPe : Pe.map aut.toMonoidHom=Pf:=by
    change conjugateBy (stabilizer ctx.Γ ctx.criticalPath.a') (mover:G)⁻¹=_
    rw [←stabilizer_act,hmove]
  let e:Pe≃*Pf:=(Pe.equivMapOfInjective aut.toMonoidHom aut.injective).trans
    (MulEquiv.subgroupCongr hPe)
  let eqv:Xe≃*Xf:=QuotientGroup.congr (pCore 2 Pe) (pCore 2 Pf) e (pCore_map_iso 2 e)
  have hmap:=pPrimeCore_map_iso 2 eqv
  change Nat.card (pPrimeCore 2 Xf)=5
  rw [←hmap]
  exact (Subgroup.card_map_of_injective (f:=eqv.toMonoidHom)
    (K:=pPrimeCore 2 Xe) eqv.injective).trans hEnd

private theorem first_frobenius_of_odd_core_five
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hfive : Nat.card (pPrimeCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep ⧸
      pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)))=5) :
    QuotientIsFrobenius20 (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let Q:=QAt ctx.Γ ctx.criticalPath.firstStep
  let X:=P⧸pCore 2 P
  let q:P→*X:=QuotientGroup.mk' (pCore 2 P)
  obtain ⟨_,hfirst,_,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  let edge:=P⊓GAt ctx.Γ middle
  let sylow:Sylow 2 edge:=default
  have hlocal:=edge_sectionThree_data ctx.sectionSeven ctx.Γ
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst)) sylow
  let _ : Group.IsSolvable P:=hlocal.2.2.2.1
  have hsolv : Group.IsSolvable X:=Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (pCore 2 P))
  have hcore : pCore 2 X=⊥:=by
    have hmap:=pCore_map_mk'_eq_of_normal_isPGroup (G:=P) (p:=2)
      (pCore 2 P) (pCore_isPGroup (G:=P) (p:=2))
    have hb : (pCore 2 P).map q=⊥:=by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
    exact hmap.symm.trans hb
  have hfour : 4∣Nat.card X:=ten_one_large_first_core_quotient_four_dvd ctx middle hpath hno
  obtain ⟨φ,hfaithful,⟨equiv⟩⟩:=
    exists_faithful_c5_semidirect_c4_of_odd_core_card_five hsolv hcore hfive hfour
  refine ⟨φ,hfaithful,equiv.toMonoidHom.comp q,
    equiv.surjective.comp (QuotientGroup.mk'_surjective _),?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective,QuotientGroup.ker_mk']
  change pCore 2 P=Q.subgroupOf P
  symm
  change (ctx.Γ.twoCoreAt ctx.criticalPath.firstStep).subgroupOf P=pCore 2 P
  rw [ctx.Γ.twoCoreAt_def,twoCoreIn,Subgroup.subgroupOf]
  change ((pCore 2 P).map P.subtype).comap P.subtype=pCore 2 P
  exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _


private theorem first_residual_five_of_odd_core_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hfive : Nat.card (pPrimeCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep ⧸
      pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)))=5) :
    Nonempty ((((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)))) ≃* C5) := by
  let P:=GAt ctx.Γ ctx.criticalPath.firstStep
  let X:=P⧸pCore 2 P
  let q:P→*X:=QuotientGroup.mk' (pCore 2 P)
  let Ebar:=((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf P).map q
  obtain ⟨_,hfirst,_,_⟩:=sectionTenOpeningGeometry ctx middle hpath
  have hsurj : Function.Surjective q:=QuotientGroup.mk'_surjective (pCore 2 P)
  have hcore : pCore 2 P≤q.ker:=by rw [QuotientGroup.ker_mk']
  have hodd:=nine_local_residual_image_eq_oddCore ctx.toLocalContext.toSectionNineLocalContext
    ctx.criticalPath.firstStep middle (ctx.Γ.adjacent_symm hfirst) q hsurj hcore
  have hcard : Nat.card Ebar=5:=by
    have hc : Nat.card (SectionOne.oddCore X)=5 := hfive
    rw [←hodd] at hc
    exact hc
  let _ : Fact (Nat.Prime 5):=⟨by decide⟩
  exact ⟨mulEquivOfPrimeCardEq hcard (by simp [C5])⟩


private theorem first_five_frobenius_of_terminal_not_nine
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hnotnine : ¬Nonempty ((((EAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a')).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.a')))) ≃* (C3×C3))) :
    Nonempty ((((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)))) ≃* C5) ∧
    QuotientIsFrobenius20 (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  obtain ⟨e⟩:=((ten_one_large_terminal_structure ctx middle hpath hno).1.resolve_left hnotnine)
  have hc : Nat.card (((EAt ctx.Γ ctx.criticalPath.a').subgroupOf
      (GAt ctx.Γ ctx.criticalPath.a')).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))))=5:=by
    rw [Nat.card_congr e.toEquiv]
    simp [C5]
  have hfive:=first_oddCore_card_five_of_terminal ctx middle hpath hc
  exact ⟨first_residual_five_of_odd_core_card ctx middle hpath hfive,
    first_frobenius_of_odd_core_five ctx middle hpath hno hfive⟩

private theorem terminal_residual_not_nine_from_context
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let P:=GAt ctx.Γ ctx.criticalPath.a'
    let E:=EAt ctx.Γ ctx.criticalPath.a'
    ¬Nonempty (((E.subgroupOf P).map (QuotientGroup.mk' (pCore 2 P)))≃*(C3×C3)) := by
  obtain ⟨hN,hel,hcomm⟩:=ten_one_large_residual_quotient_elementary ctx middle hpath hno
  let _:=hN
  let U:=twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
  let V:=VAt ctx.Γ ctx.criticalPath.a'
  have hindex:Nat.card U=16*Nat.card V:=ten_one_large_residual_quotient_card ctx middle hpath hno
  obtain ⟨_,C,hVC,hCU,_⟩:=ten_one_large_noncentral_chief_factor ctx middle hpath hno
  have hVU:V≤U:=hVC.trans hCU.le
  have hVcard:Nat.card V=32:=(ten_one_large_terminal_structure ctx middle hpath hno).2.1
  have hcard:Nat.card (U⧸V.subgroupOf U)=16:=by
    have hh:=Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv,hindex,hVcard] at hh
    change 16*32=Nat.card (U⧸V.subgroupOf U)*32 at hh
    omega
  exact ten_one_large_terminal_residual_not_nine ctx middle hpath hno hN hel hcard hcomm

private theorem first_five_frobenius_from_context
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    Nonempty ((((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)))) ≃* C5) ∧
    QuotientIsFrobenius20 (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  exact first_five_frobenius_of_terminal_not_nine ctx middle hpath hno
    (terminal_residual_not_nine_from_context ctx middle hpath hno)

public theorem ten_one_large_first_residual_five
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    Nonempty ((((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
      (GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)))) ≃* C5) := by
  exact (first_five_frobenius_from_context ctx middle hpath hno).1

public theorem ten_one_large_first_frobenius
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    QuotientIsFrobenius20 (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  exact (first_five_frobenius_from_context ctx middle hpath hno).2
end Stellmacher.SectionTen
