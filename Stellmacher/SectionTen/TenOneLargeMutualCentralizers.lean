module
public import Stellmacher.SectionTen.TenOneLargeTerminalStructure

/-!
# The two endpoint modules centralize one another precisely in their intersection

In the actual large Section Ten configuration, excluding first-module
transvections on the terminal quotient makes both mutual centralizers equal
to the literal endpoint-module intersection. No source-(15) conclusion or
neighborhood cardinality is assumed.

Source (14) gives terminal order thirty-two and intersection order eight.
The selected first-module actor has quotient displacement order four, hence
its fixed subgroup on the order-sixteen quotient has order four and its
ambient lift has order eight. The terminal centralizer of the first module
lies in that lift and contains the intersection, so both are equal. A single
middle-stabilizer actor swaps the two actual endpoint modules; conjugation
transports the equality in the reverse direction without reorienting the
context or assuming a new no-transvection condition.

Source: Stellmacher (10.1), printed p.63, equation (14), used in (16).
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u

public theorem ten_one_large_mutual_centralizers
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.a' : Set G) =
        VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a') ∧
    (VAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (VAt ctx.Γ ctx.criticalPath.firstStep : Set G) =
        VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a') := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let A := VAt Γ cp.firstStep
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let I := A ⊓ V
  obtain ⟨_,hVcard,hIcard⟩ := ten_one_large_terminal_structure ctx middle hpath hno
  have hshort : 1 < cp.length := by
    have := ctx.critical_length
    change 1 < ctx.criticalPath.length
    omega
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment,halignment⟩
  obtain ⟨hN,hW,action,hformula,_hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort cp.a' horbit
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  let projection := QuotientGroup.mk' (Z.subgroupOf V)
  have hdata := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort cp.a' horbit
  have hZcard : Nat.card Z=2 := hdata.1
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hQP : QAt Γ cp.a' ≤ P := by
    change Γ.twoCoreAt cp.a' ≤ P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le P
  have hZV : Z ≤ V := hdata.2.1.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPV))
  have hWcard : Nat.card W=16 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hZcard,hVcard] at hh
    change 32 = Nat.card W * 2 at hh
    omega
  obtain ⟨actor,hactor,hout,hcases⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  have hindex := (hcases.resolve_left (hno actor hactor hout)).1
  let actorP : P := ⟨actor,(lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2 hactor⟩
  let _ : IsElementaryAbelian 2 A :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
  have hsquare : action actorP ^ 2 = 1 := by
    rw [←map_pow,show actorP^2=1 from
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian actor hactor),map_one]
  let D := Subgroup.zpowers actor
  have hDP : D ≤ P := Subgroup.zpowers_le.mpr actorP.property
  have hDnative : D.subgroupOf P = Subgroup.zpowers actorP := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hDP,MonoidHom.map_zpowers]
    rfl
  have hrank := (Subgroup.quotient_conjugation_commutatorAction_card_iff
    P V Z D hPV hDP hZV action hformula 4).mpr hindex
  rw [hDnative,MonoidHom.map_zpowers] at hrank
  let fixed := FixedPoints.subgroup (Subgroup.zpowers (action actorP)) W
  have hfixedCard : Nat.card fixed=4 := by
    have hh := (MulAut.involution_fixed_displacement_card_data (action actorP) hsquare).1
    change Nat.card W=Nat.card fixed*_ at hh
    rw [hWcard,hrank] at hh
    omega
  let L := (fixed.comap projection).map V.subtype
  have hLcard : Nat.card L=8 := by
    have hh := (Subgroup.lift_support_basic V Z hZV fixed).2.2.1
    change Nat.card L=Nat.card fixed*Nat.card Z at hh
    rw [hfixedCard,hZcard] at hh
    exact hh
  have hcentralLift : V ⊓ Subgroup.centralizer (A:Set G) ≤ L := by
    intro point hpoint
    refine ⟨⟨point,hpoint.1⟩,?_,rfl⟩
    change projection ⟨point,hpoint.1⟩∈fixed
    intro mover
    have hcommute : actor*point=point*actor :=
      Subgroup.mem_centralizer_iff.mp hpoint.2 actor hactor
    have hfixed : (action actorP) • projection ⟨point,hpoint.1⟩ = projection ⟨point,hpoint.1⟩ := by
      change action actorP (projection ⟨point,hpoint.1⟩)=projection ⟨point,hpoint.1⟩
      rw [hformula]
      apply congrArg projection
      apply Subtype.ext
      change actor*point*actor⁻¹=point
      rw [hcommute,mul_inv_cancel_right]
    exact smul_eq_self_of_mem_zpowers mover.property hfixed
  have hAI : A ≤ Subgroup.centralizer (A:Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hIcentral : I ≤ V ⊓ Subgroup.centralizer (A:Set G) :=
    le_inf inf_le_right (inf_le_left.trans hAI)
  have hright : V ⊓ Subgroup.centralizer (A:Set G)=I := by
    apply (Subgroup.eq_of_le_of_card_ge hIcentral ?_).symm
    have hbound := Subgroup.card_le_of_le hcentralLift
    change Nat.card I=8 at hIcard
    rw [hLcard] at hbound
    rwa [hIcard]
  obtain ⟨_,hfirst,hterminal,hends⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,_hmover,hmoveA,hmoveV⟩ := ten_one_neighbor_pair_alignment
    ctx middle hpath hterminal hfirst hends.symm
  let equiv := MulAut.conj mover⁻¹
  have hAmap : A.map equiv.toMonoidHom=V := by
    change (v Γ cp.firstStep).map equiv.toMonoidHom=v Γ cp.a'
    rw [←v_act,hmoveA]
  have hVmap : V.map equiv.toMonoidHom=A := by
    change (v Γ cp.a').map equiv.toMonoidHom=v Γ cp.firstStep
    rw [←v_act,hmoveV]
  have hImap : I.map equiv.toMonoidHom=I := by
    change (A⊓V).map equiv.toMonoidHom=A⊓V
    rw [Subgroup.map_inf _ _ _ equiv.injective,hAmap,hVmap,inf_comm]
  have hCmap : (Subgroup.centralizer (V:Set G)).map equiv.toMonoidHom ≤
      Subgroup.centralizer (A:Set G) := by
    have hh := Subgroup.map_centralizer_le_centralizer_image (V:Set G) equiv.toMonoidHom
    change (Subgroup.centralizer (V:Set G)).map equiv.toMonoidHom ≤
      Subgroup.centralizer (V.map equiv.toMonoidHom:Set G) at hh
    rwa [hVmap] at hh
  have hleftLe : A ⊓ Subgroup.centralizer (V:Set G) ≤ I := by
    apply (Subgroup.map_le_map_iff_of_injective (f:=equiv.toMonoidHom) equiv.injective).mp
    rw [Subgroup.map_inf _ _ _ equiv.injective,hAmap,hImap,←hright]
    exact inf_le_inf_left V hCmap
  let _ : IsElementaryAbelian 2 V := by
    rw [←hAmap]
    exact IsElementaryAbelian.map equiv.toMonoidHom
  have hVV : V ≤ Subgroup.centralizer (V:Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact ⟨le_antisymm hleftLe (le_inf inf_le_left (inf_le_right.trans hVV)),hright⟩

end Stellmacher.SectionTen
