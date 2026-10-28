module
public import Stellmacher.SectionTen.TenOneLargeTerminalFullSupport
public import Stellmacher.SectionTen.TenOneCommonIntersection
public import Theory.GroupAction.InvolutionDisplacementCard
public import Theory.GroupAction.QuotientDisplacementCard
public import Theory.GroupAction.SubgroupQuotientSupportLift

/-!
# The terminal and intersection orders in source (14)

In the actual no-transvection Section Ten configuration, a terminal odd-core
commutator support of order sixteen forces the terminal module to have order
thirty-two and the endpoint-module intersection to have order eight. The
support cardinality is the small alternative of (1.3) after source (13);
neither resulting ambient cardinality is supplied as a hypothesis.

Full terminal residual support identifies the quotient module with this
sixteen-element support, and its central denominator has order two. The
selected first-module actor has quotient displacement order four, so its
fixed subgroup on the quotient has order four. Its ambient lift has order
eight and contains the endpoint intersection because the first module is
elementary abelian. Conversely the selected displacement joined with the
terminal center has order eight and lies in the intersection: its commutator
lies in the neighborhood derived subgroup, and the middle-center splitting
places the terminal center in both endpoint modules. These bounds give the
exact intersection order.

Source: Stellmacher (10.1), printed p.63, equation (14). The supplied quotient
normality instance, elementary quotient instance, action, conjugation formula
and two-core kernel are retained throughout.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u

public theorem ten_one_large_terminal_cardinalities
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
    (hkernel : action.ker = pCore 2 (GAt ctx.Γ ctx.criticalPath.a'))
    (hsupport : Nat.card (commutatorAction (SectionOne.oddCore action.range)
      (VAt ctx.Γ ctx.criticalPath.a' ⧸
        (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf (VAt ctx.Γ ctx.criticalPath.a'))) = 16) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 32 ∧
      Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let A := VAt Γ cp.firstStep
  let I := A ⊓ V
  let W := V ⧸ Z.subgroupOf V
  let projection := QuotientGroup.mk' (Z.subgroupOf V)
  have hshort : 1 < cp.length := by
    have := ctx.critical_length
    change 1 < ctx.criticalPath.length
    omega
  have hWcard : Nat.card W = 16 := by
    have hh := hsupport
    rw [ten_one_large_terminal_oddCore_full_support ctx middle hpath hno action hformula hkernel,
      Nat.card_congr Subgroup.topEquiv.toEquiv] at hh
    exact hh
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hdata := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩
  have hZcard : Nat.card Z = 2 := hdata.1
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hQP : QAt Γ cp.a' ≤ P := by
    change Γ.twoCoreAt cp.a' ≤ P
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le P
  have hZV : Z ≤ V := hdata.2.1.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPV))
  have hVcard : Nat.card V = 32 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hZcard,hWcard] at hh
    exact hh
  obtain ⟨actor,hactor,hout,hcases⟩ := ten_one_quotient_commutator_actor ctx middle hpath
  have hindex := (hcases.resolve_left (hno actor hactor hout)).1
  let actorP : P := ⟨actor,(lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2 hactor⟩
  let _ : IsElementaryAbelian 2 A :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
  have hsquare : action actorP ^ 2 = 1 := by
    rw [← map_pow,show actorP ^ 2 = 1 from
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
  have hfixedCard : Nat.card fixed = 4 := by
    have hh := (MulAut.involution_fixed_displacement_card_data (action actorP) hsquare).1
    change Nat.card W = Nat.card fixed * _ at hh
    rw [hWcard,hrank] at hh
    omega
  let L := (fixed.comap projection).map V.subtype
  have hLcard : Nat.card L = 8 := by
    have hh := (Subgroup.lift_support_basic V Z hZV fixed).2.2.1
    change Nat.card L = Nat.card fixed * Nat.card Z at hh
    rw [hfixedCard,hZcard] at hh
    exact hh
  have hIL : I ≤ L := by
    intro point hpoint
    refine ⟨⟨point,hpoint.2⟩,?_,rfl⟩
    change projection ⟨point,hpoint.2⟩ ∈ fixed
    intro mover
    have hcommute : actor * point = point * actor := setLike_mul_comm (s := A) hactor hpoint.1
    have hfixed : (action actorP) • projection ⟨point,hpoint.2⟩ = projection ⟨point,hpoint.2⟩ := by
      change action actorP (projection ⟨point,hpoint.2⟩) = projection ⟨point,hpoint.2⟩
      rw [hformula]
      apply congrArg projection
      apply Subtype.ext
      change actor * point * actor⁻¹ = point
      rw [hcommute,mul_inv_cancel_right]
    exact smul_eq_self_of_mem_zpowers mover.property hfixed
  have hIupper : Nat.card I ≤ 8 := hLcard ▸ Subgroup.card_le_of_le hIL
  let C := ⁅V,D⁆ ⊔ Z
  have hCcard : Nat.card C = 8 := by
    change Nat.card C = 4 * Nat.card Z at hindex
    simpa only [hZcard] using hindex
  let Wnext := GeneratedNeighborhoodV Γ middle
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hVW : V ≤ Wnext := le_sSup ⟨_,(mem_neighborhood_iff_adjacent Γ).mpr hterminal,rfl⟩
  have hAW : A ≤ Wnext := le_sSup ⟨_,(mem_neighborhood_iff_adjacent Γ).mpr hfirst,rfl⟩
  have hcommI : ⁅V,D⁆ ≤ I := by
    have hcomm : ⁅V,D⁆ ≤ DerivedAmbient Wnext := by
      rw [show DerivedAmbient Wnext = ⁅Wnext,Wnext⁆ from Subgroup.map_subtype_commutator Wnext]
      exact Subgroup.commutator_mono hVW ((Subgroup.zpowers_le.mpr hactor).trans hAW)
    exact hcomm.trans (ten_one_generated_derived_le_intersection ctx middle hpath)
  have hZmiddle : Z ≤ ZAt Γ middle := by
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_right
  have hmiddleA : ZAt Γ middle ≤ A := by
    change ZAt Γ middle ≤ VAt Γ cp.firstStep
    rw [VAt,v,Γ.vAt_def]
    exact le_sSup ⟨middle,(mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirst),rfl⟩
  have hCI : C ≤ I := sup_le hcommI (le_inf (hZmiddle.trans hmiddleA) hZV)
  have hIlower : 8 ≤ Nat.card I := hCcard ▸ Subgroup.card_le_of_le hCI
  exact ⟨hVcard,le_antisymm hIupper hIlower⟩

end Stellmacher.SectionTen
