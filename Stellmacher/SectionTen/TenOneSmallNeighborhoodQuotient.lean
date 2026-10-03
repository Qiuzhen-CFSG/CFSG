module
public import Stellmacher.SectionTen.TenOneSmallNeighborhoodCard

/-!
# The elementary middle-neighborhood quotient in the small case

Under the order-eight first-module hypothesis, the actual generated middle
neighborhood U has elementary abelian quotient U/Zmiddle of order eight.
The theorem retains the literal quotient normality witness. This supplies
the module for the middle residual calculation in Stellmacher (10.1)(a1),
Journal of Algebra 190 (1997), printed p.60.

The proved derived identity U'=Zmiddle makes the quotient abelian. Local
transitivity carries the elementary first module to every neighbor module.
Their images generate U/Zmiddle, so the kernel of the quotient's squaring
homomorphism contains every generator and hence all of U. The established
orders |U|=32 and |Zmiddle|=4 give quotient order eight. No quotient action,
first quotient model, or extraspecial hypothesis is assumed.
-/
namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_neighborhood_quotient_elementary
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8) :
    ∃ hN : ((ZAt ctx.Γ middle).subgroupOf (GeneratedNeighborhoodV ctx.Γ middle)).Normal,
      let _ := hN
      IsElementaryAbelian 2
        (GeneratedNeighborhoodV ctx.Γ middle ⧸ (ZAt ctx.Γ middle).subgroupOf
          (GeneratedNeighborhoodV ctx.Γ middle)) ∧
      Nat.card (GeneratedNeighborhoodV ctx.Γ middle ⧸ (ZAt ctx.Γ middle).subgroupOf
        (GeneratedNeighborhoodV ctx.Γ middle)) = 8 := by
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVU {v : ctx.Γ.Vertex} (hv : v ∈ Neighborhood ctx.Γ middle) : VAt ctx.Γ v ≤ U :=
    le_sSup ⟨v,hv,rfl⟩
  have hZU : Z ≤ U :=
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst)).trans
      (hVU ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst))
  have hUQ : U ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hUP : U ≤ GAt ctx.Γ middle := hUQ.trans (by
    change ctx.Γ.twoCoreAt middle ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _)
  have hN : (Z.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (hUP.trans (stabilizer_le_normalizer_z ctx.Γ middle))
  let _ := hN
  let W := U ⧸ Z.subgroupOf U
  let π : U →* W := QuotientGroup.mk' (Z.subgroupOf U)
  have hderived : ⁅U,U⁆ = Z := by
    rw [← Subgroup.map_subtype_commutator U]
    exact (ten_one_small_derived ctx middle hpath hsmall).trans
      (ten_one_small_intersection ctx middle hpath hsmall)
  have hnative : commutator U ≤ Z.subgroupOf U := by
    intro x hx
    change (x:G) ∈ Z
    rw [← hderived,← Subgroup.map_subtype_commutator U]
    exact Subgroup.mem_map_of_mem U.subtype hx
  let _ : IsMulCommutative W :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hnative
  let _ : CommGroup W := IsMulCommutative.instCommGroup
  let square : W →* W := powMonoidHom 2
  let K := (square.ker.comap π).map U.subtype
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ ctx.criticalPath.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case (by omega)).1
  have helem (v : ctx.Γ.Vertex) (hv : v ∈ Neighborhood ctx.Γ middle) :
      IsElementaryAbelian 2 (VAt ctx.Γ v) := by
    obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
      middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) hv
    have hmap : VAt ctx.Γ v = (VAt ctx.Γ ctx.criticalPath.firstStep).map
        (MulAut.conj (mover:G)⁻¹).toMonoidHom := by
      rw [← hmove]
      exact v_act ctx.Γ mover ctx.criticalPath.firstStep
    rw [hmap]
    exact IsElementaryAbelian.map _
  have hUK : U ≤ K := by
    apply sSup_le
    rintro F ⟨v,hv,rfl⟩
    let _ := helem v hv
    intro x hx
    refine ⟨⟨x,hVU hv hx⟩,?_,rfl⟩
    change (π ⟨x,hVU hv hx⟩)^2 = 1
    rw [← map_pow]
    have hxpow : (⟨x,hVU hv hx⟩ : U)^2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=VAt ctx.Γ v) x hx)
    rw [hxpow,map_one]
  have hW : IsElementaryAbelian 2 W := ⟨by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro w
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
    obtain ⟨x,hx,hxu⟩ := hUK u.property
    have heq : x = u := Subtype.ext hxu
    change (π x)^2 = 1 at hx
    exact heq ▸ hx⟩
  have hUcard : Nat.card U = 32 := ten_one_small_neighborhood_card ctx middle hpath hsmall
  have hZcard : Nat.card Z = 4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hcard : Nat.card W = 8 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf U)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,hUcard,hZcard] at hh
    change 32 = Nat.card W * 4 at hh
    omega
  exact ⟨hN,hW,hcard⟩
end Stellmacher.SectionTen

