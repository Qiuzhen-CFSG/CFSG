module
public import Stellmacher.SectionTen.TenOneSmallResidualQuotientElementary
public import Stellmacher.SectionEight.GeneratedEightSixSL2ResidualOdd
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Theory.GroupAction.SLTwoDerivedRankOne

/-!
# The residual-core orders in the small branch of Stellmacher (10.1)

For the actual small-module Section Ten configuration, the first residual
two-core modulo its neighbor module has order four. Since that module has
order eight, the residual core has order thirty-two.

The preceding geometric theorems provide the elementary quotient R/V and
show that the first core acts trivially. Its exact quotient-conjugation
action has full residual displacement because [R,E]=R. Descending along
the specified map P→SL2(2) identifies the residual image with the derived
three-subgroup. The generated middle neighborhood maps to an order-two
subgroup, and the previously computed commutator line retains order two.
The concrete SL2 derived-action theorem gives quotient order four. The
literal containment V≤R then converts the quotient count to the ambient
cardinality interface and the order-thirty-two corollary.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (10.1)(a),
printed p.60, immediately before the extraspecial local-structure conclusion.
No desired quotient cardinality or model of the residual core is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_residual_quotient_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    QuotientCardEq (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep))
      (VAt ctx.Γ ctx.criticalPath.firstStep) 4 := by
  let vertex := ctx.criticalPath.firstStep
  let P := GAt ctx.Γ vertex
  let Q := QAt ctx.Γ vertex
  let E := EAt ctx.Γ vertex
  let R := twoCoreIn E
  let V := VAt ctx.Γ vertex
  let U := GeneratedNeighborhoodV ctx.Γ middle
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : R ≤ P := (twoCoreIn_le E).trans hEP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := stabilizer_le_normalizer_v ctx.Γ vertex
  have hVR : V ≤ R := ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel
  obtain ⟨hN, helementary, hRQ⟩ := ten_one_small_residual_quotient_elementary
    ctx middle hpath hsmall hmodel
  let _ := hN
  let W := R ⧸ V.subgroupOf R
  let _ : IsElementaryAbelian 2 W := helementary
  have hperfect : BenderSuzuki.External.hktPResidual 2 E = ⊤ := by
    rw [hE]
    exact twoResidualAmbient_has_top_twoResidual P
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ
      vertex ctx.criticalPath.a
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm
        ctx.criticalPath.firstStep_adj)) P le_rfl
  have hfullR : ⁅R, E⁆ = R := by
    have hh := congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh.symm
  obtain ⟨action, haction, hQkernel, hfull⟩ :=
    Subgroup.exists_quotient_conjugation_full_action P R V E Q hPR hPV hN hEP hfullR hRQ
  obtain ⟨projection, hsurj, hkernel⟩ := hmodel
  have hkernelLe : projection.ker ≤ action.ker := hkernel ▸ hQkernel
  let quotientAction := QuotientGroup.lift projection.ker action hkernelLe
  let equiv := QuotientGroup.quotientKerEquivOfSurjective projection hsurj
  let actionSL2 : SL2Two →* MulAut W := quotientAction.comp equiv.symm.toMonoidHom
  have hcomp : actionSL2.comp projection = action := by
    ext actor point
    have heq : equiv (QuotientGroup.mk' projection.ker actor) = projection actor := rfl
    change quotientAction (equiv.symm (projection actor)) point = action actor point
    rw [← heq, equiv.symm_apply_apply]
    rfl
  have hnative : E.subgroupOf P = twoResidualSubgroup P := by
    change (ctx.Γ.twoResidualAt vertex).subgroupOf P = _
    rw [ctx.Γ.twoResidualAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hEimage : (E.subgroupOf P).map projection = commutator SL2Two := by
    rw [hnative, SectionThree.twoResidualSubgroup_eq_hktPResidual',
      hktPResidual_map_of_surjective' projection hsurj,
      ← SectionThree.twoResidualAmbient_top_eq_hktPResidual,
      SectionEight.eight_six_sl2_residual_eq_commutator]
  have hfullSL2 : commutatorAction ((commutator SL2Two).map actionSL2) W = ⊤ := by
    rw [← hEimage, Subgroup.map_map, hcomp]
    exact hfull
  obtain ⟨_, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hUcore : U ≤ QAt ctx.Γ middle :=
    nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle
  have hUP : U ≤ P := hUcore.trans
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle vertex
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) default).2.2)
  let D := (U.subgroupOf P).map projection
  have hDcard : Nat.card D = 2 := by
    change Nat.card ((U.subgroupOf P).map projection) = 2
    rw [← Subgroup.relIndex_ker, hkernel, Subgroup.relIndex_subgroupOf hUP]
    exact ten_one_small_neighbor_core_index ctx middle hpath ⟨projection, hsurj, hkernel⟩ hfirst
  have hline : Nat.card (commutatorAction (D.map actionSL2) W) = 2 := by
    change Nat.card (commutatorAction (((U.subgroupOf P).map projection).map actionSL2) W) = 2
    rw [Subgroup.map_map, hcomp,
      Subgroup.quotient_conjugation_commutatorAction_card P R V U hPR hUP hN action haction]
    exact ten_one_small_core_neighborhood_line ctx middle hpath hsmall ⟨projection, hsurj, hkernel⟩
  have hWcard : Nat.card W = 4 :=
    card_four_of_sl2_derived_full_rank_one actionSL2 hfullSL2 D hDcard hline
  have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf R)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVR).toEquiv] at hcount
  change Nat.card R = Nat.card W * Nat.card V at hcount
  rw [hWcard] at hcount
  exact hcount

public theorem ten_one_small_residual_core_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    Nat.card (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) = 32 := by
  have hcard := ten_one_small_residual_quotient_card ctx middle hpath hsmall hmodel
  change Nat.card (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) =
    4 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) at hcard
  rw [hsmall] at hcard
  exact hcard
end Stellmacher.SectionTen

