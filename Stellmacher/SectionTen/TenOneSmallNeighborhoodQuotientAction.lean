module
public import Stellmacher.SectionTen.TenOneSmallNeighborhoodQuotient
public import Stellmacher.SectionNine.NineSevenCommutatorActionBridge
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Stellmacher.SectionEight.GeneratedEightSixSL2ResidualOdd
public import Theory.GroupTheory.Commutator.ActionTriviality
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupAction.ThreeOnElementaryEight

/-!
# The residual action on the elementary middle-neighborhood quotient

For the actual order-eight first-module case, U/Zmiddle is elementary of
order eight and carries the literal middle-stabilizer conjugation action.
The middle core lies in its kernel. The actual image of the middle residual
has order three, acts nontrivially, and has displacement of order four.
The quotient normality witness and exact action formula are retained for
the subsequent identification of the residual-core quotient.

Each neighbor module has order eight, so its quotient by Zmiddle has
order two. The proved neighbor/core commutator bound shows that the middle
core fixes every generating image. Trivial residual action would normalize
the first module, whereas residual neighbor transitivity carries that module
to the distinct terminal module. Descent through the actual middle SL2(2)
quotient identifies the residual image as a nontrivial image of its derived
order-three group. The elementary-eight/order-three action theorem then
gives displacement order four. No faithful action or displacement order is
assumed, and the first local quotient model is not required.

Source: Stellmacher (10.1)(a1), Journal of Algebra 190 (1997), printed p.60,
the small-case middle-residual calculation after the quaternion recognition.
-/
namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_neighborhood_quotient_action
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8) :
    let M := GAt ctx.Γ middle
    let U := GeneratedNeighborhoodV ctx.Γ middle
    let Z := ZAt ctx.Γ middle
    ∃ hN : (Z.subgroupOf U).Normal,
      let _ := hN
      ∃ hMU : M ≤ Subgroup.normalizer (U : Set G),
        IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U) ∧
        Nat.card (U ⧸ Z.subgroupOf U) = 8 ∧
        ∃ action : M →* MulAut (U ⧸ Z.subgroupOf U),
          (∀ actor : M, ∀ point : U,
            action actor (QuotientGroup.mk' (Z.subgroupOf U) point) =
              QuotientGroup.mk' (Z.subgroupOf U)
                ⟨(actor:G)*(point:G)*(actor:G)⁻¹,
                  (Subgroup.mem_normalizer_iff.mp (hMU actor.property) point).mp point.property⟩) ∧
          (QAt ctx.Γ middle).subgroupOf M ≤ action.ker ∧
          Nat.card (((EAt ctx.Γ middle).subgroupOf M).map action) = 3 ∧
          commutatorAction (((EAt ctx.Γ middle).subgroupOf M).map action)
            (U ⧸ Z.subgroupOf U) ≠ ⊥ ∧
          Nat.card (commutatorAction (((EAt ctx.Γ middle).subgroupOf M).map action)
            (U ⧸ Z.subgroupOf U)) = 4 := by
  let M := GAt ctx.Γ middle
  let Q := QAt ctx.Γ middle
  let E := EAt ctx.Γ middle
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hopen := sectionTenOpeningData ctx middle hpath
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVU {v : ctx.Γ.Vertex} (hv : v ∈ Neighborhood ctx.Γ middle) : VAt ctx.Γ v ≤ U :=
    le_sSup ⟨v,hv,rfl⟩
  have hVfirstU : V ≤ U := hVU ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
  have hZV : Z ≤ V := nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst)
  have hE : E = twoResidualIn M := ctx.Γ.twoResidualAt_def _
  have hEM : E ≤ M := hE ▸ twoResidualIn_le M
  have hMU : M ≤ Subgroup.normalizer (U : Set G) :=
    nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle
  have hMZ : M ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z ctx.Γ middle
  obtain ⟨hN,hW,hWcard⟩ := ten_one_small_neighborhood_quotient_elementary ctx middle hpath hsmall
  let _ := hN
  let W := U ⧸ Z.subgroupOf U
  let π : U →* W := QuotientGroup.mk' (Z.subgroupOf U)
  obtain ⟨action,hact⟩ := Subgroup.exists_quotient_conjugation_action M U Z hMU hMZ hN
  have hVcard (v : ctx.Γ.Vertex) (hv : v ∈ Neighborhood ctx.Γ middle) :
      Nat.card (VAt ctx.Γ v) = 8 := by
    obtain ⟨a,ha⟩ := (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) hv
    rw [← ha,VAt,v_act,Subgroup.card_map_of_injective (MulAut.conj (a:G)⁻¹).injective]
    exact hsmall
  have hQker : Q.subgroupOf M ≤ action.ker := by
    intro a ha
    let K := (((action a).toMonoidHom.comp π).eqLocus π).map U.subtype
    have hUK : U ≤ K := by
      apply sSup_le
      rintro F ⟨v,hv,rfl⟩
      have hcomm : ⁅VAt ctx.Γ v,Q⁆ ≤ Z :=
        nine_seven_neighbor_core_module_commutator_le_center ctx.toLocalContext.toSectionNineLocalContext
          ((mem_neighborhood_iff_adjacent ctx.Γ).mp hv) (hVcard v hv) hopen.center_card
      intro x hx
      refine ⟨⟨x,hVU hv hx⟩,?_,rfl⟩
      change action a (π ⟨x,hVU hv hx⟩) = π ⟨x,hVU hv hx⟩
      rw [hact]
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (a:G)*x*(a:G)⁻¹/x ∈ Z
      have hh : ⁅(a:G),x⁆ ∈ Z := by
        rw [Subgroup.commutator_comm] at hcomm
        exact hcomm (Subgroup.commutator_mem_commutator ha hx)
      simpa only [commutatorElement_def,div_eq_mul_inv] using hh
    apply MonoidHom.mem_ker.mpr
    ext w
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
    obtain ⟨x,hx,hxu⟩ := hUK u.property
    have heq : x = u := Subtype.ext hxu
    change action a (π x) = π x at hx
    exact heq ▸ hx
  let F := (E.subgroupOf M).map action
  have hnontrivial : commutatorAction F W ≠ ⊥ := by
    intro hbot
    have htrivial := actsTrivially_of_commutatorAction_eq_bot hbot
    have hEV : E ≤ Subgroup.normalizer (V : Set G) := by
      apply Subgroup.le_normalizer_iff.mpr
      intro a ha x hx
      let aM : M := ⟨a,hEM ha⟩
      let xU : U := ⟨x,hVfirstU hx⟩
      have hfix := htrivial ⟨action aM,Subgroup.mem_map_of_mem action ha⟩ (π xU)
      change action aM (π xU) = π xU at hfix
      rw [hact] at hfix
      have hh := QuotientGroup.eq_iff_div_mem.mp hfix
      change a*x*a⁻¹/x ∈ Z at hh
      have hm := V.mul_mem (hZV hh) hx
      simpa only [div_mul_cancel] using hm
    obtain ⟨a,ha,hmove⟩ := nine_seven_residual_neighbor_transitive ctx.sectionSeven ctx.Γ
      middle ctx.criticalPath.firstStep ctx.criticalPath.a' hfirst hterminal
    have hmap : V.map (MulAut.conj a⁻¹).toMonoidHom = V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEV (E.inv_mem ha))
    have heq : VAt ctx.Γ ctx.criticalPath.a' = V := by
      rw [← hmove,VAt,v_act]
      exact hmap
    apply hopen.first_noncontainment
    change V ≤ QAt ctx.Γ ctx.criticalPath.a'
    rw [← heq]
    exact neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hb _
  obtain ⟨projection,hsurj,hkernel⟩ := hopen.quotient_model
  have hkernelLe : projection.ker ≤ action.ker := hkernel ▸ hQker
  let quotientAction := QuotientGroup.lift projection.ker action hkernelLe
  let equiv := QuotientGroup.quotientKerEquivOfSurjective projection hsurj
  let actionSL2 : SL2Two →* MulAut W := quotientAction.comp equiv.symm.toMonoidHom
  have hcomp : actionSL2.comp projection = action := by
    ext actor point
    have heq : equiv (QuotientGroup.mk' projection.ker actor) = projection actor := rfl
    change quotientAction (equiv.symm (projection actor)) point = action actor point
    rw [← heq,equiv.symm_apply_apply]
    rfl
  have hnative : E.subgroupOf M = twoResidualSubgroup M := by
    change (ctx.Γ.twoResidualAt middle).subgroupOf M = _
    rw [ctx.Γ.twoResidualAt_def]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hEimage : (E.subgroupOf M).map projection = commutator SL2Two := by
    rw [hnative,SectionThree.twoResidualSubgroup_eq_hktPResidual',
      hktPResidual_map_of_surjective' projection hsurj,
      ← SectionThree.twoResidualAmbient_top_eq_hktPResidual,
      SectionEight.eight_six_sl2_residual_eq_commutator]
  have hFimage : F = (commutator SL2Two).map actionSL2 := by
    rw [← hEimage,Subgroup.map_map,hcomp]
  have hFdiv : Nat.card F ∣ 3 := by
    rw [hFimage,← isSL2Two_commutator_card (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)]
    exact Subgroup.card_map_dvd _ _
  have hFcard : Nat.card F = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hFdiv with hone | hthree
    · have hFbot : F = ⊥ := Subgroup.card_eq_one.mp hone
      apply False.elim
      apply hnontrivial
      apply bot_unique
      rw [commutatorAction_eq_closure,Subgroup.closure_le]
      rintro x ⟨a,w,rfl⟩
      have ha : (a:MulAut W) = 1 := by simpa [hFbot] using a.property
      change w⁻¹ * (a:MulAut W) w ∈ (⊥ : Subgroup W)
      rw [ha]
      simp
    · exact hthree
  let _ : IsElementaryAbelian 2 W := hW
  have hdisplacement : Nat.card (commutatorAction F W) = 4 :=
    (card_three_action_on_eight_fixed_commutator_card hFcard hWcard hnontrivial).2
  exact ⟨hN,hMU,hW,hWcard,action,hact,hQker,hFcard,hnontrivial,hdisplacement⟩
end Stellmacher.SectionTen

