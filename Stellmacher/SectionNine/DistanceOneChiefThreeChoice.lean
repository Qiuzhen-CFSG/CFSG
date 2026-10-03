module
public import Stellmacher.SectionNine.DistanceOneChiefOrder
public import Stellmacher.SectionNine.DistanceOneQuadraticImage
public import Stellmacher.SectionOne.NineCoreQuadraticSupport
public import Stellmacher.SectionOne.NormalizedThreeNonquadraticSixteen

/-!
# The order-three image selected in the distance-one chief branch

In the actual noncentral distance-one branch, the canonical chief action
range contains an order-three subgroup normalized by the U-image. Its
fixed chief plane has order four and is moved by that U-image. The full
preimage of the chosen subgroup has no nonidentity fixed point in the
initial center.

Factor initial-center conjugation through the chief range using the proved
action-kernel equality. This gives a faithful quotient-module witness on
the original initial center with exactly the same acting group as the
chief quotient. On the chief module the quadratic U-image preserves an
intrinsic nine-core support line. On the initial center the same image is
nonquadratic by source(5), forcing that line to be fixed-free. Witness
fixed-point transport gives the stated ambient centralizer intersection.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), printed p48,
the choice of D* before the final chief-branch contradiction. The subgroup
lift and fixed-layer normalizer are supplied by separate modules; no
ambient odd-subgroup choice is part of the action construction here.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_chief_three_image_choice
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    let P := stabilizer ctx.Γ ctx.criticalPath.a
    let action := distanceOneChiefAction ctx.toLocalContext
    let projection := action.rangeRestrict
    let J := (branch.U.subgroupOf P).map projection
    ∃ D : Subgroup action.range, Nat.card D = 3 ∧
      J ≤ Subgroup.normalizer (D : Set action.range) ∧
      Nat.card (FixedPoints.subgroup D (DistanceOneChiefQuotient ctx.toLocalContext)) = 4 ∧
      z ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer ((D.comap projection).map P.subtype : Set G) = ⊥ ∧
      ∃ actor : J, ∃ point ∈ FixedPoints.subgroup D (DistanceOneChiefQuotient ctx.toLocalContext),
        actor • point ≠ point := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Z := z Γ cp.a
  let Q := q Γ cp.a
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let action : P →* MulAut W := distanceOneChiefAction ctx.toLocalContext
  let X := action.range
  let projection : P →* X := action.rangeRestrict
  let J := (branch.U.subgroupOf P).map projection
  change ∃ D : Subgroup X, Nat.card D = 3 ∧
    J ≤ Subgroup.normalizer (D : Set X) ∧ Nat.card (FixedPoints.subgroup D W) = 4 ∧
    Z ⊓ Subgroup.centralizer ((D.comap projection).map P.subtype : Set G) = ⊥ ∧
    ∃ actor : J, ∃ point ∈ FixedPoints.subgroup D W, actor • point ≠ point
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Z := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  let _ : IsElementaryAbelian 2 W := distance_one_chief_quotient_elementary ctx hb hfaith branch
  have hZP : Z ≤ P := by
    dsimp only [Z, P]
    rw [z, Γ.zAt_def]
    apply sSup_le
    rintro center ⟨sylow, rfl⟩
    exact (omegaOneCenter_le_centerAmbient _).trans
      ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))
  have hkernel : projection.ker = (P ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf P := by
    rw [MonoidHom.ker_rangeRestrict]
    have hh := distance_one_chief_action_kernel ctx hb hfaith branch
    change action.ker = (Subgroup.centralizer (Z : Set G)).subgroupOf P at hh
    simpa only [Subgroup.inf_subgroupOf_left] using hh
  obtain ⟨original⟩ := exists_quotientModuleWitness P Z hZP (stabilizer_le_normalizer_z Γ cp.a)
  let _ := original.groupX
  let _ := original.finiteX
  let center : P →* MulAut Z := original.action.comp original.projection
  have hkerLe : projection.ker ≤ center.ker := by
    intro actor hactor
    have hp : original.projection actor = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [original.kernel_eq, ← hkernel]
      exact hactor
    change original.action (original.projection actor) = 1
    rw [hp, map_one]
  let equiv : P ⧸ projection.ker ≃* X :=
    QuotientGroup.liftEquiv projection.ker action.rangeRestrict_surjective rfl
  let lifted := QuotientGroup.lift projection.ker center hkerLe
  let centerAction : X →* MulAut Z := lifted.comp equiv.symm.toMonoidHom
  have hformula (actor : P) : centerAction (projection actor) = center actor := by
    change lifted (equiv.symm (projection actor)) = center actor
    have hm : equiv (QuotientGroup.mk' projection.ker actor) = projection actor :=
      QuotientGroup.liftEquiv_mk _ action.rangeRestrict_surjective rfl actor
    rw [← hm, equiv.symm_apply_apply]
    rfl
  let witness : QuotientModuleWitness P (P ⊓ Subgroup.centralizer (Z : Set G)) Z := {
    X := X
    projection := projection
    surjective := action.rangeRestrict_surjective
    kernel_eq := hkernel
    module_le := hZP
    action := centerAction
    action_compatible := by
      intro actor point
      rw [hformula]
      exact original.action_compatible actor point }
  let _ : MulDistribMulAction X Z := MulDistribMulAction.compHom Z centerAction
  obtain ⟨hsetup, hZcard, hFcard, _, _, _, _⟩ :=
    distance_one_faithful_recognition_setup ctx hb branch.extraction witness
  let F := SectionOne.oddCore X
  let _ : F.Normal := pPrimeCore_normal
  have hJmap : J.map X.subtype = (branch.U.subgroupOf P).map action := by
    rw [Subgroup.map_map]
    rfl
  have hJcard : Nat.card J = 4 := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, hJmap]
    exact distance_one_chief_U_map_card_four ctx hb hfaith branch
  have hJquad : commutatorAction₂ J W = ⊥ := by
    rw [← commutatorAction₂_map_actor_subtype X, hJmap]
    exact distance_one_chief_U_map_quadratic ctx hb branch
  let next := Γ.act branch.extraction.x⁻¹ cp.a
  let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  have hVP : V ≤ P := (distance_one_product_factors Γ cp.a next).2.2.1.trans inf_le_left
  have hQP : Q ≤ P := by
    dsimp only [Q, P]
    rw [q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQkernel : Q.subgroupOf P ≤ projection.ker := by
    intro element helement
    rw [hkernel]
    refine ⟨element.property, ?_⟩
    have hQc : Q ≤ Subgroup.centralizer (Z : Set G) :=
      (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer.ge.trans inf_le_right
    exact hQc helement
  have hJle : J ≤ (V.subgroupOf P).map projection := by
    have hh := Subgroup.map_mono (f := projection)
      (Subgroup.subgroupOf_mono P branch.le_product_core)
    rw [Subgroup.subgroupOf_sup hVP hQP, Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff (Q.subgroupOf P)).mpr hQkernel, sup_bot_eq] at hh
    exact hh
  have hVcard : Nat.card ((V.subgroupOf P).map projection) = 4 :=
    (distance_one_relative_odd_order ctx hb branch.extraction witness).2
  have hJeq : J = (V.subgroupOf P).map projection :=
    Subgroup.eq_of_le_of_card_ge hJle (by rw [hJcard, hVcard])
  let _ : IsElementaryAbelian 2 J := by
    rw [hJeq]
    exact distance_one_image_elementary ctx branch.extraction witness
  let _ : IsElementaryAbelian 3 F := SectionOne.nineCore_elementary_of_elementary_four
    hsetup hFcard J inferInstance hJcard
  have hfaithW : fixingSubgroup X (Set.univ : Set W) = ⊥ := by
    apply bot_unique
    intro actor hactor
    apply Subtype.ext
    ext point
    rw [mem_fixingSubgroup_iff] at hactor
    exact hactor point (Set.mem_univ point)
  have hWcard : Nat.card W = 16 := distance_one_chief_quotient_card_sixteen ctx hb hfaith branch
  obtain ⟨D, _, hDcard, hDnormal, hDfixed, hmoves⟩ :=
    SectionOne.nineCore_quadratic_actor_support_line F J hFcard hWcard hfaithW hJcard hJquad
  have hnonquad : commutatorAction₂ J Z ≠ ⊥ := by
    intro hquad
    have hbound := distance_one_quadratic_image_card_le_two ctx hb branch.extraction witness
      J hJle hquad
    rw [hJcard] at hbound
    omega
  have hfree : FixedPoints.subgroup D Z = ⊥ :=
    SectionOne.normalized_three_fixed_free_of_nonquadratic_sixteen D J hDcard
      (IsElementaryAbelian.isPGroup 2 J) hZcard hsetup.action_faithful hDnormal hnonquad
  let E := (D.comap projection).map P.subtype
  have hEP : E ≤ P := Subgroup.map_subtype_le _
  have hEimage : (E.subgroupOf P).map projection = D := by
    rw [show E = (D.comap projection).map P.subtype from rfl, subgroupOf_map_subtype_eq,
      Subgroup.map_comap_eq_self_of_surjective action.rangeRestrict_surjective]
  have hfreeAmbient : Z ⊓ Subgroup.centralizer (E : Set G) = ⊥ := by
    have hh := witness.fixedPoints_map_subtype E hEP
    change (FixedPoints.subgroup ((E.subgroupOf P).map projection) Z).map Z.subtype = _ at hh
    rw [hEimage, hfree, Subgroup.map_bot] at hh
    exact hh.symm
  exact ⟨D, hDcard, hDnormal, hDfixed, hfreeAmbient, hmoves⟩

end Stellmacher.SectionNine
