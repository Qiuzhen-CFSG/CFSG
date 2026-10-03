module

public import Stellmacher.SectionNine.DistanceOneChiefDisplacement
public import Theory.GroupTheory.CommutatorPreimageTransport

/-!
# The initial-center quotient used in chief-module recognition

All images in this file are taken in the initial stabilizer modulo its
vertex center. This quotient is not the faithful center-action quotient.
The cardinality of the canonical chief quotient is exactly the centralizer
index on the initial core image, and the extracted subgroup has a nontrivial
quadratic displacement of order at most four on that image.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public instance distanceOneInitialCenter_normal_in_stabilizer
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    ((z ctx.Γ ctx.criticalPath.a).subgroupOf
      (stabilizer ctx.Γ ctx.criticalPath.a)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a)

public abbrev DistanceOneInitialCenterQuotient
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :=
  (stabilizer ctx.Γ ctx.criticalPath.a) ⧸
    (z ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)

public def distanceOneInitialCenterImage
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (D : Subgroup G) :
    Subgroup (DistanceOneInitialCenterQuotient ctx) :=
  (D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
    (QuotientGroup.mk' ((z ctx.Γ ctx.criticalPath.a).subgroupOf
      (stabilizer ctx.Γ ctx.criticalPath.a)))

public theorem distance_one_initial_center_image_card
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (D : Subgroup G)
    (hDP : D ≤ stabilizer ctx.Γ ctx.criticalPath.a) :
    Nat.card (distanceOneInitialCenterImage ctx D) =
      (z ctx.Γ ctx.criticalPath.a).relIndex D := by
  unfold distanceOneInitialCenterImage
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hDP]

public theorem distance_one_initial_center_image_commutator
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (D F : Subgroup G)
    (hDP : D ≤ stabilizer ctx.Γ ctx.criticalPath.a)
    (hFP : F ≤ stabilizer ctx.Γ ctx.criticalPath.a) :
    distanceOneInitialCenterImage ctx ⁅D, F⁆ =
      ⁅distanceOneInitialCenterImage ctx D, distanceOneInitialCenterImage ctx F⁆ := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  have hcomm : ⁅D, F⁆ ≤ P :=
    (Subgroup.commutator_mono hDP hFP).trans (Subgroup.commutator_le_sup P P |>.trans
      (sup_le le_rfl le_rfl))
  have hnative : (⁅D, F⁆).subgroupOf P = ⁅D.subgroupOf P, F.subgroupOf P⁆ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hcomm, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hDP, Subgroup.map_subgroupOf_eq_of_le hFP]
  unfold distanceOneInitialCenterImage
  rw [hnative, Subgroup.map_commutator]

public theorem distance_one_initial_center_image_eq_bot_iff
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (D : Subgroup G)
    (hDP : D ≤ stabilizer ctx.Γ ctx.criticalPath.a) :
    distanceOneInitialCenterImage ctx D = ⊥ ↔ D ≤ z ctx.Γ ctx.criticalPath.a := by
  unfold distanceOneInitialCenterImage
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  constructor
  · intro hbound element helement
    exact hbound (show (⟨element, hDP helement⟩ : stabilizer ctx.Γ ctx.criticalPath.a) ∈
      D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a) from helement)
  · exact fun hbound _ helement => hbound helement

public theorem distance_one_chief_subgroup_eq_commutatorPreimage
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    distanceOneChiefSubgroup ctx = Subgroup.commutatorPreimage
      (q ctx.Γ ctx.criticalPath.a) (e ctx.Γ ctx.criticalPath.a) (z ctx.Γ ctx.criticalPath.a) := by
  have hprops := distance_one_chief_subgroup_properties ctx
  have hQP : q ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  refine le_antisymm (Subgroup.le_commutatorPreimage hprops.1 hprops.2.2.2.1.le) ?_
  apply hprops.2.2.2.2 _ (Subgroup.commutatorPreimage_le _ _ _)
  exact Subgroup.commutator_commutatorPreimage_eq _ _ _
    (hQP.trans (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a))
    (hprops.2.1.trans hprops.1) (distance_one_initial_center_full_residual ctx)

public theorem distance_one_chief_quotient_card_centralizer_index
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    Nat.card (DistanceOneChiefQuotient ctx) =
      (Subgroup.centralizer
        (distanceOneInitialCenterImage ctx (e ctx.Γ ctx.criticalPath.a) :
          Set (DistanceOneInitialCenterQuotient ctx))).relIndex
        (distanceOneInitialCenterImage ctx (q ctx.Γ ctx.criticalPath.a)) := by
  have hQP : q ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hEP : e ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  rw [distance_one_chief_quotient_card, distance_one_chief_subgroup_eq_commutatorPreimage]
  simpa only [distanceOneInitialCenterImage] using
    Subgroup.commutatorPreimage_relIndex_subgroup_quotient _ _ _ _ hQP hEP
      (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a)

public theorem distance_one_chief_image_displacement_bounds
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    let Qbar := distanceOneInitialCenterImage ctx.toLocalContext (q ctx.Γ ctx.criticalPath.a)
    let Ubar := distanceOneInitialCenterImage ctx.toLocalContext branch.U
    1 < Nat.card (⁅Qbar, Ubar⁆ : Subgroup (DistanceOneInitialCenterQuotient ctx.toLocalContext)) ∧
      Nat.card (⁅Qbar, Ubar⁆ : Subgroup (DistanceOneInitialCenterQuotient ctx.toLocalContext)) ≤ 4 := by
  have hTP := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  have hQP := (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1.trans hTP
  have hUP := branch.le_sylow.trans hTP
  have hDP := (distance_one_chief_displacement_le_intersection ctx branch).trans
    (inf_le_right.trans hQP)
  dsimp only
  rw [← distance_one_initial_center_image_commutator ctx.toLocalContext _ _ hQP hUP,
    distance_one_initial_center_image_card ctx.toLocalContext _ hDP]
  exact distance_one_chief_displacement_relIndex_bounds ctx branch

public theorem distance_one_chief_image_displacement_quadratic
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (branch : DistanceOneChiefBranchData ctx) :
    let Qbar := distanceOneInitialCenterImage ctx.toLocalContext (q ctx.Γ ctx.criticalPath.a)
    let Ubar := distanceOneInitialCenterImage ctx.toLocalContext branch.U
    ⁅⁅Qbar, Ubar⁆, Ubar⁆ = ⊥ := by
  have hTP := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  have hQP := (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1.trans hTP
  have hUP := branch.le_sylow.trans hTP
  have hDP := (distance_one_chief_displacement_le_intersection ctx branch).trans
    (inf_le_right.trans hQP)
  have hbound := distance_one_chief_displacement_quadratic ctx hb branch
  have hZP := ((distance_one_chief_subgroup_properties ctx.toLocalContext).2.1.trans
    (distance_one_chief_subgroup_properties ctx.toLocalContext).1).trans hQP
  dsimp only
  rw [← distance_one_initial_center_image_commutator ctx.toLocalContext _ _ hQP hUP,
    ← distance_one_initial_center_image_commutator ctx.toLocalContext _ _ hDP hUP]
  exact (distance_one_initial_center_image_eq_bot_iff ctx.toLocalContext _
    (hbound.trans hZP)).mpr hbound

public theorem distance_one_chief_actor_center_image_card
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    Nat.card (distanceOneInitialCenterImage ctx.toLocalContext branch.U) = 16 := by
  have hUP := branch.le_sylow.trans
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  rw [distance_one_initial_center_image_card ctx.toLocalContext _ hUP]
  have hcount := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G)
    (branch.U ⊓ z ctx.Γ ctx.criticalPath.a) branch.U bot_le inf_le_left
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    Subgroup.inf_relIndex_left, branch.initial_center_intersection_card, branch.card] at hcount
  change (z ctx.Γ ctx.criticalPath.a).relIndex branch.U = 16
  omega

public theorem distance_one_chief_actor_center_image_elementary
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (branch : DistanceOneChiefBranchData ctx) :
    IsElementaryAbelian 2 (distanceOneInitialCenterImage ctx.toLocalContext branch.U) := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let Z := z ctx.Γ ctx.criticalPath.a
  let terminal := z ctx.Γ ctx.criticalPath.a'
  let projection := QuotientGroup.mk' (Z.subgroupOf P)
  have hUP := branch.le_sylow.trans
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  have hterminal : terminal ≤ Z :=
    distance_one_terminal_center_le_initial_center ctx.toLocalContext hb
  have hUU : ⁅branch.U, branch.U⁆ ≤ Z :=
    (Subgroup.commutator_mono le_rfl branch.le_terminal_core).trans
      (branch.terminal_core_commutator.le.trans hterminal)
  have hUUP : ⁅branch.U, branch.U⁆ ≤ P :=
    (Subgroup.commutator_le_sup branch.U branch.U).trans (sup_le hUP hUP)
  have hcomm : IsMulCommutative (distanceOneInitialCenterImage ctx.toLocalContext branch.U) := by
    apply Subgroup.commutator_self_eq_bot_iff.mp
    rw [← distance_one_initial_center_image_commutator ctx.toLocalContext _ _ hUP hUP]
    exact (distance_one_initial_center_image_eq_bot_iff ctx.toLocalContext _ hUUP).mpr hUU
  have hUE : ⁅branch.U, twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆ = branch.U := by
    simpa only [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, stabilizer] using
      branch.terminal_residual_commutator
  obtain ⟨hN, hW⟩ := distance_one_v1_quotient_elementary ctx hb branch.U
    branch.le_terminal_core branch.terminal_center_le branch.terminal_core_commutator hUE
  let _ := hN
  let _ := hW
  refine { toIsMulCommutative := hcomm, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro element
  obtain ⟨preimage, hpreimage, heq⟩ := element.property
  apply Subtype.ext
  change (element : DistanceOneInitialCenterQuotient ctx.toLocalContext) ^ 2 = 1
  rw [← heq, ← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  have hpow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (branch.U ⧸ terminal.subgroupOf branch.U))
    (QuotientGroup.mk' (terminal.subgroupOf branch.U) ⟨preimage, hpreimage⟩)
  rw [← map_pow] at hpow
  have hmem := (QuotientGroup.eq_one_iff _).mp hpow
  exact hterminal hmem

end Stellmacher.SectionNine
