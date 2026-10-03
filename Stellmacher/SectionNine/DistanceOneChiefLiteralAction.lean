module

public import Stellmacher.SectionNine.DistanceOneChiefActionKernelData
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Literal image data for the canonical chief action

These facts use actual subgroup maps under the prescribed conjugation action,
without unfolding the sealed actor-image definition. The residual image acts
fully and has odd prime-power order; the U-image is quadratic with displacement
of order at most four. The initial-center kernel has odd image: its intersection
with the edge Sylow is the initial core, which the action already kills.

Oddness and the two centralizing commutators do not by themselves prove that
this image is trivial. The small quadratic representation step remains separate.
Source: Stellmacher, printed p.47 (10), and printed p.36 (7.7)(a).
-/

namespace Stellmacher.SectionNine

open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement

universe u

public theorem distance_one_chief_residual_map_fixed_eq_bot
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    FixedPoints.subgroup
      (((e ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx)) (DistanceOneChiefQuotient ctx) = ⊥ := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let Q := q ctx.Γ ctx.criticalPath.a
  let C := distanceOneChiefSubgroup ctx
  let E := e ctx.Γ ctx.criticalPath.a
  let projection := QuotientGroup.mk' (C.subgroupOf Q)
  let image := (E.subgroupOf P).map (distanceOneChiefAction ctx)
  let fixed := FixedPoints.subgroup image (DistanceOneChiefQuotient ctx)
  let D := (fixed.comap projection).map Q.subtype
  have hEP : E ≤ P := by
    dsimp only [E, P]
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hDE : ⁅D, E⁆ ≤ C := by
    apply Subgroup.commutator_le.mpr
    rintro point ⟨representative, hrepresentative, rfl⟩ actor hactor
    let actorP : P := ⟨actor, hEP hactor⟩
    let actorImage : image :=
      ⟨distanceOneChiefAction ctx actorP, Subgroup.mem_map_of_mem _ hactor⟩
    have hfixed := hrepresentative actorImage
    change distanceOneChiefAction ctx actorP (projection representative) =
      projection representative at hfixed
    rw [distance_one_chief_action_apply] at hfixed
    have hmem := QuotientGroup.eq_iff_div_mem.mp hfixed
    have hcomm : ⁅actor, (representative : G)⁆ ∈ C := by
      change actor * (representative : G) * actor⁻¹ / (representative : G) ∈ C at hmem
      simpa only [commutatorElement_def, div_eq_mul_inv] using hmem
    rw [← commutatorElement_inv]
    exact C.inv_mem hcomm
  have hDC : D ≤ C := (Subgroup.le_commutatorPreimage (Subgroup.map_subtype_le _) hDE).trans_eq
    (distance_one_chief_second_preimage_eq ctx)
  apply bot_unique
  intro point hpoint
  obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Q) point
  apply Subgroup.mem_bot.mpr
  apply (QuotientGroup.eq_one_iff _).mpr
  exact hDC (Subgroup.mem_map_of_mem Q.subtype hpoint)

section Ambient

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)

public theorem distance_one_chief_U_map_displacement_card_le_four
    (branch : DistanceOneChiefBranchData ctx) :
    Nat.card (commutatorAction
      ((branch.U.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx.toLocalContext))
      (DistanceOneChiefQuotient ctx.toLocalContext)) ≤ 4 := by
  let _ : ((distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf
      (q ctx.Γ ctx.criticalPath.a)).Normal :=
    distanceOneChiefSubgroup_normal_in_core ctx.toLocalContext
  have hUP := branch.le_sylow.trans
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  have hcard := Subgroup.quotient_conjugation_commutatorAction_card
    (stabilizer ctx.Γ ctx.criticalPath.a) (q ctx.Γ ctx.criticalPath.a)
    (distanceOneChiefSubgroup ctx.toLocalContext) branch.U
    (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a) hUP inferInstance
    (distanceOneChiefAction ctx.toLocalContext) (distance_one_chief_action_apply ctx.toLocalContext)
  exact hcard.le.trans ((Subgroup.relIndex_le_of_le_left
    (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1
      (((z ctx.Γ ctx.criticalPath.a).subgroupOf
        ⁅q ctx.Γ ctx.criticalPath.a, branch.U⁆).index_ne_zero_of_finite)).trans
      (distance_one_chief_displacement_relIndex_bounds ctx branch).2)

public theorem distance_one_chief_U_map_quadratic
    (hb : ctx.criticalPath.length = 1) (branch : DistanceOneChiefBranchData ctx) :
    commutatorAction₂
      ((branch.U.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx.toLocalContext))
      (DistanceOneChiefQuotient ctx.toLocalContext) = ⊥ := by
  let _ : ((distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf
      (q ctx.Γ ctx.criticalPath.a)).Normal :=
    distanceOneChiefSubgroup_normal_in_core ctx.toLocalContext
  have hUP := branch.le_sylow.trans
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1
  exact Subgroup.quotient_conjugation_quadratic_of_double_commutator_le
    (stabilizer ctx.Γ ctx.criticalPath.a) (q ctx.Γ ctx.criticalPath.a)
    (distanceOneChiefSubgroup ctx.toLocalContext) branch.U
    (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a) hUP inferInstance
    ((distance_one_chief_displacement_quadratic ctx hb branch).trans
      (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1)
    (distanceOneChiefAction ctx.toLocalContext) (distance_one_chief_action_apply ctx.toLocalContext)

public theorem distance_one_chief_residual_map_odd_pGroup
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    ∃ prime : ℕ, prime.Prime ∧ Odd prime ∧ IsPGroup prime
      (((e ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx.toLocalContext)) := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  have hcoreker : pCore 2 P ≤ (distanceOneChiefAction ctx.toLocalContext).ker := by
    intro actor hactor
    apply distance_one_chief_core_le_action_kernel ctx hb hfaith branch
    change (actor : G) ∈ q ctx.Γ ctx.criticalPath.a
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem P.subtype hactor
  have hlocal := (edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  obtain ⟨prime, hprime, hodd, hgroup⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    T (sectionThreeHypotheses ctx.sectionSeven) P
    ((pFamily_iff_pSet _ _ _).mp hlocal.1) hlocal.2
    (distanceOneChiefAction ctx.toLocalContext) hcoreker
  have hEsub : (e ctx.Γ ctx.criticalPath.a).subgroupOf P = twoResidualSubgroup P := by
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self (by simp)
  refine ⟨prime, hprime, hodd, ?_⟩
  change IsPGroup prime (((e ctx.Γ ctx.criticalPath.a).subgroupOf P).map
    (distanceOneChiefAction ctx.toLocalContext))
  rwa [hEsub]

public theorem distance_one_chief_residual_map_action_full
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    commutatorAction
      (((e ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx.toLocalContext))
      (DistanceOneChiefQuotient ctx.toLocalContext) = ⊤ := by
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let F := ((e ctx.Γ ctx.criticalPath.a).subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
    (distanceOneChiefAction ctx.toLocalContext)
  let _ : IsElementaryAbelian 2 W := distance_one_chief_quotient_elementary ctx hb hfaith branch
  obtain ⟨prime, hprime, hodd, hgroup⟩ :=
    distance_one_chief_residual_map_odd_pGroup ctx hb hfaith branch
  let _ : Fact prime.Prime := ⟨hprime⟩
  have hcop : Nat.Coprime (Nat.card F) (Nat.card W) := by
    obtain ⟨exponent, heq⟩ := hgroup.exists_card_eq
    obtain ⟨dimension, hdimension⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    change Nat.card F = prime ^ exponent at heq
    rw [heq, hdimension]
    exact (hodd.pow.coprime_two_right).pow_right dimension
  have hsplit : IsCompl (FixedPoints.subgroup F W) (commutatorAction F W) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := F)
      (Group.isSolvable_of_comm fun first second => IsMulCommutative.is_comm.comm first second)
      hcop inferInstance
  have hfixed : FixedPoints.subgroup F W = ⊥ :=
    distance_one_chief_residual_map_fixed_eq_bot ctx.toLocalContext
  have htop := hsplit.sup_eq_top
  rwa [hfixed, bot_sup_eq] at htop

public theorem distance_one_initial_center_kernel_map_odd
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    Odd (Nat.card
      (((Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)).subgroupOf
        (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx.toLocalContext))) := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let C := P ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)
  let K := C.subgroupOf P
  let action : P →* MulAut (DistanceOneChiefQuotient ctx.toLocalContext) :=
    distanceOneChiefAction ctx.toLocalContext
  change Odd (Nat.card
    (((Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)).subgroupOf P).map action))
  have hUE : ⁅branch.U, twoResidualIn (stabilizer ctx.Γ ctx.criticalPath.a')⁆ = branch.U := by
    simpa only [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, stabilizer] using
      branch.terminal_residual_commutator
  have hdata := distance_one_initial_centralizer_kernel_data ctx hb branch.U
    branch.le_terminal_core hUE
  let _ : K.Normal := hdata.2.1
  obtain ⟨_, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  obtain ⟨innerSylow, hinner⟩ := sylow.exists_subgroupOf_eq_of_normal K
  have hcore : (sylow : Subgroup P) ⊓ K = (q ctx.Γ ctx.criticalPath.a).subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_inf _ _ _ P.subtype_injective, hsylow,
      Subgroup.map_subgroupOf_eq_of_le (show C ≤ P from inf_le_left)]
    rw [inf_comm, hdata.2.2.1]
    exact (Subgroup.map_subgroupOf_eq_of_le
      (show q ctx.Γ ctx.criticalPath.a ≤ P from by
        rw [q, ctx.Γ.twoCoreAt_def]
        exact Subgroup.map_subtype_le _)).symm
  have hle : (sylow : Subgroup P).subgroupOf K ≤ action.ker.subgroupOf K := by
    intro actor hactor
    exact distance_one_chief_core_le_action_kernel ctx hb hfaith branch
      (hcore.le ⟨hactor, actor.property⟩)
  have hodd : Odd ((sylow : Subgroup P).subgroupOf K).index := by
    rw [← hinner, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact innerSylow.not_dvd_index
  have hindex : Odd (action.ker.relIndex K) :=
    hodd.of_dvd_nat (Subgroup.index_dvd_of_le hle)
  rw [Subgroup.relIndex_ker] at hindex
  simpa only [K, C, Subgroup.inf_subgroupOf_left] using hindex

end Ambient

end Stellmacher.SectionNine
