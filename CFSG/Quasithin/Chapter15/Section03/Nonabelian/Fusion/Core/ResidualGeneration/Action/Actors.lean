module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Quotients
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Index
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The residual in the recognized actor group

The two-residual of Aut(SL₃(2)) is its actual inner subgroup. The quotient
projection transports the ambient residual onto this subgroup; restricting
an actual Sylow subgroup therefore gives an actor image of order eight.
A nontrivial V-image has full commutator with the simple inner subgroup,
whose centralizer in the automorphism group is trivial. The two-group
kernel and two-perfectness of K lift that commutator identity to K itself.

These are the group-theoretic action deductions used in Aschbacher–Smith,
combined manuscript (1 March 2004), 15.3.58–59, printed pp.1149–1150.
The module deductions are separate: no containment of U in K is assumed here.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
open Subgroup
open Matrix.PSL3Two
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core

private theorem linear_three_simple : IsSimpleGroup SL := by
  let : IsSimpleGroup PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  exact equiv.isSimpleGroup

private noncomputable def innerEquiv : SL ≃* MulAut.innerSubgroup SL :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot center_eq_bot)

private theorem linear_three_two_perfect : IsPPerfect 2 SL := by
  let : IsSimpleGroup SL := linear_three_simple
  intro N hN hp
  rcases hN.eq_bot_or_eq_top with hn | hn
  · obtain ⟨n, hc⟩ := hp.exists_card_eq
    have he : 168 = 2 ^ n := by
      change N.index = 2 ^ n at hc
      simpa only [hn, index_bot, card_SL] using hc
    have hd : 3 ∣ 2 ^ n := he ▸ (by decide : 3 ∣ 168)
    have hf := (by decide : Nat.Prime 3).dvd_of_dvd_pow hd
    norm_num at hf
  · exact hn

private theorem aut_residual_inner :
    pResidual 2 (MulAut SL) = MulAut.innerSubgroup SL := by
  exact pResidual_eq_of_isPPerfect _
    (linear_three_two_perfect.of_surjective innerEquiv.toMonoidHom innerEquiv.surjective)
    Automorphisms.outer_sl_isTwoGroup

variable {G : Type*} [Group G] [Finite G]

/-- The embedded residual is the intrinsic residual when restricted to H. -/
theorem residual_subgroupOf_H (Z : Subgroup G) :
    (residualK Z).subgroupOf (centralizerH Z) = pResidual 2 (centralizerH Z) := by
  apply map_injective (centralizerH Z).subtype_injective
  rw [map_subgroupOf_eq_of_le (residual_le_H Z), ← twoResidualAmbient_eq_pResidual]

/-- The quotient projection carries the residual onto the actor residual. -/
theorem actorImage_residual (Z : Subgroup G) :
    actorImage Z (residualK Z) = pResidual 2 (ActorQuotient Z) := by
  unfold actorImage
  rw [residual_subgroupOf_H]
  exact map_pResidual_of_surjective 2 (actorProjection Z) (QuotientGroup.mk'_surjective _)

/-- Recognition identifies the actual residual image with inner automorphisms. -/
theorem actorImage_residual_inner (Z : Subgroup G)
    (e : ActorQuotient Z ≃* MulAut SL) :
    (actorImage Z (residualK Z)).map e.toMonoidHom = MulAut.innerSubgroup SL := by
  rw [actorImage_residual, map_pResidual 2 e, aut_residual_inner]

omit [Finite G] in
/-- The range of the restriction is the literal ambient actor image. -/
theorem residualActor_range (Z : Subgroup G) :
    (residualActor Z).range = actorImage Z (residualK Z) := by
  rw [← residualActor_map Z _ le_rfl]
  simp only [subgroupOf_self, ← MonoidHom.range_eq_map]

/-- The actual residual actor image is isomorphic to SL₃(2), through conjugation. -/
noncomputable def residualImageEquiv (Z : Subgroup G)
    (e : ActorQuotient Z ≃* MulAut SL) : (residualActor Z).range ≃* SL :=
  (MulEquiv.subgroupCongr (residualActor_range Z)).trans
    (((actorImage Z (residualK Z)).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr (actorImage_residual_inner Z e)).trans innerEquiv.symm))

/-- The actor image of the literal T ∩ K has order eight. -/
theorem residualSylow_actor_card (T Z : Subgroup G)
    (S : Sylow 2 (centralizerH Z))
    (hS : (S : Subgroup (centralizerH Z)).map (centralizerH Z).subtype = T)
    (e : ActorQuotient Z ≃* MulAut SL) :
    Nat.card (actorImage Z (residualSylow T Z)) = 8 := by
  obtain ⟨R, hR⟩ := residualSylow_exists T Z S hS
  let f := (residualActor Z).rangeRestrict
  let P := R.mapSurjective (f := f) (residualActor Z).rangeRestrict_surjective
  have hP : ((P : Subgroup (residualActor Z).range).map (residualActor Z).range.subtype) =
      actorImage Z (residualSylow T Z) := by
    change ((R : Subgroup (residualK Z)).map f).map _ = _
    rw [map_map]
    change (R : Subgroup (residualK Z)).map (residualActor Z) = _
    have hRi : (R : Subgroup (residualK Z)) =
        (residualSylow T Z).subgroupOf (residualK Z) := by
      apply map_injective (residualK Z).subtype_injective
      rw [hR, map_subgroupOf_eq_of_le (show residualSylow T Z ≤ residualK Z from inf_le_right)]
    rw [hRi]
    exact residualActor_map Z (residualSylow T Z) inf_le_right
  rw [← hP, card_map_of_injective (residualActor Z).range.subtype_injective,
    P.card_eq_multiplicity, Nat.card_congr (residualImageEquiv Z e).toEquiv, card_SL]
  decide +kernel


private theorem inner_commutator (B : Subgroup (MulAut SL)) (hB : B ≠ ⊥) :
    ⁅MulAut.innerSubgroup SL, B⁆ = MulAut.innerSubgroup SL := by
  let I := MulAut.innerSubgroup SL
  let C := ⁅I, B⁆
  have hCI : C ≤ I := commutator_le_left I B
  let : IsSimpleGroup SL := linear_three_simple
  let : IsSimpleGroup I := innerEquiv.symm.isSimpleGroup
  let : (C.subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left I B)
  rcases (inferInstance : (C.subgroupOf I).Normal).eq_bot_or_eq_top with h | h
  · have hc : C = ⊥ := by
      have hh := congrArg (map I.subtype) h
      simpa only [map_subgroupOf_eq_of_le hCI, Subgroup.map_bot] using hh
    have hb : B ≤ centralizer (I : Set (MulAut SL)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    rw [MulAut.centralizer_innerSubgroup_eq_bot center_eq_bot] at hb
    exact (hB (bot_unique hb)).elim
  · have hh := congrArg (map I.subtype) h
    simpa only [map_subgroupOf_eq_of_le hCI, ← MonoidHom.range_eq_map, range_subtype] using hh

omit [Finite G] in
/-- Commutators transport through the quotient after restriction to H. -/
theorem actorImage_commutator (Z A B : Subgroup G)
    (hA : A ≤ centralizerH Z) (hB : B ≤ centralizerH Z) :
    actorImage Z ⁅A, B⁆ = ⁅actorImage Z A, actorImage Z B⁆ := by
  have he : ⁅A, B⁆.subgroupOf (centralizerH Z) =
      ⁅A.subgroupOf (centralizerH Z), B.subgroupOf (centralizerH Z)⁆ := by
    apply map_injective (centralizerH Z).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB,
      map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup A B).trans (sup_le hA hB))]
  unfold actorImage
  rw [he, map_commutator]

/-- The nontrivial V-action of 15.3.51(1) generates the whole residual by commutators. -/
theorem residual_commutator_eq (Z V : Subgroup G)
    (e : ActorQuotient Z ≃* MulAut SL)
    (hVH : V ≤ centralizerH Z) (hVQ : ¬ V ≤ coreQ Z) :
    ⁅residualK Z, V⁆ = residualK Z := by
  let K := residualK Z
  let C := ⁅K, V⁆
  have hn : centralizerH Z ≤ normalizer (K : Set G) := by
    exact (normal_subgroupOf_iff_le_normalizer (residual_le_H Z)).mp (residual_normal_in_H Z)
  have hCK : C ≤ K := le_normalizer_iff_commutator_le_left.mp (hVH.trans hn)
  have hB : (actorImage Z V).map e.toMonoidHom ≠ ⊥ := by
    intro hb
    apply hVQ
    intro v hv
    apply (actorProjection_eq_one_iff Z ⟨v, hVH hv⟩).mp
    apply e.injective
    have hm : e (actorProjection Z ⟨v, hVH hv⟩) ∈
        (actorImage Z V).map e.toMonoidHom :=
      mem_map_of_mem _ (mem_map_of_mem _ hv)
    simpa only [hb, mem_bot, map_one] using hm
  have hmap : actorImage Z C = actorImage Z K := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [show C = ⁅residualK Z, V⁆ from rfl, actorImage_commutator Z _ _ (residual_le_H Z) hVH,
      map_commutator, actorImage_residual_inner, inner_commutator _ hB]
  let D := C.subgroupOf K
  let : D.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left K V)
  have hDmap : D.map (residualActor Z) = (residualActor Z).range := by
    rw [residualActor_map Z C hCK, hmap, residualActor_range]
  have hsup : D ⊔ (residualActor Z).ker = ⊤ := by
    rw [← comap_map_eq, hDmap]
    exact eq_top_iff.mpr (fun x _ => ⟨x, rfl⟩)
  have hp : IsPGroup 2 (residualActor Z).ker := by
    rw [residualActor_ker]
    exact (pCore_isPGroup.map (centralizerH Z).subtype).comap_subtype
  have htop : D = ⊤ := residualK_isPPerfect Z D inferInstance
    (isPGroup_quotient_of_sup_eq_top D (residualActor Z).ker hp hsup)
  have hh := congrArg (map K.subtype) htop
  change (C.subgroupOf K).map K.subtype = (⊤ : Subgroup K).map K.subtype at hh
  simpa only [map_subgroupOf_eq_of_le hCK, ← MonoidHom.range_eq_map, range_subtype] using hh


/-- Every specified inner actor has a lift in the actual residual. -/
theorem exists_residual_lift_inner (Z : Subgroup G)
    (e : ActorQuotient Z ≃* MulAut SL) (g : SL) :
    ∃ k : residualK Z, e (residualActor Z k) = MulAut.conj g := by
  have hg : MulAut.conj g ∈ (actorImage Z (residualK Z)).map e.toMonoidHom := by
    rw [actorImage_residual_inner]
    exact ⟨g, rfl⟩
  obtain ⟨a, ha, he⟩ := hg
  obtain ⟨h, hh, rfl⟩ := ha
  exact ⟨⟨h, hh⟩, he⟩

/-- Once the actor kernel lies in K, an inner actor lifts only to elements of K. -/
theorem mem_residual_of_actor_inner (Z : Subgroup G)
    (e : ActorQuotient Z ≃* MulAut SL) (hQK : coreQ Z ≤ residualK Z)
    (h : centralizerH Z) (hi : e (actorProjection Z h) ∈ MulAut.innerSubgroup SL) :
    (h : G) ∈ residualK Z := by
  obtain ⟨g, hg⟩ := hi
  obtain ⟨k, hk⟩ := exists_residual_lift_inner Z e g
  have he : actorProjection Z h = residualActor Z k := e.injective (hg.symm.trans hk.symm)
  have hq : (h : G) * (k : G)⁻¹ ∈ coreQ Z := by
    apply (actorProjection_eq_one_iff Z (h * (inclusion (residual_le_H Z) k)⁻¹)).mp
    rw [map_mul, map_inv, he]
    exact mul_inv_cancel _
  have hm := (residualK Z).mul_mem (hQK hq) k.property
  simpa only [inv_mul_cancel_right] using hm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
