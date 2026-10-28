module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.ExtraspecialBranch.Geometry

/-!
# Applying the faithful-action clause of 14.1.17(4)

The actor is injective on Rc*, so the chosen inverter has order two in
M/O₂(M). Its inversion of the E₉ action image is nontrivial. Once Y* is
a three-group, normality puts it in O₃(M*), and hence the inverter acts
faithfully on that three-core. This proves the premise of 14.1.17(4),
rather than replacing that conditional source clause by its conclusion.

The resulting cyclic Sylow groups control every three-subgroup of C_M(V)*.
The quotient by O₂(M) is injective on three-subgroups, so the assertion
lifts to C_M(V). Finally, the intersection factorization makes the actor
image of M ∩ Mc a two-group, placing every Sylow three-subgroup in that
kernel. No theta-generation or Rc-cyclicity hypothesis is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemmas
14.1.17(4) and 15.3.7, printed pp.980 and 1122 (PDF pp.997 and 1139).
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives.ExtraspecialBranch
variable {G : Type*} [Group G] [Finite G]
variable {M Mc V : Subgroup G} {T : Sylow 2 G} {d : NaturalOrthogonalAction M V}

/-- The source inverter gives a faithful cyclic action on the actual O₃(M*). -/
public theorem exists_faithful_star_inverter (h : SourceInputs M Mc V T d)
    (hp : IsPGroup 3 (star M (residualY M Mc))) :
    ∃ r : StarGroup M, r ∈ star M (Rc M Mc) ∧ orderOf r = 2 ∧
      Function.Injective
        ((MulAut.conjNormal : StarGroup M →* MulAut (pCore 3 (StarGroup M))).domRestrict
          (zpowers r)) := by
  classical
  let q := QuotientGroup.mk' (pCore 2 M)
  let f := starActor d h.core_le_kernel
  obtain ⟨r₀, hr₀, hrne, hrsq, hinv⟩ := h.inverter
  let r := q r₀
  have hrmem : r ∈ star M (Rc M Mc) := mem_map_of_mem q hr₀
  have hrne' : r ≠ 1 := by
    intro heq
    exact hrne (show d.actor r₀ = 1 from (congrArg f heq).trans f.map_one)
  have hrsq' : r ^ 2 = 1 := by
    have hs : (⟨r, hrmem⟩ : star M (Rc M Mc)) ^ 2 = 1 := by
      apply star_rc_actor_injective h
      change f (r ^ 2) = f 1
      rw [map_pow, map_one]
      change d.actor r₀ ^ 2 = 1
      exact hrsq
    exact congrArg (star M (Rc M Mc)).subtype hs
  have hrorder : orderOf r = 2 := orderOf_eq_prime hrsq' hrne'
  let a : StarGroup M →* MulAut (pCore 3 (StarGroup M)) := MulAut.conjNormal
  have hanontrivial : a r ≠ 1 := by
    intro ha
    obtain ⟨e⟩ := h.image_model
    let c : ElementaryNine := (Multiplicative.ofAdd (1 : ZMod 3), 1)
    let b := e.symm c
    have hb : (b : OrthogonalActor) ≠ (b : OrthogonalActor)⁻¹ := by
      intro heq
      have hb' : b = b⁻¹ := Subtype.ext heq
      have hc : c = c⁻¹ := by simpa only [b, map_inv, e.apply_symm_apply] using congrArg e hb'
      exact (by decide : c ≠ c⁻¹) hc
    obtain ⟨y, hy, hyb⟩ := b.property
    have hycore : q y ∈ pCore 3 (StarGroup M) :=
      star_residual_le_threeCore hp (mem_map_of_mem q hy)
    have heq : r * q y * r⁻¹ = q y :=
      congrArg (fun j : MulAut (pCore 3 (StarGroup M)) =>
        (j ⟨q y, hycore⟩ : StarGroup M)) ha
    have heq' : d.actor (r₀ * y * r₀⁻¹) = d.actor y := by
      have he := congrArg f heq
      rw [map_mul, map_mul, map_inv] at he
      change d.actor r₀ * d.actor y * (d.actor r₀)⁻¹ = d.actor y at he
      simpa only [map_mul, map_inv] using he
    have hyinv : d.actor y = (d.actor y)⁻¹ := heq'.symm.trans (hinv y hy)
    exact hb (by rwa [hyb] at hyinv)
  refine ⟨r, hrmem, hrorder, (MonoidHom.ker_eq_bot_iff _).mp ?_⟩
  apply eq_bot_iff.mpr
  rintro ⟨x, hx⟩ hxker
  have hxval : x = 1 ∨ x = r := by
    rw [mem_zpowers_iff_mem_range_orderOf, hrorder] at hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hnlt := Finset.mem_range.mp hn
    interval_cases n <;> simp
  rcases hxval with rfl | rfl
  · exact mem_bot.mpr rfl
  · exact (hanontrivial hxker).elim

/-- Apply genuine 14.1.17(4), discharging its cyclic-action faithfulness premise. -/
public theorem exists_star_inverter_cyclic_centralizer (h : SourceInputs M Mc V T d)
    (hp : IsPGroup 3 (star M (residualY M Mc))) :
    ∃ r : StarGroup M, r ∈ star M (Rc M Mc) ∧ orderOf r = 2 ∧
      ∀ S : Sylow 3 (centralizer (zpowers r : Set (StarGroup M))), IsCyclic S := by
  obtain ⟨r, hr, ho, hi⟩ := exists_faithful_star_inverter h hp
  refine ⟨r, hr, ho, h.faithful_cyclic r hr ?_ hi⟩
  intro hrone
  simp [hrone] at ho

/-- Every three-subgroup in the star centralizer of V is cyclic. -/
public theorem star_centralizer_three_subgroups_cyclic (h : SourceInputs M Mc V T d)
    (hp : IsPGroup 3 (star M (residualY M Mc)))
    (A : Subgroup (StarGroup M)) (hA : IsPGroup 3 A)
    (hAC : A ≤ star M (M ⊓ centralizer (V : Set G))) : IsCyclic A := by
  obtain ⟨r, hr, _, hc⟩ := exists_star_inverter_cyclic_centralizer h hp
  have hAZ : A ≤ centralizer (zpowers r : Set (StarGroup M)) :=
    hAC.trans (h.star_centralizes.trans (centralizer_le
      (zpowers_le.mpr ((le_sup_right : star M (Rc M Mc) ≤ _) hr))))
  let j := Subgroup.inclusion hAZ
  have hj : IsPGroup 3 j.range := hA.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  obtain ⟨S, hS⟩ := hj.exists_le_sylow
  let := hc S
  let i : A →* S := j.codRestrict S (fun a => hS ⟨a, rfl⟩)
  exact isCyclic_of_injective i (fun x y he =>
    Subgroup.inclusion_injective hAZ (congrArg Subtype.val he))

/-- A three-subgroup of C_M(V) embeds through the two-core quotient and is cyclic. -/
public theorem isCyclic_three_subgroup_of_le_actor_ker (h : SourceInputs M Mc V T d)
    (hp : IsPGroup 3 (star M (residualY M Mc)))
    (A : Subgroup M) (hA : IsPGroup 3 A) (hAC : A ≤ d.actor.ker) : IsCyclic A := by
  let q := QuotientGroup.mk' (pCore 2 M)
  have hAC' : A ≤ (M ⊓ centralizer (V : Set G)).subgroupOf M := by
    intro x hx
    have hxC : x ∈ (centralizer (V : Set G)).subgroupOf M := d.ker_actor ▸ hAC hx
    exact ⟨x.property, hxC⟩
  let := star_centralizer_three_subgroups_cyclic h hp (A.map q) (hA.map q) (map_mono hAC')
  have hinj : Function.Injective (q.domRestrict A) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    rintro ⟨x, hx⟩ hxker
    have hxq : x ∈ pCore 2 M := (QuotientGroup.eq_one_iff x).mp hxker
    exact mem_bot.mpr (Subtype.ext
      (disjoint_def.mp (hA.disjoint_of_coprime pCore_isPGroup (by decide)) hx hxq))
  exact isCyclic_of_injective (q.subgroupMap A) (fun x y he => hinj (congrArg Subtype.val he))

/-- The actual intersection has cyclic Sylow three-subgroups: its actor image is a two-group. -/
public theorem intersection_sylow_three_cyclic (h : SourceInputs M Mc V T d)
    (hp : IsPGroup 3 (star M (residualY M Mc)))
    (S : Sylow 3 (M ⊓ Mc : Subgroup G)) : IsCyclic S := by
  let i : (M ⊓ Mc : Subgroup G) →* M := Subgroup.inclusion inf_le_left
  let A := (S : Subgroup (M ⊓ Mc : Subgroup G)).map i
  have hA : IsPGroup 3 A := S.isPGroup'.map i
  have hAI : A ≤ (M ⊓ Mc).subgroupOf M := by
    rintro x ⟨s, _, rfl⟩
    exact s.property
  have hIimage : ((M ⊓ Mc).subgroupOf M).map d.actor =
      ((T : Subgroup G).subgroupOf M).map d.actor := by
    rw [h.intersection, subgroupOf_sup inf_le_left h.sylow_le, Subgroup.map_sup]
    have hc : ((M ⊓ centralizer (V : Set G)).subgroupOf M).map d.actor = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro x hx
      rw [d.ker_actor]
      exact hx.2
    rw [hc, bot_sup_eq]
  have hAtwo : IsPGroup 2 (A.map d.actor) :=
    ((T.isPGroup'.comap_subtype).map d.actor).to_le
      ((map_mono hAI).trans hIimage.le)
  have hAbot : A.map d.actor = ⊥ :=
    eq_bot_iff.mpr (disjoint_self.mp ((hA.map d.actor).disjoint_of_coprime hAtwo (by decide))).le
  let := isCyclic_three_subgroup_of_le_actor_ker h hp A hA ((Subgroup.map_eq_bot_iff _).mp hAbot)
  let e := (S : Subgroup (M ⊓ Mc : Subgroup G)).equivMapOfInjective i
    (Subgroup.inclusion_injective inf_le_left)
  exact isCyclic_of_injective e.toMonoidHom e.injective

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives.ExtraspecialBranch
