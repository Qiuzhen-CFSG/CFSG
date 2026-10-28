module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.ActorSubtypeCommutator
public import Theory.GroupAction.Quotient
public import Theory.ElementaryAbelian.Basic

public import Theory.GroupAction.Quadratic
public import Mathlib.Data.Fintype.Perm

/-!
# Reduction of a small-displacement odd centralizer

A centralizing automorphism fixing the actor displacement fixes the full
module, by passing to its fixed-point quotient and using commutator generation.
Consequently an odd centralizer acts faithfully on the displacement. If that
elementary two-group has at most four elements, the centralizer is trivial or
has order three. In the latter case the displacement has order four and the
centralizer acts fully on the entire module.

The generic fixed-subgroup arguments are exported independently of the private
proofs in `Extraspecial27CenterAction`. No classification theorem is used.
The last two results also record the elementary-abelian and normalization
consequences needed for the separate quadratic-four representation obstruction.
-/

@[expose] public section

open scoped IsMulCommutative commutatorElement

universe u v

namespace QuadraticFourCentralizer

theorem central_fixed_subgroup_isInvariant
    {G : Type u} {V : Type v} [Group G] [Group V]
    [MulDistribMulAction G V] (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) :
    IsInvariant G V (FixedPoints.subgroup Z V) := by
  have hforward (g : G) (point : V) (hpoint : point ∈ FixedPoints.subgroup Z V) :
      g • point ∈ FixedPoints.subgroup Z V := by
    rw [FixedPoints.mem_subgroup] at hpoint ⊢
    intro central
    have hcomm := Subgroup.mem_center_iff.mp (hZ central.property) g
    change (central : G) • (g • point) = g • point
    rw [← mul_smul, ← hcomm, mul_smul]
    exact congrArg (fun value : V => g • value) (hpoint central)
  constructor
  intro g point
  constructor
  · exact hforward g point
  · intro hpoint
    simpa using hforward g⁻¹ (g • point) hpoint

theorem invariant_subgroup_eq_top_of_commutator_relations
    {G : Type u} {V : Type v} [Group G] [Group V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (F R : Subgroup G) (W : Subgroup V)
    (hWinv : IsInvariant G V W)
    (hcommRle : commutatorAction R V ≤ W)
    (hcommFR : ⁅F, R⁆ = F)
    (hcommFV : commutatorAction F V = ⊤) :
    W = ⊤ := by
  classical
  let hWnorm : W.Normal := Subgroup.normal_of_isMulCommutative W
  let _ : W.Normal := hWnorm
  let _ : IsInvariant G V W := hWinv
  let _ : MulDistribMulAction G (V ⧸ W) :=
    quotientMulDistribMulAction (A := G) (G := V) W hWinv
  let ρ : G →* MulAut (V ⧸ W) := MulDistribMulAction.toMulAut G (V ⧸ W)
  have hRmap : R.map ρ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker]
    ext qv
    refine QuotientGroup.induction_on qv ?_
    intro v
    change (((r • v : V) : V ⧸ W)) = (v : V ⧸ W)
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hgen : v⁻¹ * (r • v) ∈ commutatorAction R V := by
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨r, hr⟩, v, rfl⟩
    simpa [div_eq_mul_inv, mul_comm] using hcommRle hgen
  have hFmap : F.map ρ = ⊥ := by
    calc
      F.map ρ = (⁅F, R⁆).map ρ := by rw [hcommFR]
      _ = ⁅F.map ρ, R.map ρ⁆ := Subgroup.map_commutator F R ρ
      _ = ⊥ := by simp [hRmap]
  have hFker : F ≤ ρ.ker := (Subgroup.map_eq_bot_iff F).mp hFmap
  have hcommFle : commutatorAction F V ≤ W := by
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := W)).2 ?_
    rintro d ⟨f, v, rfl⟩
    have hρf : ρ (f : G) = 1 := MonoidHom.mem_ker.mp (hFker f.property)
    have hq : (((f : G) • v : V) : V ⧸ W) = (v : V ⧸ W) := by
      change ρ (f : G) (v : V ⧸ W) = (v : V ⧸ W)
      rw [hρf]
      rfl
    have hdiv : ((f : G) • v) / v ∈ W :=
      QuotientGroup.eq_iff_div_mem.mp hq
    rw [(IsMulCommutative.is_comm (M := V)).comm v⁻¹ (f • v)]
    change ((f : G) • v) * v⁻¹ ∈ W
    simpa [div_eq_mul_inv] using hdiv
  apply top_unique
  rw [← hcommFV]
  exact hcommFle

theorem central_eq_one_of_fixes_commutator
    {G : Type u} {V : Type v} [Group G] [Group V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (F R : Subgroup G) (central : G) (hcentral : central ∈ Subgroup.center G)
    (hgenerates : ⁅F, R⁆ = F) (hfull : commutatorAction F V = ⊤)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hfix : ∀ point ∈ commutatorAction R V, central • point = point) :
    central = 1 := by
  let Z := Subgroup.zpowers central
  let C := FixedPoints.subgroup Z V
  have hZ : Z ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hcentral
  have hinvariant : IsInvariant G V C := central_fixed_subgroup_isInvariant Z hZ
  have hcontains : commutatorAction R V ≤ C := by
    intro point hpoint
    rw [FixedPoints.mem_subgroup]
    intro actor
    obtain ⟨power, hpower⟩ := Subgroup.mem_zpowers_iff.mp actor.property
    change (actor : G) • point = point
    rw [← hpower]
    exact MulAction.mem_fixedBy_zpow (MulAction.mem_fixedBy.mpr (hfix point hpoint)) power
  have htop : C = ⊤ := invariant_subgroup_eq_top_of_commutator_relations
    F R C hinvariant hcontains hgenerates hfull
  have hglobal : central ∈ fixingSubgroup G (Set.univ : Set V) := by
    rw [mem_fixingSubgroup_iff]
    intro point _
    have hpoint : point ∈ C := by rw [htop]; exact Subgroup.mem_top _
    exact (FixedPoints.mem_subgroup (M := Z) (a := point)).mp hpoint
      ⟨central, Subgroup.mem_zpowers central⟩
  simpa [hfaith] using hglobal

theorem order_three_faithful_card_four_commutatorAction_eq_top
    {A : Type u} {U : Type v} [Group A] [Group U]
    [Finite A] [Finite U] [IsElementaryAbelian 2 U]
    [MulDistribMulAction A U]
    (hcardA : Nat.card A = 3) (hcardU : Nat.card U = 4)
    (hfaith : fixingSubgroup A (Set.univ : Set U) = ⊥) :
    commutatorAction A U = ⊤ := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hcardA)
  let C : Subgroup U := FixedPoints.subgroup A U
  have hcardCle : Nat.card C ≤ 4 := by
    rw [← hcardU]
    simpa using Subgroup.card_le_of_le (show C ≤ (⊤ : Subgroup U) from le_top)
  have hmod : Nat.ModEq 3 4 (Nat.card C) := by
    have := hAp.card_modEq_card_fixedPoints U
    change Nat.ModEq 3 (Nat.card U)
      (Nat.card (FixedPoints.subgroup A U)) at this
    simpa [C, hcardU] using this
  have hcardC : Nat.card C = 1 ∨ Nat.card C = 4 := by
    have hpos : 0 < Nat.card C := Nat.card_pos
    have hneTwo : Nat.card C ≠ 2 := by
      intro h
      rw [h] at hmod
      norm_num [Nat.ModEq] at hmod
    have hneThree : Nat.card C ≠ 3 := by
      intro h
      rw [h] at hmod
      norm_num [Nat.ModEq] at hmod
    omega
  have hCneTop : C ≠ ⊤ := by
    intro hCtop
    have hAnontrivial : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcardA]
      norm_num)
    obtain ⟨a, hane⟩ := exists_ne (1 : A)
    have haFix : a ∈ fixingSubgroup A (Set.univ : Set U) := by
      rw [mem_fixingSubgroup_iff]
      intro u _
      have huC : u ∈ C := by rw [hCtop]; exact Subgroup.mem_top u
      exact (FixedPoints.mem_subgroup (M := A) (a := u)).mp huC a
    rw [hfaith] at haFix
    exact hane (by simpa using haFix)
  have hCbot : C = ⊥ := by
    apply (Subgroup.card_eq_one (H := C)).mp
    exact hcardC.resolve_right (fun h => hCneTop
      ((Subgroup.card_eq_iff_eq_top C).mp (by simpa [hcardU] using h)))
  have hcop : Nat.Coprime (Nat.card A) (Nat.card U) := by
    rw [hcardA, hcardU]
    norm_num
  have hsup := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := U) (A := A)
    (Group.isSolvable_of_comm fun a b =>
      (IsMulCommutative.is_comm (M := U)).comm a b) hcop
  change C ⊔ commutatorAction A U = ⊤ at hsup
  rwa [hCbot, bot_sup_eq] at hsup

theorem central_three_action
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (F R Z : Subgroup G) (hcentral : Z ≤ Subgroup.center G)
    (hgenerates : ⁅F, R⁆ = F) (hfull : commutatorAction F V = ⊤)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥)
    (hcardZ : Nat.card Z = 3) (hcardU : Nat.card (commutatorAction R V) = 4) :
    commutatorAction Z V = ⊤ ∧
      ∀ central : Z, (∀ point ∈ commutatorAction R V,
        (central : G) • point = point) → central = 1 := by
  classical
  have hfaithful : ∀ central : Z, (∀ point ∈ commutatorAction R V,
      (central : G) • point = point) → central = 1 := by
    intro central hfix
    apply Subtype.ext
    exact central_eq_one_of_fixes_commutator F R central (hcentral central.property)
      hgenerates hfull hfaith hfix
  refine ⟨?_, hfaithful⟩
  let U := commutatorAction R V
  let W := commutatorAction Z V
  let _ : IsElementaryAbelian 2 U :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro point
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 V) (point : V) }
  have hZnormalizes : Z ≤ Subgroup.normalizer (R : Set G) :=
    hcentral.trans (Subgroup.center_le_normalizer _)
  let _ : IsInvariant Z V U :=
    commutatorAction_isInvariant_of_normalizing_actor Z R hZnormalizes
  have hfaithU : fixingSubgroup Z (Set.univ : Set U) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro central hfix
    apply hfaithful central
    intro point hpoint
    rw [mem_fixingSubgroup_iff] at hfix
    exact congrArg Subtype.val (hfix ⟨point, hpoint⟩ (Set.mem_univ _))
  have hcommU : commutatorAction Z U = ⊤ :=
    order_three_faithful_card_four_commutatorAction_eq_top hcardZ hcardU hfaithU
  have hmap : (commutatorAction Z U).map U.subtype ≤ W := by
    rw [Subgroup.map_le_iff_le_comap, commutatorAction_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro displacement ⟨central, point, rfl⟩
    change (point : V)⁻¹ * (central : G) • (point : V) ∈ commutatorAction Z V
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨central, (point : V), rfl⟩
  have hcontains : U ≤ W := by
    intro point hpoint
    have hmem : (⟨point, hpoint⟩ : U) ∈ commutatorAction Z U := by
      rw [hcommU]; exact Subgroup.mem_top _
    exact hmap (Subgroup.mem_map_of_mem U.subtype hmem)
  have hnormalizes : (⊤ : Subgroup G) ≤ Subgroup.normalizer (Z : Set G) := by
    intro actor _
    rw [Subgroup.mem_normalizer_iff]
    intro central
    constructor
    · intro hmem
      have hcomm := Subgroup.mem_center_iff.mp (hcentral hmem) actor
      simpa [hcomm, mul_assoc] using hmem
    · intro hmem
      have hcomm := Subgroup.mem_center_iff.mp (hcentral hmem) actor⁻¹
      have heq : actor⁻¹ * (actor * central * actor⁻¹) * actor = central := by group
      have hcancel : actor⁻¹ * (actor * central * actor⁻¹) * actor ∈ Z := by
        rw [hcomm]
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmem
      rwa [heq] at hcancel
  have htopInvariant : IsInvariant (⊤ : Subgroup G) V W :=
    commutatorAction_isInvariant_of_normalizing_actor ⊤ Z hnormalizes
  have hinvariant : IsInvariant G V W := by
    let _ := htopInvariant
    constructor
    intro actor point
    exact IsInvariant.invariant (A := (⊤ : Subgroup G))
      (⟨actor, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) point
  exact invariant_subgroup_eq_top_of_commutator_relations
    F R W hinvariant hcontains hgenerates hfull

theorem centralizer_eq_one_of_fixes_displacement
    {W : Type*} [Group W] [IsMulCommutative W]
    (F J : Subgroup (MulAut W)) (central : MulAut W)
    (hCF : central ∈ Subgroup.centralizer (F : Set (MulAut W)))
    (hCJ : central ∈ Subgroup.centralizer (J : Set (MulAut W)))
    (hgenerate : ⁅F, J⁆ = F) (hfull : commutatorAction F W = ⊤)
    (hfix : ∀ point ∈ commutatorAction J W, central point = point) :
    central = 1 := by
  let E := Subgroup.centralizer ({central} : Set (MulAut W))
  have hFE : F ≤ E := by
    intro actor hactor
    rw [Subgroup.mem_centralizer_iff]
    rintro element (rfl : element = central)
    exact (Subgroup.mem_centralizer_iff.mp hCF actor hactor).symm
  have hJE : J ≤ E := by
    intro actor hactor
    rw [Subgroup.mem_centralizer_iff]
    rintro element (rfl : element = central)
    exact (Subgroup.mem_centralizer_iff.mp hCJ actor hactor).symm
  have hCE : central ∈ E := by
    rw [Subgroup.mem_centralizer_iff]
    rintro element (rfl : element = central)
    rfl
  let central' : E := ⟨central, hCE⟩
  have hcentral : central' ∈ Subgroup.center E := by
    rw [Subgroup.mem_center_iff]
    intro actor
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp actor.property central (Set.mem_singleton _)).symm
  have hcomm : ⁅F.subgroupOf E, J.subgroupOf E⁆ = F.subgroupOf E := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hFE,
      Subgroup.map_subgroupOf_eq_of_le hJE, hgenerate]
  have hfull' : commutatorAction (F.subgroupOf E) W = ⊤ := by
    rw [← commutatorAction_map_actor_subtype E,
      Subgroup.map_subgroupOf_eq_of_le hFE, hfull]
  have hfaith : fixingSubgroup E (Set.univ : Set W) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro actor hactor
    apply Subtype.ext
    ext point
    rw [mem_fixingSubgroup_iff] at hactor
    exact hactor point (Set.mem_univ _)
  have hone : central' = 1 := by
    apply central_eq_one_of_fixes_commutator (F.subgroupOf E) (J.subgroupOf E)
      central' hcentral hcomm hfull' hfaith
    intro point hpoint
    rw [← commutatorAction_map_actor_subtype E,
      Subgroup.map_subgroupOf_eq_of_le hJE] at hpoint
    exact hfix point hpoint
  exact congrArg Subtype.val hone

theorem odd_faithful_small_action_card
    {A U : Type*} [Group A] [Group U] [Finite A] [Finite U]
    [IsElementaryAbelian 2 U] [MulDistribMulAction A U]
    (hodd : Odd (Nat.card A)) (hne : Nat.card A ≠ 1)
    (hsmall : Nat.card U ≤ 4)
    (hfaith : fixingSubgroup A (Set.univ : Set U) = ⊥) :
    Nat.card A = 3 ∧ Nat.card U = 4 := by
  classical
  let ρ : A →* Equiv.Perm U := MulAction.toPermHom A U
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro actor hactor
    have hfix : actor ∈ fixingSubgroup A (Set.univ : Set U) := by
      rw [mem_fixingSubgroup_iff]
      intro point _
      exact Equiv.congr_fun (MonoidHom.mem_ker.mp hactor) point
    simpa [hfaith] using hfix
  have hperm : Nat.card (Equiv.Perm U) = (Nat.card U).factorial := by
    let _ := Fintype.ofFinite U
    simp only [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hdiv : Nat.card A ∣ (Nat.card U).factorial := by
    rw [← hperm]
    exact Subgroup.card_dvd_of_injective ρ hinj
  have hdiv24 : Nat.card A ∣ 24 :=
    hdiv.trans (by simpa only [Nat.factorial] using Nat.factorial_dvd_factorial hsmall)
  have hcop : Nat.Coprime (Nat.card A) 8 := by
    exact (Nat.coprime_two_right.mpr hodd).pow_right 3
  have hdiv3 : Nat.card A ∣ 3 := hcop.dvd_of_dvd_mul_left hdiv24
  have hcardA : Nat.card A = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdiv3).resolve_left hne
  refine ⟨hcardA, ?_⟩
  have hUp := IsElementaryAbelian.isPGroup 2 U
  obtain ⟨dimension, hdimension⟩ := hUp.exists_card_eq
  have hdim : dimension ≤ 2 := by
    by_contra hnot
    have hlarge : 2 ^ 3 ≤ 2 ^ dimension := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  interval_cases dimension <;> norm_num at hdimension
  · rw [hcardA, hdimension] at hdiv
    norm_num at hdiv
  · rw [hcardA, hdimension] at hdiv
    norm_num at hdiv
  · exact hdimension

theorem nontrivial_odd_centralizer_full_three
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (F J K : Subgroup (MulAut W))
    (hfull : commutatorAction F W = ⊤) (hgenerate : ⁅F, J⁆ = F)
    (hsmall : Nat.card (commutatorAction J W) ≤ 4)
    (hKodd : Odd (Nat.card K)) (hKne : K ≠ ⊥)
    (hKF : ⁅K, F⁆ = ⊥) (hKJ : ⁅K, J⁆ = ⊥) :
    Nat.card K = 3 ∧ Nat.card (commutatorAction J W) = 4 ∧
      commutatorAction K W = ⊤ := by
  classical
  let U := commutatorAction J W
  have hKF' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKF
  have hKJ' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKJ
  let _ : IsInvariant K W U :=
    commutatorAction_isInvariant_of_normalizing_actor K J
      (hKJ'.trans (Subgroup.centralizer_le_normalizer _))
  let _ : IsElementaryAbelian 2 U :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro point
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 W) (point : W) }
  have hfaith : fixingSubgroup K (Set.univ : Set U) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro central hcentral
    apply Subtype.ext
    apply centralizer_eq_one_of_fixes_displacement F J central
      (hKF' central.property) (hKJ' central.property) hgenerate hfull
    intro point hpoint
    rw [mem_fixingSubgroup_iff] at hcentral
    exact congrArg Subtype.val (hcentral ⟨point, hpoint⟩ (Set.mem_univ _))
  obtain ⟨hKcard, hUcard⟩ := odd_faithful_small_action_card hKodd
    (fun hone => hKne (Subgroup.card_eq_one.mp hone)) hsmall hfaith
  refine ⟨hKcard, hUcard, ?_⟩
  have hKU : commutatorAction K U = ⊤ :=
    order_three_faithful_card_four_commutatorAction_eq_top hKcard hUcard hfaith
  let M := commutatorAction K W
  have hcontains : U ≤ M := by
    have hmap : (commutatorAction K U).map U.subtype ≤ M := by
      rw [Subgroup.map_le_iff_le_comap, commutatorAction_eq_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro displacement ⟨central, point, rfl⟩
      change (point : W)⁻¹ * (central : MulAut W) • (point : W) ∈ commutatorAction K W
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨central, (point : W), rfl⟩
    intro point hpoint
    have hmem : (⟨point, hpoint⟩ : U) ∈ commutatorAction K U := by
      rw [hKU]
      exact Subgroup.mem_top _
    exact hmap (Subgroup.mem_map_of_mem U.subtype hmem)
  let E := F ⊔ J
  have hFE : F ≤ E := le_sup_left
  have hJE : J ≤ E := le_sup_right
  have hEnorm : E ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    (sup_le (Subgroup.le_centralizer_iff.mp hKF')
      (Subgroup.le_centralizer_iff.mp hKJ')).trans
        (Subgroup.centralizer_le_normalizer _)
  have hMinv : IsInvariant E W M :=
    commutatorAction_isInvariant_of_normalizing_actor E K hEnorm
  have hcomm : ⁅F.subgroupOf E, J.subgroupOf E⁆ = F.subgroupOf E := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hFE,
      Subgroup.map_subgroupOf_eq_of_le hJE, hgenerate]
  have hfull' : commutatorAction (F.subgroupOf E) W = ⊤ := by
    rw [← commutatorAction_map_actor_subtype E,
      Subgroup.map_subgroupOf_eq_of_le hFE, hfull]
  apply invariant_subgroup_eq_top_of_commutator_relations
    (F.subgroupOf E) (J.subgroupOf E) M hMinv ?_ hcomm hfull'
  rw [← commutatorAction_map_actor_subtype E,
    Subgroup.map_subgroupOf_eq_of_le hJE]
  exact hcontains

theorem elementaryAbelian_of_quadratic
    {W : Type*} [Group W] [IsElementaryAbelian 2 W]
    (J : Subgroup (MulAut W)) (hquadratic : commutatorAction₂ J W = ⊥) :
    IsElementaryAbelian 2 J := by
  have hsquare (point : W) : point ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) point
  have hinverse (point : W) : point⁻¹ = point := by
    apply inv_eq_of_mul_eq_one_right
    exact (pow_two point).symm.trans (hsquare point)
  have hactor (actor : J) : actor ^ 2 = 1 := by
    apply Subtype.ext
    ext point
    have hdelta : point⁻¹ * (actor : MulAut W) point ∈ commutatorAction J W := by
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨actor, point, rfl⟩
    have hfixed := commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot
      hquadratic hdelta
    rw [FixedPoints.mem_subgroup] at hfixed
    specialize hfixed actor
    change (actor : MulAut W) (point⁻¹ * (actor : MulAut W) point) =
      point⁻¹ * (actor : MulAut W) point at hfixed
    simp only [map_mul, map_inv] at hfixed
    change (actor : MulAut W) ((actor : MulAut W) point) = point
    calc
      (actor : MulAut W) ((actor : MulAut W) point) =
          (actor : MulAut W) point *
            (((actor : MulAut W) point)⁻¹ * (actor : MulAut W) ((actor : MulAut W) point)) := by simp
      _ = (actor : MulAut W) point * (point⁻¹ * (actor : MulAut W) point) := by rw [hfixed]
      _ = point := by
        rw [hinverse, ← mul_assoc, mul_comm ((actor : MulAut W) point) point,
          mul_assoc, ← pow_two, hsquare, mul_one]
  exact
    { toIsMulCommutative :=
        ⟨⟨fun actor other => (Commute.of_orderOf_dvd_two
          (fun element => orderOf_dvd_of_pow_eq_one (hactor element)) actor other).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hactor }

theorem normalizes_of_commutator_eq
    {G : Type*} [Group G] (F J : Subgroup G) (hgenerate : ⁅F, J⁆ = F) :
    J ≤ Subgroup.normalizer (F : Set G) :=
  Subgroup.le_normalizer_iff_commutator_le_left.mpr hgenerate.le

end QuadraticFourCentralizer
