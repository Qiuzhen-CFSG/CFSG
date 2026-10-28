module

public import Theory.SpecificGroups.Tits.ConverseLocalCores.FirstCertificate
public import Theory.GroupTheory.Fitting.Centralizer
public import Mathlib.Data.Finite.Perm

/-!
# Characteristic two in the first Tits parabolic

The Sylow subgroup has index five. The kernel of its coset action is a
two-group, and the quotient has order dividing gcd(120,10240) = 40. Every
group of order dividing 40 has a normal Sylow five-subgroup and a two-group
quotient, so the actual first parabolic is solvable.

The five checked rotation conjugates place s2 in the two-core. If the odd
core were nontrivial, its order would be five, and it would contain the
specified rotation. Disjoint normal cores commute, contradicting the
checked failure of this rotation to commute with s2. Solvable Fitting
self-centralization therefore gives the required intrinsic core bound.

Source: the condition E in Aschbacher–Smith, Theorem 0.1.2(1), printed
pp.3–4 and 481–482; the concrete words are from Parrott (1972), p.683.
No disputed core order or quotient structure from F.1.12(I)(9) is assumed.
-/

namespace Tits.ConverseLocalCores
open Subgroup ExceptionalParabolics OuterOddSubgroups.OverlapCentralizers

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem solvable_of_card_dvd_forty {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G ∣ 40) : Group.IsSolvable G := by
  let P : Sylow 5 G := Classical.choice inferInstance
  have hi : (P : Subgroup G).index ∣ 8 := by
    have hcop : Nat.Coprime (P : Subgroup G).index 5 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr P.not_dvd_index).symm
    exact hcop.dvd_of_dvd_mul_left ((P : Subgroup G).index_dvd_card.trans hc)
  have hcount : Nat.card (Sylow 5 G) = 1 := by
    have hd := P.card_dvd_index.trans hi
    have hm := card_sylow_modEq_one 5 G
    change Nat.card (Sylow 5 G) % 5 = 1 % 5 at hm
    have hd' : Nat.card (Sylow 5 G) ∣ 2 ^ 3 := hd
    obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
    interval_cases n
    · simpa using he
    all_goals norm_num [he] at hm
  let : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp hcount).1
  let : (P : Subgroup G).Normal := P.normal_of_subsingleton
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have htwo : IsPGroup 2 (G ⧸ (P : Subgroup G)) :=
    IsPGroup.of_card_dvd_pow (n := 3) hi
  let : Group.IsNilpotent (G ⧸ (P : Subgroup G)) := htwo.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (P : Subgroup G)).2
    ⟨inferInstance, inferInstance⟩

private theorem first_sylow_index : (S.subgroupOf first).index = 5 := by
  have h := relIndex_mul_relIndex (⊥ : Subgroup Atlas1600Group) S first bot_le sylow_le_first
  rw [relIndex_bot_left, relIndex_bot_left, sylow_card, ReeLocalBlockOrders.first_card] at h
  change S.relIndex first = 5
  omega

private theorem first_solvable : Group.IsSolvable first := by
  classical
  let T := S.subgroupOf first
  let Q := first ⧸ T.normalCore
  have h120 : Nat.card Q ∣ 120 := by
    change T.normalCore.index ∣ 120
    rw [normalCore_eq_ker, index_ker]
    have h := (MulAction.toPermHom first (first ⧸ T)).range.card_subgroup_dvd_card
    have hperm : Nat.card (Equiv.Perm (first ⧸ T)) = 120 := by
      rw [Nat.card_perm]
      change T.index.factorial = 120
      rw [first_sylow_index]
      decide
    rwa [hperm] at h
  have h10240 : Nat.card Q ∣ 10240 := by
    change T.normalCore.index ∣ 10240
    simpa only [ReeLocalBlockOrders.first_card] using T.normalCore.index_dvd_card
  have h40 : Nat.card Q ∣ 40 := Nat.dvd_gcd h120 h10240
  let : Group.IsSolvable Q := solvable_of_card_dvd_forty h40
  have hS : IsPGroup 2 S := IsPGroup.of_card (n := 11) (by simpa using sylow_card)
  let : Group.IsNilpotent T.normalCore :=
    (hS.comap_subtype.to_le T.normalCore_le).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient T.normalCore).2
    ⟨inferInstance, inferInstance⟩

private theorem s_mem (i : ParrottGenerator) (hi : i ≠ .r1) (hi8 : i ≠ .r8) :
    atlas1600ParrottAssignment i ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  apply subset_closure
  cases i <;> simp_all

private def root : first :=
  ⟨atlas1600ParrottAssignment .s2, sylow_le_first (s_mem .s2 (by decide) (by decide))⟩
private def rotation : first := ⟨firstRotation, by
  exact first.mul_mem (sylow_le_first (s_mem .s1 (by decide) (by decide))) reflection_mem_first⟩

private theorem root_mem_core : root ∈ pCore 2 first := by
  let T := S.subgroupOf first
  have hn : root ∈ T.normalCore := by
    intro b
    obtain ⟨⟨n,j⟩, rfl⟩ := firstNormalForm_surjective b
    change (atlas1600SylowTwoNormalForm n * firstRotation ^ j.val) *
      atlas1600ParrottAssignment .s2 *
      (atlas1600SylowTwoNormalForm n * firstRotation ^ j.val)⁻¹ ∈ S
    have he : (atlas1600SylowTwoNormalForm n * firstRotation ^ j.val) *
        atlas1600ParrottAssignment .s2 *
        (atlas1600SylowTwoNormalForm n * firstRotation ^ j.val)⁻¹ =
        atlas1600SylowTwoNormalForm n *
        (firstRotation ^ j.val * atlas1600ParrottAssignment .s2 * (firstRotation ^ j.val)⁻¹) *
        (atlas1600SylowTwoNormalForm n)⁻¹ := by group
    rw [he]
    exact S.mul_mem (S.mul_mem (atlas1600SylowTwoNormalForm_mem _)
      (FirstCertificate.root_conjugate_mem _)) (S.inv_mem (atlas1600SylowTwoNormalForm_mem _))
  apply (show T.normalCore ≤ pCore 2 first from ?_) hn
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  have hS : IsPGroup 2 S := IsPGroup.of_card (n := 11) (by simpa using sylow_card)
  exact hS.comap_subtype.to_le T.normalCore_le

private theorem root_rotation_ne : root * rotation ≠ rotation * root := by
  intro h
  have hv := congrArg (fun g : first => g.val.val 0) h
  have hn : (Atlas1600ParrottData.s2Perm *
        (Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm)) 0 ≠
      ((Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm) *
        Atlas1600ParrottData.s2Perm) 0 := by decide +kernel
  apply hn
  change ((atlas1600ParrottAssignment .s2).val *
      ((atlas1600ParrottAssignment .s1).val * (atlas1600ParrottAssignment .r1).val)) 0 =
    (((atlas1600ParrottAssignment .s1).val * (atlas1600ParrottAssignment .r1).val) *
      (atlas1600ParrottAssignment .s2).val) 0 at hv
  simpa only [atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation] using hv

private theorem rotation_order : orderOf rotation = 5 :=
  (Subgroup.orderOf_coe rotation).symm.trans firstRotation_order

private noncomputable def rotationSylow : Sylow 5 first := by
  have hp : IsPGroup 5 (zpowers rotation) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, rotation_order]; rfl)
  apply hp.toSylow
  have hi : (zpowers rotation).index = 2048 := by
    have h := (zpowers rotation).card_mul_index
    rw [Nat.card_zpowers, rotation_order, ReeLocalBlockOrders.first_card] at h
    omega
  rw [hi]
  decide

private theorem first_odd_core_eq_bot : pPrimeCore 2 first = ⊥ := by
  let O := pPrimeCore 2 first
  have hcop : Nat.Coprime (Nat.card O) (2 ^ 11) :=
    (pPrimeCore_coprime_card (p := 2) (G := first)).symm.pow_right 11
  have hdiv : Nat.card O ∣ 2 ^ 11 * 5 := by
    simpa only [ReeLocalBlockOrders.first_card, show 2 ^ 11 * 5 = 10240 by norm_num]
      using O.card_subgroup_dvd_card
  have hdiv5 : Nat.card O ∣ 5 := hcop.dvd_of_dvd_mul_left hdiv
  rcases (Nat.dvd_prime Nat.prime_five).mp hdiv5 with hone | hfive
  · exact Subgroup.card_eq_one.mp hone
  · have hO5 : IsPGroup 5 O := IsPGroup.of_card (p := 5) (n := 1) (by simpa using hfive)
    have hOP : O = (rotationSylow : Subgroup first) :=
      eq_of_le_of_card_ge (hO5.le_sylow_of_normal rotationSylow) (by
        change Nat.card (zpowers rotation) ≤ Nat.card O
        rw [Nat.card_zpowers, rotation_order, hfive])
    have hr : rotation ∈ O := by rw [hOP]; exact mem_zpowers rotation
    have hdis : Disjoint (pCore 2 first) O :=
      IsPGroup.disjoint_of_ne 2 5 (by decide) _ _ pCore_isPGroup hO5
    have hcent : pCore 2 first ≤ centralizer (O : Set first) :=
      commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdis)
    exact (root_rotation_ne (mem_centralizer_iff.mp (hcent root_mem_core) rotation hr).symm).elim

/-- The intrinsic two-core of the first marked parabolic is self-centralizing. -/
public theorem first_core_self_centralizing :
    centralizer (pCore 2 first : Set first) ≤ pCore 2 first := by
  have hfit : fittingSubgroup first = pCore 2 first :=
    Fitting_eq_pcore first 2 first_odd_core_eq_bot
  rw [← hfit]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable first_solvable
end Tits.ConverseLocalCores
