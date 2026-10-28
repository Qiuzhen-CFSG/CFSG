module

public import Theory.GroupTheory.PGroup.QuaternionCentralProductCubicCommutator
public import Theory.GroupAction.CoprimeSmallQuotient
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.GroupTheory.Nilpotent
public import Theory.ElementaryAbelian.ExtraspecialNormalCommutator

/-!
# Quaternion recognition from fixed index four

Let a group of order three act on a finite extraspecial two-group P, fixing
its center. If the fixed subgroup in P/Z(P) has index four, the literal action
commutator [P,A] is quaternion of order eight.

Coprime splitting in the elementary abelian quotient gives a moved subgroup
of order four. The fixed subgroup in P is normal: conjugation changes a fixed
element by a central commutator, which is also fixed. Consequently [P,A]
centralizes the fixed subgroup, and coprime decomposition identifies its center
with its intersection with Z(P). Normality and nontriviality put the central
line in [P,A], so its order is eight and its central quotient has order four.
Coprime commutator idempotence supplies a nontrivial cubic action on that
quotient and identifies the restricted action commutator with all of [P,A].
The intrinsic quaternion recognition theorem then applies.

The quotient action is kept explicit with its compatibility equation, so the
result applies to an already chosen quotient action without changing instances.
The concrete consumer uses conjugation on the actual octad restriction kernel.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.2, the definition of
Delta_H in §46, p.251, and the cubic class in 49.3(2). The fixed-point count
is an independent input; this lemma proves the subsequent recognition step.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

private theorem action_commutator_map
    {P V A : Type*} [Group P] [Group V] [Group A]
    [MulDistribMulAction A P] [MulDistribMulAction A V]
    (f : P →* V) (hf : Function.Surjective f)
    (he : ∀ a : A, ∀ x : P, f (a • x) = a • f x) :
    (commutatorAction A P).map f = commutatorAction A V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, y, rfl⟩, rfl⟩
    exact ⟨a, f y, by rw [map_mul, map_inv, he]⟩
  · rintro ⟨a, y, rfl⟩
    obtain ⟨z, rfl⟩ := hf y
    exact ⟨z⁻¹ * (a • z), ⟨a, z, rfl⟩, by rw [map_mul, map_inv, he]⟩

private theorem fixed_normal_of_class_two
    {P A : Type*} [Group P] [Group A] [MulDistribMulAction A P]
    (hclass : _root_.commutator P ≤ center P)
    (hfix : ∀ a : A, ∀ z : center P, a • (z : P) = z) :
    (fixedPointSubgroup A P).Normal := by
  constructor
  intro x hx y a
  have hc : ⁅y, x⁆ ∈ center P := hclass
    (commutator_mem_commutator (mem_top y) (mem_top x))
  have he : y * x * y⁻¹ = ⁅y, x⁆ * x := by
    simp [commutatorElement_def, mul_assoc]
  rw [he, smul_mul', hfix a ⟨_, hc⟩, hx a]

private theorem moved_center_of_class_two
    {P A : Type*} [Group P] [Group A] [Finite P] [Finite A]
    [MulDistribMulAction A P]
    (hs : Group.IsSolvable P) (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (hclass : _root_.commutator P ≤ center P)
    (hfix : ∀ a : A, ∀ z : center P, a • (z : P) = z) :
    center (commutatorAction A P) = (center P).subgroupOf (commutatorAction A P) := by
  let C := commutatorAction A P
  let F := fixedPointSubgroup A P
  let : F.Normal := fixed_normal_of_class_two hclass hfix
  have hCF : C ≤ centralizer (F : Set P) :=
    commutatorAction_le_centralizer_of_fixed_normal F (fun a _ hx => hx a)
  have hgen : F ⊔ C = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime hs hcop
  ext x
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨f, hf, c, hc, rfl⟩ := mem_sup_of_normal_left.mp (hgen ▸ mem_top y)
    have hfcomm : Commute f (x : P) := hCF x.property f hf
    have hccomm : Commute c (x : P) :=
      congrArg Subtype.val (mem_center_iff.mp hx (⟨c, hc⟩ : C))
    exact (hfcomm.mul_left hccomm).eq
  · intro hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hx y)

/-- Fixed index four in the central quotient recognizes the action commutator
as quaternion-eight. The quotient action must be the action induced from P. -/
public theorem IsExtraspecial.nonempty_commutatorAction_equiv_quaternion_of_fixed_index_four
    {P A : Type*} [Group P] [Group A] [Finite P] [Finite A]
    [MulDistribMulAction A P] [MulDistribMulAction A (P ⧸ center P)]
    (hP : IsExtraspecial 2 P) (hA : Nat.card A = 3)
    (hfix : ∀ a : A, ∀ z : center P, a • (z : P) = z)
    (he : ∀ a : A, ∀ x : P,
      QuotientGroup.mk' (center P) (a • x) = a • QuotientGroup.mk' (center P) x)
    (hcard : Nat.card (P ⧸ center P) =
      Nat.card (fixedPointSubgroup A (P ⧸ center P)) * 4) :
    Nonempty (commutatorAction A P ≃* QuaternionGroup 2) := by
  let := hP
  have hp : IsPGroup 2 P := IsExtraspecial.isPGroup 2 P
  let : Group.IsNilpotent P := hp.isNilpotent
  have hs : Group.IsSolvable P := inferInstance
  have hcop : Nat.Coprime (Nat.card A) (Nat.card P) := by
    rw [hA]
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let V := P ⧸ center P
  let π : P →* V := QuotientGroup.mk' (center P)
  let C := commutatorAction A P
  let D := commutatorAction A V
  let F := fixedPointSubgroup A V
  let : IsElementaryAbelian 2 V := IsExtraspecial.quotient_elementary_abelian 2 P
  have hsplit : IsCompl F D :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun x y : V => mul_comm x y))
      (hcop.of_dvd_right (center P).index_dvd_card) inferInstance
  have hprod : Nat.card V = Nat.card F * Nat.card D := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint F D
      le_normalizer_of_normal hsplit.disjoint
    simpa only [hsplit.sup_eq_top, card_top] using hh
  have hD : Nat.card D = 4 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F from Nat.card_pos)
    exact hprod.symm.trans hcard
  have hmap : C.map π = D := action_commutator_map π (QuotientGroup.mk'_surjective _) he
  have hcenter : center C = (center P).subgroupOf C :=
    moved_center_of_class_two hs hcop
      (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient hfix
  have hfour : Nat.card (C ⧸ center C) = 4 := by
    rw [hcenter, ← natCard_map_mk'_eq, hmap]
    exact hD
  let : C.Normal := commutatorAction_normal
  have hCne : C ≠ ⊥ := by
    intro hb
    have hh : Nat.card D = 1 := by rw [← hmap, hb, Subgroup.map_bot, card_bot]
    omega
  have hZC : center P ≤ C := extraspecial_center_le_of_normal_ne_bot C hCne
  have hZcard : Nat.card (center C) = 2 := by
    rw [hcenter, natCard_subgroupOf_eq _ _ hZC, IsExtraspecial.center_order_p 2 P]
  have hCcard : Nat.card C = 8 := by
    rw [(center C).card_eq_card_quotient_mul_card_subgroup, hfour, hZcard]
  let : IsInvariant A P C := commutatorAction_isInvariant
  have hCC : (commutatorAction A C).map C.subtype = C :=
    commutatorAction_map_eq_of_coprime_of_le C hs hcop le_rfl
  have hfixC : ∀ a : A, ∀ z : center C, a • (z : C) = z := by
    intro a z
    apply Subtype.ext
    exact hfix a ⟨z.val.val, hcenter.le z.property⟩
  have hmove : ∃ a : A, ∃ x : C, (a • x) * x⁻¹ ∉ center C := by
    by_contra hn
    push Not at hn
    have hle : commutatorAction A C ≤ center C := by
      rw [commutatorAction_eq_closure, closure_le]
      rintro _ ⟨a, x, rfl⟩
      have hh := (inferInstance : (center C).Normal).conj_mem _ (hn a x) x⁻¹
      convert hh using 1
      group
      rfl
    have hCZ : C ≤ center P := by
      rw [← hCC]
      rintro _ ⟨x, hx, rfl⟩
      exact hcenter.le (hle hx)
    have hh := Subgroup.card_le_of_le hCZ
    rw [hCcard, IsExtraspecial.center_order_p 2 P] at hh
    omega
  obtain ⟨e⟩ :=
    (hp.to_subgroup C).nonempty_commutatorAction_equiv_quaternion_of_center_quotient_four
      hfour hA hfixC hmove
  let j : commutatorAction A C →* C := (commutatorAction A C).subtype
  have hj : Function.Bijective j := ⟨Subtype.val_injective, by
    intro c
    have hc : (c : P) ∈ (commutatorAction A C).map C.subtype := hCC.symm ▸ c.property
    obtain ⟨x, hx, heq⟩ := hc
    exact ⟨⟨x, hx⟩, Subtype.ext heq⟩⟩
  exact ⟨(MulEquiv.ofBijective j hj).symm.trans e⟩
