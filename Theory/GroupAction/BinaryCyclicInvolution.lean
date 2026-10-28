module

public import Theory.GroupAction.FourElementInvolutionLines
public import Theory.Comparator.Defs

/-!
# Binary cyclic involution actions

An involution on an elementary abelian two-group has square-zero displacement.
Consequently its action commutator is fixed pointwise, and the orders of the
fixed subgroup and the commutator multiply to the order of the module.
The cardinal identity reuses the order-two action theorem; the quadraticity
proof also allows the identity actor and does not require finiteness.

These are the elementary action facts used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, D.2.11(4), printed p.183.
-/

open scoped IsMulCommutative
universe u

/-- Rank-nullity for the action of a cyclic involution. -/
public theorem cyclicInvolution_card_eq_fixed_mul_commutator {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (t : G) (ht : IsInvolution t) :
    Nat.card V = Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V) *
      Nat.card (commutatorAction (Subgroup.zpowers t) V) := by
  classical
  cases subsingleton_or_nontrivial V with
  | inl h =>
    let _ := h
    simp only [Nat.card_unique, mul_one]
  | inr h =>
    let _ := h
    let s : Subgroup.zpowers t := ⟨t, Subgroup.mem_zpowers t⟩
    have hs : s ≠ 1 ∧ s ^ 2 = 1 :=
      ⟨fun he => ht.1 (congrArg Subtype.val he), Subtype.ext ht.2⟩
    exact (card_two_action_fixed_commutator_card_data (U := V) s hs
      (by rw [Nat.card_zpowers]; exact orderOf_eq_prime ht.2 ht.1)).1

/-- A binary involution fixes its displacement subgroup pointwise. -/
public theorem cyclicInvolution_commutator_le_fixed {G V : Type u} [Group G] [Group V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (t : G) (ht : t ^ 2 = 1) :
    commutatorAction (Subgroup.zpowers t) V ≤
      FixedPoints.subgroup (Subgroup.zpowers t) V := by
  have htt : t * t = 1 := by simpa only [pow_two] using ht
  have hinv (v : V) : v⁻¹ = v := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v
  rw [commutatorAction_eq_closure, Subgroup.closure_le]
  rintro _ ⟨s, v, rfl⟩
  have hs : (s : G) = 1 ∨ (s : G) = t := by
    by_cases htid : t = 1
    · left
      simpa [htid] using s.property
    · have hcard : Nat.card (Subgroup.zpowers t) = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime ht htid]
      obtain ⟨other, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.zpowers t)).mp hcard
      by_cases hs : s = 1
      · exact Or.inl (congrArg Subtype.val hs)
      · right
        exact congrArg Subtype.val ((huniq s hs).trans
          (huniq ⟨t, Subgroup.mem_zpowers t⟩
            (fun he => htid (congrArg Subtype.val he))).symm)
  intro a
  rcases hs with hs | hs
  · change (a : G) • (v⁻¹ * (s : G) • v) = v⁻¹ * (s : G) • v
    simp [hs]
  · have hfixed : t • (v⁻¹ * t • v) = v⁻¹ * t • v := by
      simp only [smul_mul', ← mul_smul, htt, one_smul, hinv]
      exact mul_comm _ _
    change (a : G) • (v⁻¹ * (s : G) • v) = v⁻¹ * (s : G) • v
    rw [hs]
    exact smul_eq_self_of_mem_zpowers a.property hfixed

/-- The cyclic action of a binary involution is quadratic. -/
public theorem cyclicInvolution_quadratic
    {G V : Type u} [Group G] [Group V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (t : G) (ht : t ^ 2 = 1) :
    commutatorAction₂ (Subgroup.zpowers t) V = ⊥ := by
  apply bot_unique
  change Subgroup.closure _ ≤ ⊥
  rw [Subgroup.closure_le]
  rintro _ ⟨a, v, hv, rfl⟩
  have hfix := cyclicInvolution_commutator_le_fixed t ht hv a
  change v⁻¹ * (a • v) = 1
  rw [hfix, inv_mul_cancel]
