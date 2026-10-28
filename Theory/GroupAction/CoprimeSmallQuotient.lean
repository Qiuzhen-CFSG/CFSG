module

public import Theory.GroupAction.CoprimeCommutatorContainment
public import Theory.GroupAction.Quotient

/-!
# Coprime commutators through a quotient of order at most two

An action on a group of order at most two is trivial. Consequently, if a
coprime commutator lies in an invariant subgroup M and an invariant normal
subgroup C has relative index at most two in M, commutator idempotence puts
the entire commutator in C.

This is the automorphism-action version of the small-quotient argument in
`Theory.GroupAction.SmallQuotientCentralization`.
-/

open Subgroup

private theorem small_action_fixed {A H : Type*} [Group A] [Group H] [Finite H]
    [MulDistribMulAction A H] (hcard : Nat.card H ≤ 2) (a : A) (x : H) : a • x = x := by
  by_cases hone : Nat.card H ≤ 1
  · let _ := Finite.card_le_one_iff_subsingleton.mp hone
    exact Subsingleton.elim _ _
  · have htwo : Nat.card H = 2 := by omega
    obtain ⟨z, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp htwo
    by_cases hx : x = 1
    · simp [hx]
    · have ha : a • x ≠ 1 := by
        intro he
        apply hx
        have hh := congrArg (fun y : H => a⁻¹ • y) he
        simpa using hh
      exact (huniq _ ha).trans (huniq _ hx).symm

/-- A coprime commutator contained in an invariant subgroup descends across
an invariant normal subquotient of order at most two. -/
public theorem commutatorAction_le_of_coprime_of_relIndex_le_two
    {P A : Type*} [Group P] [Group A] [Finite P] [Finite A]
    [MulDistribMulAction A P]
    (C M : Subgroup P) [C.Normal] [IsInvariant A P C] [IsInvariant A P M]
    (hsolv : Group.IsSolvable P) (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (hindex : C.relIndex M ≤ 2) (hcontain : commutatorAction A P ≤ M) :
    commutatorAction A P ≤ C := by
  let N := C.subgroupOf M
  let : IsInvariant A M N := isInvariant_subgroupOf C M
  let : MulDistribMulAction A (M ⧸ N) := quotientMulDistribMulAction N inferInstance
  have hcard : Nat.card (M ⧸ N) ≤ 2 := by
    simpa only [relIndex, index_eq_card] using hindex
  rw [← commutatorAction_map_eq_of_coprime_of_le M hsolv hcop hcontain]
  rw [map_le_iff_le_comap, commutatorAction_eq_closure, closure_le]
  rintro y ⟨a, m, rfl⟩
  have hf := small_action_fixed hcard a (QuotientGroup.mk' N m)
  have hf' : QuotientGroup.mk' N (a • m) = QuotientGroup.mk' N m := hf
  have hk : m⁻¹ * (a • m) ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (m⁻¹ * (a • m)) = 1
    rw [map_mul, map_inv, hf', inv_mul_cancel]
  exact hk

/-- Fixing a normal subgroup pointwise puts every action commutator in its
centralizer. -/
public theorem commutatorAction_le_centralizer_of_fixed_normal
    {P A : Type*} [Group P] [Group A] [MulDistribMulAction A P]
    (Z : Subgroup P) [Z.Normal]
    (hfix : ∀ a : A, ∀ z ∈ Z, a • z = z) :
    commutatorAction A P ≤ centralizer (Z : Set P) := by
  rw [commutatorAction_eq_closure, closure_le]
  rintro x ⟨a, g, rfl⟩ z hz
  have he := hfix a (g * z * g⁻¹) ((inferInstance : Z.Normal).conj_mem z hz g)
  simp only [smul_mul', smul_inv', hfix a z hz] at he
  symm
  calc
    (g⁻¹ * (a • g)) * z = g⁻¹ * ((a • g) * z * (a • g)⁻¹) * (a • g) := by group
    _ = g⁻¹ * (g * z * g⁻¹) * (a • g) := by rw [he]
    _ = z * (g⁻¹ * (a • g)) := by group
