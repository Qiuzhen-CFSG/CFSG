import Mathlib
import Submission.FeitThompson.FinalTheorem
import Submission.OddIndex

/-!
# From global isolation to Sylow-local hypothesis

This module converts the global isolation hypothesis on an involution `t`
into the local data required by the Z*-theorem:

- `t` is an involution (`t ≠ 1` and `t² = 1`)
- There exists a Sylow 2-subgroup `S` containing `t` such that `t` is central in `S`
- `t` is weakly closed in `S` (any conjugate of `t` lying in `S` equals `t`)

The key construction uses the odd-index theorem for `C_G(t)` to embed a Sylow
2-subgroup of the centralizer as a full Sylow 2-subgroup of `G`.
-/

namespace Submission.ZStar

open Subgroup

section basicDefinitions

variable {G : Type*} [Group G]

/-- An involution is a nonidentity element whose square is one. -/
def IsInvolution (x : G) : Prop :=
  x ≠ 1 ∧ x ^ 2 = 1

/-- An element `t` is weakly closed in a subgroup `S` if `t ∈ S` and any
conjugate of `t` lying in `S` already equals `t`. -/
def IsWeaklyClosedInSylow (t : G) (S : Subgroup G) : Prop :=
  t ∈ S ∧ ∀ g : G, g * t * g⁻¹ ∈ S → g * t * g⁻¹ = t

end basicDefinitions

section basicLemmas

variable {G : Type*} [Group G] {t : G}

/-- From `t * t = 1` and `t ≠ 1`, deduce `t⁻¹ = t`. -/
lemma inv_eq_self_of_sq_eq_one (ht2 : t * t = 1) : t⁻¹ = t := by
  apply inv_eq_of_mul_eq_one_left
  rw [ht2]

/-- From `t * t = 1` and `t ≠ 1`, deduce `orderOf t = 2`. -/
lemma orderOf_eq_two (ht2 : t * t = 1) (ht1 : t ≠ 1) : orderOf t = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime (p := 2)
  · rw [pow_two, ht2]
  · exact ht1

end basicLemmas

section indexCalculations

variable {G : Type*} [Group G] [Fintype G]

-- The odd-index theorem is provided by Submission.OddIndex.odd_index_of_centralizer

end indexCalculations

section constructSylow

variable {G : Type*} [Group G] [Fintype G] (t : G) (ht2 : t * t = 1) (ht1 : t ≠ 1)
  (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t)

include ht2 ht1 hisolated in
/-- Construct a Sylow 2-subgroup of G contained in the centralizer of t. -/
theorem exists_sylow_le_centralizer :
    ∃ S : Sylow 2 G,
      t ∈ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := Subgroup.centralizer ({t} : Set G)
  have ht_mem_C : t ∈ C := by
    simp [C, Subgroup.mem_centralizer_singleton_iff]
  have hC_index_odd : Odd C.index := by
    -- C.index = (Subgroup.centralizer {t}).index, and OddIndex gives oddness
    simpa [C] using Submission.OddIndex.odd_index_of_centralizer (t := t) ht2 ht1 hisolated

  -- t as an element of C
  let tC : C := ⟨t, ht_mem_C⟩

  -- zpowers tC is a 2-group
  have h_order : orderOf t = 2 := orderOf_eq_two ht2 ht1
  have h_tC_order : orderOf tC = 2 := by
    -- orderOf is invariant under subgroup embedding
    rw [← Subgroup.orderOf_coe tC, h_order]

  have h_zpow_2group : IsPGroup 2 (zpowers tC : Subgroup C) := by
    have h_card : Nat.card (zpowers tC : Subgroup C) = (2 : ℕ) ^ 1 := by
      rw [Nat.card_zpowers, h_tC_order]
      norm_num
    exact IsPGroup.of_card h_card

  -- Embed in a Sylow 2-subgroup of C
  obtain ⟨PC, hPC⟩ := h_zpow_2group.exists_le_sylow
  have htC_mem_PC : tC ∈ (PC : Subgroup C) :=
    hPC (Subgroup.mem_zpowers tC)

  -- Map to G via the subtype embedding
  let P : Subgroup G := (PC : Subgroup C).map C.subtype

  -- P is a 2-group
  have hP_pgroup : IsPGroup 2 P :=
    PC.isPGroup'.map C.subtype

  -- Compute index
  have hP_index : P.index = (PC : Subgroup C).index * C.index := by
    dsimp [P]
    rw [Subgroup.index_map_subtype (PC : Subgroup C)]

  -- Neither factor is divisible by 2
  have hPC_index_not_two : ¬ 2 ∣ (PC : Subgroup C).index :=
    PC.not_dvd_index
  have hC_index_not_two : ¬ 2 ∣ C.index := by
    rcases hC_index_odd with ⟨k, hk⟩
    rw [hk]
    omega

  have hP_index_not_two : ¬ 2 ∣ P.index := by
    rw [hP_index]
    intro h
    -- If 2 divides product, and 2 is prime, it divides one factor
    have hprime : Nat.Prime 2 := Nat.prime_two
    rcases hprime.dvd_mul.mp h with (h | h)
    · exact hPC_index_not_two h
    · exact hC_index_not_two h

  -- Convert to Sylow 2 of G
  let S : Sylow 2 G := IsPGroup.toSylow hP_pgroup hP_index_not_two

  have hS_t : t ∈ (S : Subgroup G) := by
    dsimp [S, P]
    apply Subgroup.mem_map.mpr
    exact ⟨tC, htC_mem_PC, rfl⟩

  have hS_le_C : (S : Subgroup G) ≤ C := by
    dsimp [S, P]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _, rfl⟩
    -- y is in C, so its image centralizes t
    exact y.2

  exact ⟨S, hS_t, hS_le_C⟩

end constructSylow

section centralAndWeak

variable {G : Type*} [Group G] [Fintype G] (t : G) (ht2 : t * t = 1) (ht1 : t ≠ 1)
  (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t)

include ht2 ht1 hisolated in
/-- The full local reduction: obtain a Sylow 2-subgroup in which t is central
and weakly closed. -/
theorem isolated_involution_local_data :
    ∃ S : Sylow 2 G,
      t ∈ (S : Subgroup G) ∧
      (∀ s, s ∈ (S : Subgroup G) → s * t = t * s) ∧
      IsWeaklyClosedInSylow t (S : Subgroup G) := by
  obtain ⟨S, hS_t, hS_le_C⟩ := exists_sylow_le_centralizer t ht2 ht1 hisolated

  -- Centrality: all elements of S commute with t (since S ≤ C_G(t))
  have h_central : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s := by
    intro s hs
    have hs_C : s ∈ Subgroup.centralizer ({t} : Set G) := hS_le_C hs
    -- mem_centralizer_singleton_iff gives the commutation directly
    rw [Subgroup.mem_centralizer_singleton_iff] at hs_C
    exact hs_C

  -- Weak closure: if a conjugate of t lies in S, it equals t
  have h_weak : IsWeaklyClosedInSylow t (S : Subgroup G) := by
    refine ⟨hS_t, ?_⟩
    intro g hgS
    -- hgS: g * t * g⁻¹ ∈ S
    -- Since elements of S commute with t, the conjugate commutes with t
    have h_central_g : (g * t * g⁻¹) * t = t * (g * t * g⁻¹) :=
      h_central (g * t * g⁻¹) hgS
    -- Use the isolation hypothesis
    exact hisolated g h_central_g

  exact ⟨S, hS_t, h_central, h_weak⟩

end centralAndWeak

end Submission.ZStar
