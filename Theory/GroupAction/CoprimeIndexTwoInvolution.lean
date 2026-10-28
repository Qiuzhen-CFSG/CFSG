module
public import Theory.GroupAction.CoprimeFixedCardinality
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic

/-!
# Fixed involutions outside an index-two kernel

For a coprime action on a finite solvable group P, let N be an invariant
normal subgroup of index two with no nonidentity common fixed point.
The action on P/N is trivial, so coprime fixed-point lifting makes C_P(A)
have order two. Its involution lies outside N.

The subgroup application retains a two-subgroup Q, a cubic actor X, and
the original cut Q intersect (R join U) contained in R. This gives the
outside involution used by Aschbacher--Smith 14.3.21(1), printed p.998.
-/

open Subgroup

namespace FixedPoints

/-- Coprime lifting gives a fixed involution outside the index-two kernel. -/
public theorem exists_involution_not_mem_of_index_two
    {A P : Type*} [Group A] [Finite A] [Group P] [Finite P]
    [MulDistribMulAction A P]
    (hsolv : Group.IsSolvable P) (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (N : Subgroup P) [N.Normal] (hN : IsInvariant A P N)
    (hi : N.index = 2) (hfixed : N ⊓ subgroup A P = ⊥) :
    ∃ t : P, orderOf t = 2 ∧ t ∉ N ∧ ∀ a : A, a • t = t := by
  let : MulDistribMulAction A (P ⧸ N) := quotientMulDistribMulAction N hN
  have hc : Nat.card (P ⧸ N) = 2 := hi
  have hall : subgroup A (P ⧸ N) = ⊤ := by
    apply top_unique
    intro x _ a
    by_cases hx : x = 1
    · simp [hx]
    · obtain ⟨_, _, he⟩ := (Nat.card_eq_two_iff' (1 : P ⧸ N)).mp hc
      have ha : a • x ≠ 1 := by
        intro hh
        apply hx
        simpa using congrArg (fun y : P ⧸ N => a⁻¹ • y) hh
      exact (he _ ha).trans (he _ hx).symm
  have hcard : Nat.card (subgroup A P) = 2 := by
    rw [card_eq_quotient_mul_kernel_of_coprime hsolv hcop N hN, hall, hfixed]
    simpa using hc
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := subgroup A P) 2
    (hcard ▸ dvd_rfl)
  refine ⟨t, ?_, ?_, t.property⟩
  · simpa only [Subgroup.orderOf_coe] using ht
  · intro hn
    have hmem : (t : P) ∈ N ⊓ subgroup A P := ⟨hn, t.property⟩
    have he : t = 1 := Subtype.ext (by simpa only [hfixed, mem_bot, Subgroup.coe_one] using hmem)
    simp [he] at ht
end FixedPoints

namespace Subgroup
/-- Literal subgroup form of the cubic fixed-point argument in 14.3.21(1). -/
public theorem exists_involution_outside_join_of_coprime_fixed_kernel
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (R U Q X : Subgroup G)
    (hQ : IsPGroup 2 Q) (hX : IsPGroup 3 X)
    (hQT : Q ≤ (T : Subgroup G))
    (hcut : Q ⊓ (R ⊔ U) ≤ R)
    (hXQ : X ≤ normalizer (Q : Set G))
    (hXR : X ≤ normalizer (R : Set G))
    [(R.subgroupOf Q).Normal]
    (hi : (R.subgroupOf Q).index = 2)
    (hfixed : R ⊓ centralizer (X : Set G) = ⊥) :
    ∃ t ∈ (T : Subgroup G), orderOf t = 2 ∧ t ∉ R ⊔ U ∧
      t ∈ centralizer (X : Set G) := by
  let : MulDistribMulAction X Q := conjMulDistribMulActionOfLeNormalizer X Q hXQ
  have hN : IsInvariant X Q (R.subgroupOf Q) := ⟨by
    intro x q
    change (q : G) ∈ R ↔ (x : G) * (q : G) * (x : G)⁻¹ ∈ R
    exact mem_normalizer_iff.mp (hXR x.property) q⟩
  have hf : R.subgroupOf Q ⊓ FixedPoints.subgroup X Q = ⊥ := by
    apply bot_unique
    intro q hq
    have hh : (q : G) ∈ R ⊓ centralizer (X : Set G) := by
      refine ⟨hq.1, ?_⟩
      intro x hx
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hq.2 ⟨x, hx⟩))
    exact Subtype.ext (by simpa only [hfixed, mem_bot, Subgroup.coe_one] using hh)
  let : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨t, ht, htR, htX⟩ :=
    FixedPoints.exists_involution_not_mem_of_index_two inferInstance
      (IsPGroup.coprime_card_of_ne 3 2 (by decide) X Q hX hQ)
      (R.subgroupOf Q) hN hi hf
  refine ⟨t, hQT t.property, ?_, ?_, ?_⟩
  · simpa only [Subgroup.orderOf_coe] using ht
  · intro htRU
    exact htR (hcut ⟨t.property, htRU⟩)
  · intro x hx
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (htX ⟨x, hx⟩))
end Subgroup
