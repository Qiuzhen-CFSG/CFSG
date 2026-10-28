module
public import Theory.GroupAction.ComponentSmallTwoSection
public import Theory.GroupTheory.NormalizedSupConsequences
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.GroupTheory.IndexNormal

/-!
# Lifting component generation across a small kernel index

A two-perfect group with a simple quotient divisible by a prime r acts
trivially on fewer than r cosets. The permutation image avoids r and is
therefore a two-group, which two-perfectness kills. Thus generation modulo
a normalized kernel lifts whenever the remaining kernel index is below r;
the generating subgroup need not contain that kernel.

The original field-four mover consumer is
GenerationTwoSymplecticCrossKernelLift, for the generator step of MS93 (5.5)
and (5.7), printed pp.915--919. Its literal kernel index is at most sixteen
and the simple quotient order is divisible by seventeen.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S]

/-- A small coset action of a two-perfect simple cover is trivial. -/
theorem component_le_of_relIndex_lt_prime
    (L A : Subgroup G) [Finite L]
    (hL : IsPPerfect 2 L) (q : L →* S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) {r : ℕ} (hr : r.Prime) (hS : r ∣ Nat.card S)
    (hi : A.relIndex L < r) : L ≤ A := by
  let N := A.subgroupOf L
  let f := MulAction.toPermHom L (L ⧸ N)
  have hperm : ¬ r ∣ Nat.card (Equiv.Perm (L ⧸ N)) := by
    rw [Nat.card_perm]
    exact fun h => (not_le_of_gt hi) (hr.dvd_factorial.mp h)
  have him := MonoidHom.isPGroup_range_of_simple_quotient q hq hk f r hS hperm
  have hker := pResidual_le_ker_of_isPGroup 2 f.rangeRestrict him
  rw [MonoidHom.ker_rangeRestrict,(pResidual_eq_top_iff 2 L).mpr hL] at hker
  intro x hx
  exact N.normalCore_le (show (⟨x,hx⟩ : L) ∈ N.normalCore from
    (N.normalCore_eq_ker.symm ▸ hker (mem_top _)))

/-- Remove a normalized kernel supplement by its remaining relative index. -/
theorem component_le_of_kernel_supplement_small_index
    (L A Q : Subgroup G) [Finite L] [Finite (A ⊔ Q : Subgroup G)]
    (hAQ : A ≤ normalizer (Q : Set G))
    (hL : IsPPerfect 2 L) (q : L →* S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) {r : ℕ} (hr : r.Prime) (hS : r ∣ Nat.card S)
    (hcover : L ≤ A ⊔ Q) (hi : A.relIndex Q < r) : L ≤ A := by
  let : Finite A := Finite.of_injective
    (inclusion (show A ≤ A ⊔ Q from le_sup_left)) (inclusion_injective _)
  apply component_le_of_relIndex_lt_prime L A hL q hq hk hr hS
  have hle := relIndex_le_of_le_right (H := A) hcover index_ne_zero_of_finite
  rw [sup_comm,relIndex_sup_of_normalizes Q A hAQ] at hle
  exact hle.trans_lt hi

/-- Image containment lifts across a small kernel index without kernel containment. -/
theorem component_le_of_image_le_small_kernel_index
    [Finite G] {J : Type*} [Group J]
    (L A : Subgroup G) (f : G →* J)
    (hL : IsPPerfect 2 L) (q : L →* S) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) {r : ℕ} (hr : r.Prime) (hS : r ∣ Nat.card S)
    (himage : L.map f ≤ A.map f) (hi : A.relIndex f.ker < r) : L ≤ A :=
  component_le_of_kernel_supplement_small_index L A f.ker
    le_normalizer_of_normal hL q hq hk hr hS
    (map_le_map_iff.mp himage) hi
end Subgroup
