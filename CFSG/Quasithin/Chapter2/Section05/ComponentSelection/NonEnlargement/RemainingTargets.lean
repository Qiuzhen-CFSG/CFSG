module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.RemainingTargets.Small
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.RemainingTargets.Bender
/-!
# Actual remaining target exclusions for 2.5.6

The source component's central quotient is the given binary PSL₃ or PSp₄
model over a field larger than two. The preceding modules exclude every
remaining target: the three Bender families, the small concrete carriers,
prime PSL₂, and central two-covers of PSL₃(2). This final application uses
the actual subgroup inclusion, retaining both original centers.
The containing-component selection and even larger-field target rigidity
are supplied by the independent source dispatcher.

Source: Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
/-- The literal component inclusion contradicts any of the remaining source
target rows; no additional rank, order or Sylow-intersection input remains. -/
theorem not_le_remaining_targets {G : Type*} [Group G] [Finite G]
    (K C : Subgroup G) (hZ : IsPGroup 2 (center K)) (hZC : IsPGroup 2 (center C))
    {n : ℕ} (hn : 1<n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n))
    (ht : ClassificationModels.IsBenderModel C ∨
      (Nonempty (C ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (C ≃* Sporadic.Mathieu.M11) ∨
        Nonempty (C ≃* alternatingGroup (Fin 6))) ∨
      (∃ q, q.Prime ∧ 3<q ∧ ClassicalGroup.IsPSL C 2 q) ∨
      ClassicalGroup.IsPSL (C ⧸ center C) 3 2) : ¬K≤C := by
  intro hKC
  rcases ht with ht | ht | ⟨q,hq,hql,ht⟩ | ht
  · exact not_injective_bender hZ hm ht (inclusion hKC) (inclusion_injective hKC)
  · exact not_injective_small_targets hn hm ht (inclusion hKC) (inclusion_injective hKC)
  · exact not_injective_prime_linear hZ hn hm hq hql ht (inclusion hKC) (inclusion_injective hKC)
  · exact not_injective_binary_linear_cover hZ hZC hn hm ht (inclusion hKC) (inclusion_injective hKC)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
