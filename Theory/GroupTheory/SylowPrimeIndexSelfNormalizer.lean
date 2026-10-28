module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow subgroups of prime index normalize only themselves

A Sylow subgroup of prime index which is not contained in the prime core
is self-normalizing. The number of Sylow subgroups divides the prime index;
if it were one the subgroup would be normal and contained in the core.
Otherwise its normalizer has the same index, hence is the subgroup itself.

This gives the relative self-normalizers of the two parabolics in
Aschbacher–Smith J.4.5, printed p.442.
-/

public section
open Subgroup

/-- A Sylow subgroup of prime index, outside the core, is self-normalizing. -/
theorem Sylow.normalizer_eq_of_prime_index_not_le_core
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hindex : S.index.Prime) (hnot : ¬ (S : Subgroup G) ≤ pCore p G) :
    normalizer (S : Set G) = (S : Subgroup G) := by
  have hc : Nat.card (Sylow p G) = S.index := by
    rcases (Nat.dvd_prime hindex).mp S.card_dvd_index with h | h
    · let : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp h).1
      exact (hnot (le_sSup ⟨S.normal_of_subsingleton,S.isPGroup'⟩)).elim
    · exact h
  have hi : (normalizer (S : Set G)).index = S.index := S.card_eq_index_normalizer.symm.trans hc
  have he : Nat.card (normalizer (S : Set G)) = Nat.card S := by
    apply Nat.eq_of_mul_eq_mul_left hindex.pos
    rw [← hi, (normalizer (S : Set G)).index_mul_card,hi,S.index_mul_card]
  exact (eq_of_le_of_card_ge le_normalizer he.le).symm
