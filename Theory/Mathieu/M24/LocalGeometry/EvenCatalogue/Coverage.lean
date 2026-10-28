module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.Coverage.ElementChecks
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.Coverage.PairChecks
public import Mathlib.Data.Finset.Max

/-!
# Exhaustive intrinsic normal elementary catalogue in an M₂₄ Sylow subgroup

The certificate first associates a listed subgroup to every nonidentity element
of a normal exponent-two subgroup R. Its generators are products of conjugates
of the element, so the listed subgroup lies in R, and a reverse word places the
element in that subgroup. Every other element of the order-1024 carrier is
excluded by a conjugate product whose square is nonidentity.

Choose the greatest-index listed subgroup contained in R. The pair certificate
forces every associated subgroup into it: otherwise the pair generates a
higher-index row or a product with nonidentity square. Thus R is exactly that
row. The computation enumerates elements and pairs of 22 rows, never arbitrary
subsets of the carrier. All certificates are checked by the kernel.

This is the Sylow catalogue input for condition E, not the ambient normalizer
calculation. Source context: Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4;
GLS3, Table 5.3e. Reproduction details are in `Coverage/source/README.md`.
-/

namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.Coverage
open SylowNormalizer OrderEnumeration

private theorem square_index_eq_zero (R : Subgroup candidate)
    (hsq : ∀ x ∈ R, x * x = 1) {i : Fin 1024} (hi : element i ∈ R) :
    multiply i i = 0 := by
  apply element_injective
  rw [element_multiply, element_zero]
  exact hsq _ hi

private theorem row_of_nonidentity (R : Subgroup candidate) (hn : R.Normal)
    (hsq : ∀ x ∈ R, x * x = 1) {x : candidate} (hx : x ∈ R) (hne : x ≠ 1) :
    ∃ i : Fin 22, subgroup i ≤ R ∧ x ∈ subgroup i := by
  obtain ⟨j, rfl⟩ := element_surjective x
  rcases rejection_check j with hj | hj | hj
  · exact (hne (by rw [hj, element_zero])).elim
  · refine ⟨closureRow (goodCode j), subgroup_le _ R ?_, ?_⟩
    · intro a
      rw [← lower_check (goodCode j) a, ← hj]
      exact normalProduct_mem R hn hx _
    · have hm := product_mem (subgroup (closureRow (goodCode j)))
        (generatorIndex (closureRow (goodCode j))) (generator_mem _) (upperWord (goodCode j))
      rw [upper_check, ← hj] at hm
      exact hm
  · exact (hj (square_index_eq_zero R hsq (normalProduct_mem R hn hx _))).elim

private theorem joinedGenerator_mem (i j : Fin 22) (R : Subgroup candidate)
    (hi : subgroup i ≤ R) (hj : subgroup j ≤ R) (a : Fin 12) :
    element (joinedGenerator i j a) ∈ R := by
  unfold joinedGenerator
  split
  · exact hi (generator_mem _ _)
  · exact hj (generator_mem _ _)

private theorem pair_containment_or_enlargement (R : Subgroup candidate)
    (hsq : ∀ x ∈ R, x * x = 1) (i j : Fin 22) (hji : j ≤ i)
    (hi : subgroup i ≤ R) (hj : subgroup j ≤ R) :
    subgroup j ≤ subgroup i ∨ ∃ k : Fin 22, i < k ∧ subgroup k ≤ R := by
  rcases pair_check i j hji with h | h | h
  · left
    apply subgroup_le
    intro a
    rw [← h.2 a]
    exact product_mem _ _ (joinedGenerator_mem i i _ le_rfl le_rfl) _
  · right
    refine ⟨pairTarget i j, h.1, subgroup_le _ R ?_⟩
    intro a
    rw [← h.2 a]
    exact product_mem _ _ (joinedGenerator_mem i j R hi hj) _
  · exfalso
    apply h
    apply square_index_eq_zero R hsq
    rw [badPairProduct, element_multiply]
    exact R.mul_mem (hi (generator_mem _ _)) (hj (generator_mem _ _))

/-- Exhaustiveness uses only intrinsic normality and exponent two. -/
public theorem catalogue_of_normal_exponent_two (R : Subgroup candidate) (hR : R ≠ ⊥)
    (hn : R.Normal) (hsq : ∀ x ∈ R, x * x = 1) :
    ∃ i : Fin 22, R = subgroup i := by
  classical
  let s : Finset (Fin 22) := Finset.univ.filter (fun i => subgroup i ≤ R)
  have mem_s (i : Fin 22) : i ∈ s ↔ subgroup i ≤ R := by simp [s]
  have hs : s.Nonempty := by
    obtain ⟨x, hx, hx1⟩ := R.bot_or_exists_ne_one.resolve_left hR
    obtain ⟨i, hi, _⟩ := row_of_nonidentity R hn hsq hx hx1
    exact ⟨i, (mem_s i).mpr hi⟩
  let i := s.max' hs
  have hi : subgroup i ≤ R := (mem_s i).mp (Finset.max'_mem s hs)
  have hmax (j : Fin 22) (hj : subgroup j ≤ R) : j ≤ i :=
    Finset.le_max' s j ((mem_s j).mpr hj)
  refine ⟨i, le_antisymm ?_ hi⟩
  intro x hx
  by_cases hx1 : x = 1
  · simpa only [hx1] using (subgroup i).one_mem
  obtain ⟨j, hj, hxj⟩ := row_of_nonidentity R hn hsq hx hx1
  rcases pair_containment_or_enlargement R hsq i j (hmax j hj) hi hj with h | ⟨k, hk, hkR⟩
  · exact h hxj
  · exact (not_lt_of_ge (hmax k hkR) hk).elim

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.Coverage
