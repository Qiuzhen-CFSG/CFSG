module
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Gluing compatible measures on a countable cover

A countable measurable cover and measures agreeing on pairwise overlaps determine
one global measure. Neither local finiteness nor sigma finiteness is needed;
an empty index type is allowed when the cover forces the underlying space empty.

The construction enumerates a nonempty countable cover, disjointifies it, and
sums the local measures restricted to those pieces. Compatibility identifies
its restriction to each original cover member with the prescribed local measure.
Mathlib's countable-cover extensionality gives uniqueness. This is the standard
measure-gluing argument, provided here for constructions of geometric volume
from chartwise densities.
-/

open Set
namespace MeasureTheory

private theorem exists_measure_nat (X : Type*) [MeasurableSpace X]
    (U : ℕ → Set X) (hU : ∀ i, MeasurableSet (U i))
    (hcover : ⋃ i, U i = univ) (μ : ℕ → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j)) :
    ∃ ν : Measure X, ∀ i, ν.restrict (U i) = (μ i).restrict (U i) := by
  let D := disjointed U
  have hD : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hU
  have hDcover : ⋃ i, D i = univ := iUnion_disjointed.trans hcover
  refine ⟨Measure.sum (fun i ↦ (μ i).restrict (D i)), fun j ↦ ?_⟩
  rw [Measure.restrict_sum _ (hU j)]
  have heq : ∀ i, ((μ i).restrict (D i)).restrict (U j) =
      ((μ j).restrict (U j)).restrict (D i) := by
    intro i
    rw [Measure.restrict_restrict (hU j), Measure.restrict_restrict (hD i)]
    rw [inter_comm (D i) (U j)]
    apply Measure.restrict_congr_mono _ (hcompat i j)
    exact fun x hx ↦ ⟨disjointed_subset U i hx.2, hx.1⟩
  simp_rw [heq]
  rw [← Measure.restrict_iUnion (disjoint_disjointed U) hD, hDcover,
    Measure.restrict_univ]

/-- Compatible measures on a countable measurable cover glue uniquely.
The prescribed local measure is restricted to its cover member, so its values
outside that member do not affect the result. -/
public theorem existsUnique_measure_restrict_eq_of_countable_cover
    {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (U : ι → Set X) (hU : ∀ i, MeasurableSet (U i))
    (hcover : ⋃ i, U i = univ) (μ : ι → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j)) :
    ∃! ν : Measure X, ∀ i, ν.restrict (U i) = (μ i).restrict (U i) := by
  classical
  have hex : ∃ ν : Measure X, ∀ i, ν.restrict (U i) = (μ i).restrict (U i) := by
    cases isEmpty_or_nonempty ι with
    | inl h => exact ⟨0, fun i ↦ isEmptyElim i⟩
    | inr h =>
      obtain ⟨e, he⟩ := exists_surjective_nat ι
      have hcov : ⋃ n, U (e n) = univ := by
        rw [he.iUnion_comp, hcover]
      obtain ⟨ν, hν⟩ := exists_measure_nat X (U ∘ e) (fun n ↦ hU (e n)) hcov
        (μ ∘ e) (fun i j ↦ hcompat (e i) (e j))
      exact ⟨ν, fun i ↦ by obtain ⟨n, rfl⟩ := he i; exact hν n⟩
  obtain ⟨ν, hν⟩ := hex
  refine ⟨ν, hν, fun ξ hξ ↦ ?_⟩
  exact Measure.ext_of_iUnion_eq_univ hcover (fun i ↦ (hξ i).trans (hν i).symm)
end MeasureTheory
