module
public import Theory.MeasureTheory.CompatibleLocalGluing
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Gluing local measures on open covers

On a Lindelöf space with measurable open sets, compatible measures on any open
cover determine a unique global measure with the prescribed local restrictions.
This removes the explicit countability requirement from measurable-cover gluing
and supplies the form needed for chartwise constructions of manifold volume.

The standard argument chooses a countable subcover using Lindelöfness and applies
`existsUnique_measure_restrict_eq_of_countable_cover`. Compatibility then extends
the resulting restriction identity to every member of the original cover, by
comparing restrictions to the countable subcover. The same extensionality argument
proves uniqueness. No finiteness assumption on the local measures is needed.
-/

open Set
namespace MeasureTheory
/-- Compatible local measures on an open cover of a Lindelöf space glue uniquely.
The cover index and the space may both be empty. -/
public theorem existsUnique_measure_restrict_eq_of_open_cover
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [LindelofSpace X]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = univ) (μ : ι → Measure X)
    (hcompat : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j)) :
    ∃! ν : Measure X, ∀ i, ν.restrict (U i) = (μ i).restrict (U i) := by
  obtain ⟨S, hS, hScov⟩ := isLindelof_univ.elim_countable_subcover U hU hcover.ge
  have : Countable S := hS.to_subtype
  have hcov : ⋃ i : S, U i = univ := by
    rw [iUnion_subtype]
    exact Subset.antisymm (subset_univ _) hScov
  obtain ⟨ν, hν, -⟩ := existsUnique_measure_restrict_eq_of_countable_cover
    (fun i : S ↦ U i) (fun i ↦ (hU i).measurableSet) hcov
    (fun i : S ↦ μ i) (fun i j ↦ hcompat i j)
  have hall : ∀ j, ν.restrict (U j) = (μ j).restrict (U j) := by
    intro j
    apply Measure.ext_of_iUnion_eq_univ hcov
    intro i
    rw [Measure.restrict_comm (hU i).measurableSet, hν i]
    rw [Measure.restrict_restrict (hU j).measurableSet,
      Measure.restrict_restrict (hU i).measurableSet,
      inter_comm (U i) (U j)]
    exact hcompat j i |>.symm
  refine ⟨ν, hall, fun ξ hξ ↦ ?_⟩
  exact Measure.ext_of_iUnion_eq_univ hcov (fun i ↦ (hξ i).trans (hν i).symm)
end MeasureTheory
