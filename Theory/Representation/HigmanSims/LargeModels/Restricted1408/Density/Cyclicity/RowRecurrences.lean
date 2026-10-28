module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowRecurrences.Arithmetic
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RecurrenceInput
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.DataFacts

/-!
# Literal right-action recurrences for the degree-1408 row orbit

Every nonseed row is the right product of its designated parent and the
specified literal matrix (`false` for A, `true` for B). Bounded kernel-checked
packed products are matched to the unchanged published tables by two linear
scans, then transported by the proved decoder lemmas.

This discharges the recurrence premise of `rowCyclic_of_orbit_certificates`.
Spanning remains an independent obligation. No kernel, spanning, irreducibility
or density hypothesis enters the recurrence proof.
Source and action conventions: `source/README.md` and `RowRecurrences/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
open RowRecurrences

private lemma list_getElem!_tail {α : Type*} [Inhabited α] (xs : List α) (i : Nat) :
    xs.tail[i]! = xs[i + 1]! := by
  cases xs <;> simp

/-- Every proposed nonseed row obeys its designated literal right action. -/
theorem rowOrbitRecurrences : RowOrbitRecurrences := by
  intro i hi
  have hidx : i.val - 1 + 1 = i.val := by omega
  have hlen : i.val - 1 < rowOrbitRows.toList.tail.length := by
    rw [List.length_tail, Array.length_toList, rowOrbitRows_size]
    omega
  obtain ⟨s, hs, hp, hout, hchoice⟩ := correspondence_sound steps
    rowOrbitRows.toList.tail rowOrbitParents.toList.tail rowOrbitChoices.toList.tail
    steps_correspondence (i.val - 1) hlen
  simp only [list_getElem!_tail, Array.getElem!_toList, hidx] at hp hout hchoice
  have hparents := parentScan_sound (fun j => rowOrbitRows[j]!) 0 rowOrbitRows.toList
    (inputs steps rowOrbitParents.toList.tail) steps_parents
    (by intro j _hj; simp only [Nat.zero_add, Array.getElem!_toList])
  have hin : s.input = rowOrbitRows[rowOrbitParents[i.val]!]! := (hparents _ hp).symm
  have hprod := products_sound aRows.toList bRows.toList steps steps_products s hs
  rw [hin, hout, hchoice] at hprod
  cases hc : rowOrbitChoices[i.val]! with
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hprod ⊢
    exact (vecMul_matrixA_of_listProduct _ _ hprod).symm
  | true =>
    simp only [hc, ↓reduceIte] at hprod ⊢
    exact (vecMul_matrixB_of_listProduct _ _ hprod).symm

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
