/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimumShapeSeparation.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MinimumMonomialOrbits
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimumShapeSeparation.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem even_odd_minimum_disjoint (k u : ℕ) :
    Disjoint (twoFourFamily k u) (oddNoFiveVectors 1) :=
  opposite_parity_disjoint _ _
    (fun x hx => (twoFourFamily_properties k u x hx).2.1)
    (fun x hx => ((odd_minimal_shell_iff x).mpr hx).2.1)

theorem minimumShape_disjoint (s t : Fin 3) (hst : s ≠ t) :
    Disjoint (minimumShape s) (minimumShape t) := by
  fin_cases s <;> fin_cases t
  all_goals first | exact (hst rfl).elim | skip
  · exact twoFourFamily_disjoint 0 2 8 0 (Or.inl (by decide))
  · exact even_odd_minimum_disjoint 0 2
  · exact (twoFourFamily_disjoint 0 2 8 0 (Or.inl (by decide))).symm
  · exact even_odd_minimum_disjoint 8 0
  · exact (even_odd_minimum_disjoint 0 2).symm
  · exact (even_odd_minimum_disjoint 8 0).symm

theorem minimumShape_unique (x : LeechShell 4) :
    ∃! t : Fin 3, x.val.val ∈ minimumShape t := by
  obtain ⟨t,ht⟩ := minimumShape_exhaustive x
  refine ⟨t,ht,?_⟩
  intro s hs
  by_contra hst
  exact Finset.disjoint_left.mp (minimumShape_disjoint s t hst) hs ht

theorem minimum_monomial_three_orbits (x y : LeechShell 4) :
    y ∈ MulAction.orbit monomialSubgroup x ↔
      ∃ t : Fin 3, x.val.val ∈ minimumShape t ∧ y.val.val ∈ minimumShape t := by
  obtain ⟨t,ht⟩ := minimumShape_exhaustive x
  rw [minimum_monomial_orbit x t ht]
  constructor
  · intro hy
    exact ⟨t,ht,hy⟩
  · rintro ⟨s,hs,hy⟩
    have he := (minimumShape_unique x).unique hs ht
    simpa [he] using hy

end Atlas.Conway
