/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/NormSixShapes.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.NormSixDodecadOrbit
public import Theory.AtlasPort.OtherSporadic.Conway.NormSixOctadOrbit
public import Theory.AtlasPort.OtherSporadic.Conway.NormSixFusionWitness
/-!
The concrete norm-six Leech shell and its stabilizers.
Coordinate orbit transport and orbit-stabilizer counting identify the full stabilizer.

Source: Gerald Höhn, `Atlas/Conway/NormSixShapes.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def normSixShape : Fin 4 → Finset IntegerCoordinates :=
  ![twoFourFamily 12 0, twoFourFamily 8 1, oddNoFiveVectors 3, oddOneFiveVectors 0]

def normSixShapeSize : Fin 4 → ℕ := ![5275648, 3108864, 8290304, 98304]

theorem normSixShape_card (t : Fin 4) : (normSixShape t).card = normSixShapeSize t := by
  fin_cases t
  · exact twoFour_shape_counts.2.1
  · exact twoFour_shape_counts.2.2.1
  · exact odd_six_shape_cards.1
  · exact odd_six_shape_cards.2

theorem normSixShape_mem (x : IntegerCoordinates) :
    (∃ t, x ∈ normSixShape t) ↔ x ∈ sixVectors := by
  simp only [sixVectors, evenSixVectors, oddSixVectors, Finset.mem_union]
  constructor
  · rintro ⟨t,ht⟩
    fin_cases t
    · exact Or.inl (Or.inl ht)
    · exact Or.inl (Or.inr ht)
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr ht)
  · rintro ((h | h) | (h | h))
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩

theorem normSixShape_sound (t : Fin 4) (x : IntegerCoordinates) (hx : x ∈ normSixShape t) :
    x ∈ leech ∧ integerDot x x = 48 :=
  (sixVectors_iff x).mp ((normSixShape_mem x).mp ⟨t,hx⟩)

theorem normSix_even_odd_disjoint (k u : ℕ) (t : Fin 2) :
    Disjoint (twoFourFamily k u) (![oddNoFiveVectors 3,oddOneFiveVectors 0] t) := by
  apply opposite_parity_disjoint _ _
    (fun x hx => (twoFourFamily_properties k u x hx).2.1)
  intro x hx
  fin_cases t
  · exact (oddNoFiveVectors_properties 3 (by decide) x hx).2.1
  · exact (oddOneFiveVectors_properties 0 (by decide) x hx).2.1

theorem normSixShape_disjoint (s t : Fin 4) (hst : s ≠ t) :
    Disjoint (normSixShape s) (normSixShape t) := by
  fin_cases s <;> fin_cases t
  all_goals first | exact (hst rfl).elim | skip
  · exact twoFourFamily_disjoint 12 0 8 1 (Or.inl (by decide))
  · exact normSix_even_odd_disjoint 12 0 0
  · exact normSix_even_odd_disjoint 12 0 1
  · exact (twoFourFamily_disjoint 12 0 8 1 (Or.inl (by decide))).symm
  · exact normSix_even_odd_disjoint 8 1 0
  · exact normSix_even_odd_disjoint 8 1 1
  · exact (normSix_even_odd_disjoint 12 0 0).symm
  · exact (normSix_even_odd_disjoint 8 1 0).symm
  · exact odd_shapes_disjoint 3 0
  · exact (normSix_even_odd_disjoint 12 0 1).symm
  · exact (normSix_even_odd_disjoint 8 1 1).symm
  · exact (odd_shapes_disjoint 3 0).symm

theorem normSixShape_transitive (x y : leech) (t : Fin 4)
    (hx : x.val ∈ normSixShape t) (hy : y.val ∈ normSixShape t) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  fin_cases t
  · exact monomial_dodecad_six_transitive x y hx hy
  · exact monomial_octad_oneFour_six_transitive x y hx hy
  · exact monomial_odd_three_transitive x y hx hy
  · exact monomial_odd_five_transitive x y hx hy

end Atlas.Conway
