/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimumMonomialOrbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MinimumShapeInvariance
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimumMonomialOrbits.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

instance leechShellAction (r : ℤ) : MulAction LeechIsometryGroup (LeechShell r) :=
  MulAction.compHom _ (shellRepresentation r)

def minimumShape (t : Fin 3) : Finset IntegerCoordinates :=
  if t = 0 then twoFourFamily 0 2 else if t = 1 then twoFourFamily 8 0
  else oddNoFiveVectors 1

theorem minimumShape_card (t : Fin 3) :
    (minimumShape t).card = ![1104,97152,98304] t := by
  fin_cases t <;> simp [minimumShape,pureFour_shape_counts.1,twoFour_shape_counts.1,
    odd_minimal_shape_card]

theorem minimumShape_exhaustive (x : LeechShell 4) :
    ∃ t : Fin 3, x.val.val ∈ minimumShape t := by
  have h := (minimalVectors_iff x.val.val).mpr ⟨x.val.prop,x.prop⟩
  simp only [minimalVectors,evenMinimalVectors,Finset.mem_union] at h
  rcases h with (h | h) | h
  · exact ⟨0,by simpa [minimumShape] using h⟩
  · exact ⟨1,by simpa [minimumShape] using h⟩
  · exact ⟨2,by simpa [minimumShape] using h⟩

theorem minimumShape_invariant (m : GolayMonomialGroup) (x : leech) (t : Fin 3)
    (hx : x.val ∈ minimumShape t) : ((monomialEmbedding m).val x).val ∈ minimumShape t := by
  fin_cases t
  · exact monomial_twoFour_invariant m x 0 2 hx
  · exact monomial_twoFour_invariant m x 8 0 hx
  · exact monomial_odd_minimum_invariant m x hx

theorem minimumShape_transitive (x y : leech) (t : Fin 3)
    (hx : x.val ∈ minimumShape t) (hy : y.val ∈ minimumShape t) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  fin_cases t
  · exact monomial_four_minimum_transitive x y hx hy
  · exact monomial_octad_minimum_transitive x y hx hy
  · obtain ⟨a,c,rfl⟩ := odd_minimum_parameterization x hx
    obtain ⟨b,d,rfl⟩ := odd_minimum_parameterization y hy
    exact monomial_odd_minimum_transitive a b c d

theorem minimum_monomial_orbit (x : LeechShell 4) (t : Fin 3)
    (hx : x.val.val ∈ minimumShape t) :
    MulAction.orbit monomialSubgroup x = {y | y.val.val ∈ minimumShape t} := by
  ext y
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨m,hm⟩ := g.prop
    change (g.val.val x.val).val ∈ minimumShape t
    rw [← hm]
    exact minimumShape_invariant m x.val t hx
  · intro hy
    obtain ⟨m,hm⟩ := minimumShape_transitive x.val y.val t hx hy
    refine ⟨⟨monomialEmbedding m,⟨m,rfl⟩⟩,?_⟩
    exact Subtype.ext hm

theorem minimumShape_sound (t : Fin 3) (z : IntegerCoordinates)
    (hz : z ∈ minimumShape t) : z ∈ leech ∧ integerDot z z = 32 := by
  apply (minimalVectors_iff z).mp
  fin_cases t
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
  · exact Finset.mem_union_right _ hz

def minimumOrbitShapeEquiv (x : LeechShell 4) (t : Fin 3)
    (hx : x.val.val ∈ minimumShape t) :
    MulAction.orbit monomialSubgroup x ≃ {z // z ∈ minimumShape t} where
  toFun y := ⟨y.val.val.val, by
    exact (Set.ext_iff.mp (minimum_monomial_orbit x t hx) y.val).mp y.prop⟩
  invFun z := ⟨⟨⟨z.val,(minimumShape_sound t z.val z.prop).1⟩,
    (minimumShape_sound t z.val z.prop).2⟩,by
      rw [minimum_monomial_orbit x t hx]
      exact z.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem minimum_monomial_orbit_card (x : LeechShell 4) (t : Fin 3)
    (hx : x.val.val ∈ minimumShape t) :
    Nat.card (MulAction.orbit monomialSubgroup x) = ![1104,97152,98304] t := by
  rw [Nat.card_congr (minimumOrbitShapeEquiv x t hx),Nat.card_eq_fintype_card,
    Fintype.card_coe,minimumShape_card]

end Atlas.Conway

