/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianScalarProjective.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneReductionSurjective
public import Theory.AtlasPort.Janko2.Algebra.GoldenFourAlternating

/-!
# IcosianScalarProjective

The actual norm-one scalar group modulo its two signs is SL₂(F₄),
and hence A₅ through the five-point projective action. The surjective
reduction homomorphism and its proved kernel construct the equivalences.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianScalarProjective.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

noncomputable section
namespace Atlas.Algebra

theorem icosianNormOneReduction_kernel_iff (u : icosianNormOneGroup) :
    u∈icosianNormOneReduction.ker ↔ u=1 ∨ u=icosianNormOneMinusOne := by
  constructor
  · intro h
    rcases icosianNormOneReduction_kernel_values u h with h | h
    · exact Or.inl (icosianNormOne_value_injective h)
    · exact Or.inr (icosianNormOne_value_injective h)
  · rintro (rfl|rfl)
    · exact map_one _
    · exact icosianNormOneReduction_minus_one

/-- The actual norm-one scalar group modulo its two signs. -/
abbrev IcosianScalarProjectiveModel := icosianNormOneGroup ⧸ icosianNormOneReduction.ker

/-- Reduction identifies the actual scalar sign quotient with SL2(F4). -/
def icosianScalarProjectiveSL :
    IcosianScalarProjectiveModel ≃* Matrix.SpecialLinearGroup (Fin 2) GoldenFour :=
  QuotientGroup.quotientKerEquivOfSurjective _ icosianNormOneReduction_surjective

theorem icosianScalarProjective_card : Nat.card IcosianScalarProjectiveModel=60 := by
  rw [Nat.card_congr icosianScalarProjectiveSL.toEquiv,goldenFour_SL_card]

/-- The scalar sign quotient acts as the actual alternating group on the
five-point projective line over the golden field modulo two. -/
def icosianScalarProjectiveAlternatingFive :
    IcosianScalarProjectiveModel ≃* alternatingGroup (Fin 5) :=
  icosianScalarProjectiveSL.trans goldenFourSLAlternatingFive

end Atlas.Algebra
