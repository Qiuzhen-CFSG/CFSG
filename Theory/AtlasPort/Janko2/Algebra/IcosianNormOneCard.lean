/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormOneCard.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneGroup
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneExhaustion
public import Theory.AtlasPort.Janko2.Algebra.IcosianParityIntegral
public import Theory.AtlasPort.Janko2.Algebra.IcosianShortParity

/-!
# IcosianNormOneCard

The norm-one integral quaternion group has order 120. The coordinate
list is placed in bijection with the actual group using integrality,
norm verification, injectivity, and exhaustion.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormOneCard.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

noncomputable section
namespace Atlas.Algebra

/-- The scalar classification is a bijection with all actual norm-one integral quaternions. -/
def icosianNormOneCoordinatesEquiv :
    {v // v ∈ icosianNormOneCoordinates} ≃ icosianNormOneGroup :=
  Equiv.ofBijective (fun v => icosianNormOneGroupOf
    (icosianCoordinatesQuaternion v.val)
    (isIcosian_coordinates_of_parity v.val
      (icosianShortCoordinates_parity v.val (Finset.mem_filter.mp v.property).1))
    (icosianNormOneCoordinates_norm v.property)) (by
      constructor
      · intro v w h
        apply Subtype.ext
        apply icosianCoordinatesQuaternion_injective
        exact congrArg (fun u : icosianNormOneGroup => u.val.val) h
      · intro u
        obtain ⟨v,hv,he⟩ := icosianNormOne_exhaust u.property (icosianNormOneGroup_norm u)
        refine ⟨⟨v,hv⟩,?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact he)

instance icosianNormOneGroup_finite : Finite icosianNormOneGroup :=
  Finite.of_equiv _ icosianNormOneCoordinatesEquiv

theorem icosianNormOneGroup_card : Nat.card icosianNormOneGroup=120 := by
  rw [← Nat.card_congr icosianNormOneCoordinatesEquiv]
  simpa using icosianNormOneCoordinates_card

end Atlas.Algebra
