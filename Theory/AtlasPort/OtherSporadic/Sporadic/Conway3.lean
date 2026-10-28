/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway3.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.NormSixLineOrder
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleBase
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechShortShellCounts
/-!
The concrete norm-six Leech shell and its stabilizers.
Coordinate orbit transport and orbit-stabilizer counting identify the full stabilizer.

Source: Gerald Höhn, `Atlas/Sporadic/Conway3.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway3
open Atlas.Codes Atlas.Lattices Atlas.Conway

/-- The actual norm-six Leech vector with coordinates (5,1,...,1). -/
def vector : LeechShell 6 := ⟨normSixVector ((0,0),0),normSixVector_norm _⟩

/-- The full stabilizer itself, not a permutation image. -/
abbrev Model := fullVectorStabilizer vector.val

theorem finite : Finite Model := inferInstance

theorem vector_norm : integerDot vector.val.val vector.val.val = 48 := vector.prop

def embedding : Model →* LeechIsometryGroup := (fullVectorStabilizer vector.val).subtype

theorem embedding_injective : Function.Injective embedding := Subtype.val_injective

def toConway1 : Model →* LeechCentralQuotient := vectorStabilizerProjection vector.val

theorem toConway1_injective : Function.Injective toConway1 :=
  vectorStabilizerProjection_injective vector.val (normSixVector_ne_zero _)

def antipodalStabilizerEquiv : Model ≃*
    MulAction.stabilizer LeechCentralQuotient (antipodalLine vector.val) :=
  vectorAntipodalStabilizerEquiv vector.val (normSixVector_ne_zero _)

def mathieu23Embedding : Mathieu23PointModel ((0,0),0) →* Model :=
  mathieu23ToNormSixStabilizer _

theorem mathieu23Embedding_injective : Function.Injective mathieu23Embedding :=
  mathieu23ToNormSixStabilizer_injective _

abbrev Complement := leechOrthogonalComplement vector.val

theorem complement_rank : Module.finrank ℤ Complement = 23 :=
  leechOrthogonalComplement_rank vector.val (by rw [vector_norm]; decide)

def integralRepresentation : Model →* (Complement ≃ₗ[ℤ] Complement) :=
  leechComplementRepresentation vector.val

theorem integralRepresentation_injective : Function.Injective integralRepresentation :=
  leechComplementRepresentation_injective vector.val (by rw [vector_norm]; decide)

theorem integralRepresentation_preserves (g : Model) (x y : Complement) :
    integerDot (integralRepresentation g x).val.val (integralRepresentation g y).val.val =
      integerDot x.val.val y.val.val := leechComplementRepresentation_preserves vector.val g x y

theorem shell_card : Nat.card (LeechShell 6) = 16773120 := leech_six_shell_card

def order : ℕ := 495766656000

theorem card : Nat.card Model = order := normSix_vector_stabilizer_order vector

theorem card_factorization : Nat.card Model = 2^10 * 3^7 * 5^3 * 7 * 11 * 23 :=
  normSix_vector_stabilizer_factorization vector

theorem shell_transitive : MulAction.IsPretransitive LeechIsometryGroup (LeechShell 6) :=
  full_normSix_pretransitive

theorem shell_index_product : 16773120 * Nat.card Model = Nat.card LeechIsometryGroup :=
  normSix_vector_orbit_stabilizer vector

theorem line_index_product : 8386560 * Nat.card Model = Nat.card LeechCentralQuotient := by
  simpa only [normSix_lines_card] using normSix_line_orbit_stabilizer vector

theorem line_index :
    (MulAction.stabilizer LeechCentralQuotient (antipodalLine vector.val)).index = 8386560 :=
  normSix_antipodal_index vector

end Atlas.Sporadic.Conway3
