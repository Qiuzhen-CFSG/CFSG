/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/Conway2.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalMinimumLines

/-!
The full norm-four Leech-vector stabilizer and its orthogonal-line action.
Minimum-shell orbit-stabilizer gives its order and its embedding in the central quotient.

Source: Gerald Höhn, `Atlas/Sporadic/Conway2.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.Conway2
open Atlas.Codes Atlas.Lattices Atlas.Conway

/-- A fixed norm-four vector of the retained Golay Leech lattice. -/
def vector : LeechShell 4 :=
  ⟨minimumPairPlus ((0,0),0) ((0,0),1),minimumPairPlus_norm _ _ (by decide)⟩

/-- The actual full vector stabilizer, with its inherited group law. -/
abbrev Model := fullVectorStabilizer vector.val

def order : ℕ := 42305421312000

theorem finite : Finite Model := inferInstance

theorem card : Nat.card Model = order := minimum_vector_stabilizer_order vector

theorem card_factorization : Nat.card Model = 2^18 * 3^6 * 5^3 * 7 * 11 * 23 :=
  minimum_vector_stabilizer_factorization vector

def embedding : Model →* LeechIsometryGroup := (fullVectorStabilizer vector.val).subtype

def toConway1 : Model →* LeechCentralQuotient := vectorStabilizerProjection vector.val

theorem toConway1_injective : Function.Injective toConway1 :=
  vectorStabilizerProjection_injective vector.val (minimum_vector_ne_zero vector)

def antipodalStabilizerEquiv : Model ≃*
    MulAction.stabilizer LeechCentralQuotient (antipodalLine vector.val) :=
  vectorAntipodalStabilizerEquiv vector.val (minimum_vector_ne_zero vector)

theorem shell_index_product : 196560 * Nat.card Model = Nat.card LeechIsometryGroup :=
  minimum_vector_orbit_stabilizer vector

theorem line_index_product : 98280 * Nat.card Model = Nat.card LeechCentralQuotient := by
  simpa only [minimum_lines_card] using minimum_line_orbit_stabilizer vector

abbrev Points := OrthogonalMinimumLines vector.val

theorem degree : Nat.card Points = 46575 := orthogonalMinimumLines_card _ _ (by decide)

theorem transitive : MulAction.IsPretransitive Model Points :=
  orthogonalMinimumLines_pretransitive _ _ (by decide)

end Atlas.Sporadic.Conway2
