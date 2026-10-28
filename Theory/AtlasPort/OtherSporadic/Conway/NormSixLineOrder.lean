/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/NormSixLineOrder.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.DerivedCrossTransitivity
public import Theory.AtlasPort.OtherSporadic.Conway.AntipodalStabilizer
public import Theory.AtlasPort.OtherSporadic.Conway.NormSixOrder
/-!
The concrete norm-six Leech shell and its stabilizers.
Coordinate orbit transport and orbit-stabilizer counting identify the full stabilizer.

Source: Gerald Höhn, `Atlas/Conway/NormSixLineOrder.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option maxRecDepth 10000
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- Intrinsic antipodal lines represented by norm-six vectors. -/
def NormSixLines := {l : LeechAntipodalLine // ∃ x : LeechShell 6, antipodalLine x.val = l}

theorem normSix_line_orbit (x : LeechShell 6) :
    MulAction.orbit LeechCentralQuotient (antipodalLine x.val) =
      {l | ∃ y : LeechShell 6, antipodalLine y.val = l} := by
  ext l
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨g,rfl⟩ := leechCentralProjection_surjective q
    exact ⟨g • x, (projection_antipodalLine g x.val).symm⟩
  · rintro ⟨y,rfl⟩
    let := full_normSix_pretransitive
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq LeechIsometryGroup x y
    refine ⟨leechCentralProjection g,?_⟩
    exact (projection_antipodalLine g x.val).trans
      (congrArg antipodalLine (congrArg Subtype.val hg))

def normSixLineOrbitEquiv (x : LeechShell 6) :
    MulAction.orbit LeechCentralQuotient (antipodalLine x.val) ≃ NormSixLines :=
  Equiv.setCongr (normSix_line_orbit x)

theorem normSix_line_stabilizer_order (x : LeechShell 6) :
    Nat.card (MulAction.stabilizer LeechCentralQuotient (antipodalLine x.val)) =
      495766656000 := by
  rw [← Nat.card_congr (vectorAntipodalStabilizerEquiv x.val (normSix_vector_ne_zero x)).toEquiv]
  exact normSix_vector_stabilizer_order x

theorem normSix_line_orbit_stabilizer (x : LeechShell 6) :
    Nat.card NormSixLines * Nat.card (fullVectorStabilizer x.val) =
      Nat.card LeechCentralQuotient := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    LeechCentralQuotient (antipodalLine x.val))
  rw [Nat.card_prod,Nat.card_congr (normSixLineOrbitEquiv x),
    ← Nat.card_congr (vectorAntipodalStabilizerEquiv x.val (normSix_vector_ne_zero x)).toEquiv] at h
  exact h

theorem normSix_lines_card : Nat.card NormSixLines = 8386560 := by
  let x : LeechShell 6 := ⟨normSixBase,normSixVector_norm _⟩
  have h := normSix_line_orbit_stabilizer x
  rw [normSix_vector_stabilizer_order,leechCentralQuotient_order] at h
  apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 495766656000)
  exact h.trans (by norm_num)

theorem normSix_antipodal_index (x : LeechShell 6) :
    (MulAction.stabilizer LeechCentralQuotient (antipodalLine x.val)).index = 8386560 := by
  change Nat.card (LeechCentralQuotient ⧸ MulAction.stabilizer LeechCentralQuotient (antipodalLine x.val)) = 8386560
  rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer
    LeechCentralQuotient (antipodalLine x.val)),Nat.card_congr (normSixLineOrbitEquiv x)]
  exact normSix_lines_card

end Atlas.Conway
