/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu23Simplicity

/-!
# Mathieu23

The concrete sporadic M23 model is the stabilizer of a specified Golay coordinate. This
interface exports its proved order, simplicity, faithful four-transitive action, and
embedding; conjugation in the ambient coordinate group identifies different choices
equivariantly.

Source: `Atlas/Sporadic/Mathieu23.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

/-! M23 as the actual stabilizer of a Golay coordinate, uniformly in that coordinate. -/

namespace Atlas.Sporadic.Mathieu23

abbrev Model (a : Atlas.Codes.Omega) := ↥(Atlas.Codes.Mathieu23PointModel a)
abbrev Points (a : Atlas.Codes.Omega) := Atlas.Codes.Mathieu23Points a

def order : ℕ := 10200960

def embedding (a : Atlas.Codes.Omega) : Model a →* Atlas.Codes.Mathieu24CodeModel :=
  Atlas.Codes.mathieu23_embedding a

theorem embedding_injective (a : Atlas.Codes.Omega) : Function.Injective (embedding a) :=
  Atlas.Codes.mathieu23_embedding_injective a

theorem finite (a : Atlas.Codes.Omega) : Finite (Model a) := inferInstance

theorem card (a : Atlas.Codes.Omega) : Nat.card (Model a) = order :=
  Atlas.Codes.mathieu23_order a

theorem degree (a : Atlas.Codes.Omega) : Nat.card (Points a) = 23 :=
  Atlas.Codes.mathieu23_degree a

theorem faithful (a : Atlas.Codes.Omega) : FaithfulSMul (Model a) (Points a) :=
  Atlas.Codes.mathieu23_faithful a

theorem four_transitive (a : Atlas.Codes.Omega) :
    MulAction.IsMultiplyPretransitive (Model a) (Points a) 4 :=
  Atlas.Codes.mathieu23_four_transitive a

theorem isSimpleGroup (a : Atlas.Codes.Omega) : IsSimpleGroup (Model a) :=
  Atlas.Codes.mathieu23_simple a

theorem exists_mul_ne_mul (a : Atlas.Codes.Omega) : ∃ g h : Model a, g * h ≠ h * g :=
  Atlas.Codes.mathieu23_noncommuting_pair a

/-- Conjugation by the supplied actual group element. -/
noncomputable def conjugacy {a b : Atlas.Codes.Omega} {g : Atlas.Codes.Mathieu24CodeModel}
    (hg : b = g • a) : Model a ≃* Model b := MulAction.stabilizerEquivStabilizer hg

def conjugacyPoints {a b : Atlas.Codes.Omega} {g : Atlas.Codes.Mathieu24CodeModel}
    (hg : b = g • a) : MulActionHom (conjugacy hg) (Points a) (Points b) :=
  SubMulAction.ofStabilizer.conjMap hg

theorem conjugacyPoints_bijective {a b : Atlas.Codes.Omega} {g : Atlas.Codes.Mathieu24CodeModel}
    (hg : b = g • a) : Function.Bijective (conjugacyPoints hg) :=
  SubMulAction.ofStabilizer.conjMap_bijective hg

theorem exists_conjugacy (a b : Atlas.Codes.Omega) :
    ∃ g : Atlas.Codes.Mathieu24CodeModel, b = g • a := by
  obtain ⟨g,hg⟩ := Atlas.Codes.golay_coordinate_transitive a b
  exact ⟨g,hg.symm⟩

structure Construction (a : Atlas.Codes.Omega) : Prop where
  finite : Finite (Model a)
  card : Nat.card (Model a) = order
  simple : IsSimpleGroup (Model a)
  noncommuting : ∃ g h : Model a, g * h ≠ h * g
  degree : Nat.card (Points a) = 23
  faithful : FaithfulSMul (Model a) (Points a)
  four_transitive : MulAction.IsMultiplyPretransitive (Model a) (Points a) 4
  inclusion_injective : Function.Injective (embedding a)

theorem construction (a : Atlas.Codes.Omega) : Construction a :=
  ⟨finite a, card a, isSimpleGroup a, exists_mul_ne_mul a, degree a,
    faithful a, four_transitive a, embedding_injective a⟩

end Atlas.Sporadic.Mathieu23
