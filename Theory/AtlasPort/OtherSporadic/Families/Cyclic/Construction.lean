/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Families/Cyclic/Construction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Families.Cyclic.Basic

/-!
# Construction

Cyclic groups of prime order supply concrete finite simple models.
The construction packages the explicit cyclic carrier and its intrinsic properties.

Source: Gerald Höhn, ATLAS, `Atlas/Families/Cyclic/Construction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.Families.Cyclic

/-- Properties of the specified residue model and its translation action. -/
structure Construction (p : ℕ) : Prop where
  finite : Finite (Model p)
  card : Nat.card (Model p) = order p
  simple : IsSimpleGroup (Model p)
  commutative : ∀ a b : Model p, a * b = b * a
  cyclic : IsCyclic (Model p)
  generator_order : orderOf (generator p) = p
  generator_generates : Subgroup.zpowers (generator p) = ⊤
  regular : ∀ x y : ZMod p, ∃! a : Model p, a • x = y
  faithful : FaithfulSMul (Model p) (ZMod p)
  transitive : MulAction.IsPretransitive (Model p) (ZMod p)

theorem construction (p : ℕ) (hp : IsAdmissible p) : Construction p where
  finite := finite p hp.pos
  card := card p hp.pos
  simple := isSimpleGroup p hp
  commutative := commutative p
  cyclic := cyclic p
  generator_order := generator_order p
  generator_generates := generator_generates p
  regular := regular p
  faithful := faithful p
  transitive := transitive p

/-- Existence retains an explicit equivalence to the prescribed model. -/
theorem exists_model (p : ℕ) (hp : IsAdmissible p) :
    ∃ (G : Type) (_ : CommGroup G), Nonempty (G ≃* Model p) ∧
      Finite G ∧ Nat.card G = p ∧ IsSimpleGroup G ∧ Construction p := by
  exact ⟨Model p, inferInstance, ⟨MulEquiv.refl _⟩, finite p hp.pos,
    card p hp.pos, isSimpleGroup p hp, construction p hp⟩

end Atlas.Families.Cyclic
