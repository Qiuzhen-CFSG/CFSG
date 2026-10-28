/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/OrderedFixingConjugacy.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Tactic.Group

/-!
# OrderedFixingConjugacy

Transporting an ordered configuration conjugates its pointwise fixing subgroup.
Conjugation and inverse conjugation give an explicit multiplicative equivalence.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/OrderedFixingConjugacy.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory

def orderedFixingConjugacy {G X I : Type*} [Group G] [MulAction G X]
    (e f : I → X) (g : G) (hg : ∀ i, g • e i = f i) :
    fixingSubgroup G (Set.range e) ≃* fixingSubgroup G (Set.range f) where
  toFun t := ⟨g*t.val*g⁻¹,by
    intro x
    obtain ⟨i,hi⟩ := x.prop
    rw [← hi,← hg i,mul_smul,mul_smul,inv_smul_smul]
    rw [show t.val • e i = e i from t.prop ⟨e i,⟨i,rfl⟩⟩]⟩
  invFun t := ⟨g⁻¹*t.val*g,by
    intro x
    obtain ⟨i,hi⟩ := x.prop
    rw [← hi,mul_smul,mul_smul,hg]
    rw [show t.val • f i = f i from t.prop ⟨f i,⟨i,rfl⟩⟩,← hg,inv_smul_smul]⟩
  left_inv t := by apply Subtype.ext; dsimp; group
  right_inv t := by apply Subtype.ext; dsimp; group
  map_mul' s t := by apply Subtype.ext; dsimp; group

end Atlas.GroupTheory
