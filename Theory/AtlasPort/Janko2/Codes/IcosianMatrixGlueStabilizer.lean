/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianMatrixGlueStabilizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianMatrixGlue

/-!
# IcosianMatrixGlueStabilizer

The monomial stabilizers of matrix glue and single-column glue coincide.
Encoding a column with a zero second column proves the converse implication
and transfers the order 288 over four elements.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianMatrixGlueStabilizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


noncomputable section
namespace Atlas.Codes
open Matrix

/-- Actual left block-matrix multiplication and block permutations. -/
instance icosianMatrixGlueMonomialAction {F : Type*} [Field F] :
    MulAction (IcosianGlueMonomialGroup F) (IcosianMatrixGlueWord F) where
  smul g x := fun i => (g.left i).val*x (g.right.symm i)
  one_smul x := by
    funext i
    change (1 : Matrix (Fin 2) (Fin 2) F)*x i=x i
    exact one_mul _
  mul_smul g h x := by
    funext i
    change ((g.left i).val*(h.left (g.right.symm i)).val)*
      x (h.right.symm (g.right.symm i))=(g.left i).val*
        ((h.left (g.right.symm i)).val*x (h.right.symm (g.right.symm i)))
    exact mul_assoc _ _ _

/-- The actual matrix action induces the same vector action on each column. -/
theorem icosianMatrixGlue_column_smul {F : Type*} [Field F]
    (g : IcosianGlueMonomialGroup F) (x : IcosianMatrixGlueWord F) (j : Fin 2) :
    icosianGlueColumn (g • x) j=g • icosianGlueColumn x j := by
  funext i r
  rfl

/-- Single-column embedding detects all vector-glue constraints. -/
theorem icosianMatrixGlueEncoder_zero_mem_iff {F : Type*} [Field F]
    (u : IcosianGlueWord F) :
    icosianMatrixGlueEncoder u 0 ∈ icosianMatrixGlue F ↔ u ∈ icosianGlue F := by
  constructor
  · intro h
    exact h 0
  · intro h j
    fin_cases j
    · exact h
    · exact (icosianGlue F).zero_mem

theorem icosianMatrixGlue_encoder_smul {F : Type*} [Field F]
    (g : IcosianGlueMonomialGroup F) (u v : IcosianGlueWord F) :
    g • icosianMatrixGlueEncoder u v=icosianMatrixGlueEncoder (g • u) (g • v) := by
  rw [← icosianMatrixGlue_reconstruct (g • icosianMatrixGlueEncoder u v)]
  rw [icosianMatrixGlue_column_smul,icosianMatrixGlue_column_smul,
    icosianMatrixGlueEncoder_column_zero,icosianMatrixGlueEncoder_column_one]

/-- Full preservation of the two-column module is equivalent to full
preservation of its actual Morita image W. -/
theorem icosianMatrixGlue_stabilizes_iff {F : Type*} [Field F]
    (g : IcosianGlueMonomialGroup F) :
    (∀ x : IcosianMatrixGlueWord F,g • x ∈ icosianMatrixGlue F ↔ x ∈ icosianMatrixGlue F) ↔
      g ∈ icosianGlueMonomialStabilizer F := by
  constructor
  · intro hg u
    have h := hg (icosianMatrixGlueEncoder u 0)
    rw [icosianMatrixGlue_encoder_smul] at h
    have hz : g • (0 : IcosianGlueWord F)=0 := by
      funext i r
      rw [icosianGlueMonomial_smul,icosianGlueBlock_apply]
      simp [icosianGluePermute]
    rw [hz,icosianMatrixGlueEncoder_zero_mem_iff,icosianMatrixGlueEncoder_zero_mem_iff] at h
    exact h
  · intro hg x
    simp only [mem_icosianMatrixGlue,icosianMatrixGlue_column_smul]
    exact forall_congr' (fun j => hg (icosianGlueColumn x j))

def icosianMatrixGlueMonomialStabilizer (F : Type*) [Field F] :
    Subgroup (IcosianGlueMonomialGroup F) where
  carrier := {g | ∀ x : IcosianMatrixGlueWord F,
    g • x ∈ icosianMatrixGlue F ↔ x ∈ icosianMatrixGlue F}
  one_mem' := by intro x; simp
  mul_mem' := by intro g h hg hh x; rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg x
    have h := hg (g⁻¹ • x)
    simpa only [smul_inv_smul] using h.symm

theorem icosianMatrixGlueMonomialStabilizer_eq {F : Type*} [Field F] :
    icosianMatrixGlueMonomialStabilizer F=icosianGlueMonomialStabilizer F := by
  ext g
  exact icosianMatrixGlue_stabilizes_iff g

theorem icosianMatrixGlueMonomialStabilizer_card_four {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F=4) : Nat.card (icosianMatrixGlueMonomialStabilizer F)=288 := by
  rw [icosianMatrixGlueMonomialStabilizer_eq]
  exact icosianGlueMonomialStabilizer_card_four hF

end Atlas.Codes
