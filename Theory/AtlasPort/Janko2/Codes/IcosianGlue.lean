/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianGlue.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic

/-!
# IcosianGlue

The three-block icosian glue is a linear subspace of six coordinates.
An explicit encoder and coefficient equations describe its block symmetries.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianGlue.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


noncomputable section
namespace Atlas.Codes
open Matrix

abbrev IcosianGlueWord (F : Type*) := Fin 3 → Fin 2 → F
abbrev IcosianGlueBlocks (F : Type*) [Field F] := Fin 3 → SpecialLinearGroup (Fin 2) F

/-- The three-block Morita glue; this is a concrete vector submodule. -/
def icosianGlue (F : Type*) [Field F] : Submodule F (IcosianGlueWord F) where
  carrier := {x | x 0 1=x 1 1 ∧ x 1 1=x 2 1 ∧ x 0 0+x 1 0+x 2 0=0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨hx,hx',hx''⟩
    rcases hy with ⟨hy,hy',hy''⟩
    refine ⟨by simp [hx,hy],by simp [hx',hy'],?_⟩
    change (x 0 0+y 0 0)+(x 1 0+y 1 0)+(x 2 0+y 2 0)=0
    linear_combination hx''+hy''
  smul_mem' := by
    intro r x hx
    rcases hx with ⟨hx,hx',hx''⟩
    refine ⟨by simp [hx],by simp [hx'],?_⟩
    change r*x 0 0+r*x 1 0+r*x 2 0=0
    linear_combination r*hx''

@[simp] theorem mem_icosianGlue {F : Type*} [Field F] (x : IcosianGlueWord F) :
    x ∈ icosianGlue F ↔ x 0 1=x 1 1 ∧ x 1 1=x 2 1 ∧ x 0 0+x 1 0+x 2 0=0 := Iff.rfl

def icosianGlueEncoder {F : Type*} [Field F] (u v b : F) : IcosianGlueWord F :=
  ![![u,b],![v,b],![-u-v,b]]

@[simp] theorem icosianGlueEncoder_mem {F : Type*} [Field F] (u v b : F) :
    icosianGlueEncoder u v b ∈ icosianGlue F := by
  simp [icosianGlueEncoder]

theorem icosianGlueBlock_apply {F : Type*} [Field F]
    (g : IcosianGlueBlocks F) (x : IcosianGlueWord F) (i : Fin 3) (r : Fin 2) :
    (g • x) i r = g i r 0*x i 0+g i r 1*x i 1 := by
  change (∑ j : Fin 2, g i r j*x i j)=_
  simp [Fin.sum_univ_two]

/-- Forward preservation is enough to force the entire triangular shape. -/
def IcosianGluePreserves {F : Type*} [Field F] (g : IcosianGlueBlocks F) : Prop :=
  ∀ x : IcosianGlueWord F,x ∈ icosianGlue F → g • x ∈ icosianGlue F

theorem icosianGlue_coefficients {F : Type*} [Field F]
    (g : IcosianGlueBlocks F) (hg : IcosianGluePreserves g) :
    (∀ i,g i 1 0=0) ∧ (∀ i,g i 0 0=g 2 0 0) ∧
    (∀ i,g i 1 1=g 2 1 1) ∧ g 0 0 1+g 1 0 1+g 2 0 1=0 := by
  have hu := hg (icosianGlueEncoder 1 0 0) (icosianGlueEncoder_mem 1 0 0)
  have hv := hg (icosianGlueEncoder 0 1 0) (icosianGlueEncoder_mem 0 1 0)
  have hb := hg (icosianGlueEncoder 0 0 1) (icosianGlueEncoder_mem 0 0 1)
  norm_num [mem_icosianGlue,icosianGlueBlock_apply,icosianGlueEncoder,Matrix.cons_val_two] at hu hv hb
  rcases hu with ⟨hu0,hu1,hu2⟩
  rcases hv with ⟨hv0,hv1,hv2⟩
  rcases hb with ⟨hb0,hb1,hb2⟩
  refine ⟨?_,?_,?_,hb2⟩
  · intro i
    fin_cases i
    · exact hu0
    · exact hv0.symm
    · exact hu1
  · intro i
    fin_cases i
    · exact sub_eq_zero.mp (show g 0 0 0-g 2 0 0=0 by simpa [sub_eq_add_neg] using hu2)
    · exact sub_eq_zero.mp (show g 1 0 0-g 2 0 0=0 by simpa [sub_eq_add_neg] using hv2)
    · rfl
  · intro i
    fin_cases i
    · exact hb0.trans hb1
    · exact hb1
    · rfl

end Atlas.Codes
