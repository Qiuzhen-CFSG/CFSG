/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianGlueClassification.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianGlue

/-!
# IcosianGlueClassification

The block-diagonal glue symmetries are determined by scalar and unipotent
parameters. Evaluating the defining constraints on information vectors proves
both necessity and sufficiency of these coefficient equations.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianGlueClassification.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


noncomputable section
namespace Atlas.Codes
open Matrix

/-- Complete coefficient description of a block-fixing glue automorphism. -/
def IcosianGlueBlockForm {F : Type*} [Field F] (g : IcosianGlueBlocks F)
    (s : Fˣ) (c : Fin 3 → F) : Prop :=
  c 0+c 1+c 2=0 ∧ ∀ i,
    g i 0 0=(s : F)⁻¹ ∧ g i 0 1=c i ∧ g i 1 0=0 ∧ g i 1 1=(s : F)

theorem icosianGlue_preserves_form {F : Type*} [Field F]
    (g : IcosianGlueBlocks F) (hg : IcosianGluePreserves g) :
    ∃ s : Fˣ,∃ c : Fin 3 → F,IcosianGlueBlockForm g s c := by
  obtain ⟨hl,ha,hd,hc⟩ := icosianGlue_coefficients g hg
  have hdet : g 2 0 0*g 2 1 1=1 := by
    have h := (g 2).property
    rw [Matrix.det_fin_two] at h
    simpa only [hl 2,mul_zero,sub_zero] using h
  have hs : g 2 1 1≠0 := by intro h; simp [h] at hdet
  let s : Fˣ := Units.mk0 (g 2 1 1) hs
  have hinv : g 2 0 0=(s : F)⁻¹ := by
    change g 2 0 0=(g 2 1 1)⁻¹
    calc
      g 2 0 0 = g 2 0 0*(g 2 1 1*(g 2 1 1)⁻¹) := by rw [mul_inv_cancel₀ hs,mul_one]
      _ = (g 2 0 0*g 2 1 1)*(g 2 1 1)⁻¹ := by ring
      _ = (g 2 1 1)⁻¹ := by rw [hdet,one_mul]
  exact ⟨s,(fun i => g i 0 1),hc,fun i => ⟨(ha i).trans hinv,rfl,hl i,hd i⟩⟩

theorem icosianGlue_form_preserves {F : Type*} [Field F]
    (g : IcosianGlueBlocks F) (s : Fˣ) (c : Fin 3 → F)
    (hg : IcosianGlueBlockForm g s c) : IcosianGluePreserves g := by
  intro x hx
  rcases hg with ⟨hc,hg⟩
  rcases hx with ⟨hx0,hx1,hx2⟩
  rcases hg 0 with ⟨h00,h01,h02,h03⟩
  rcases hg 1 with ⟨h10,h11,h12,h13⟩
  rcases hg 2 with ⟨h20,h21,h22,h23⟩
  simp only [mem_icosianGlue,icosianGlueBlock_apply,h00,h01,h02,h03,
    h10,h11,h12,h13,h20,h21,h22,h23,zero_mul,zero_add]
  refine ⟨by rw [hx0],by rw [hx1],?_⟩
  rw [hx0,hx1]
  linear_combination (s : F)⁻¹*hx2+x 2 1*hc

theorem icosianGlue_preserves_iff {F : Type*} [Field F] (g : IcosianGlueBlocks F) :
    IcosianGluePreserves g ↔ ∃ s : Fˣ,∃ c : Fin 3 → F,IcosianGlueBlockForm g s c :=
  ⟨icosianGlue_preserves_form g,fun ⟨s,c,h⟩ => icosianGlue_form_preserves g s c h⟩

end Atlas.Codes
