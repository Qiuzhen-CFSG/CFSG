/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/IcosianGlueRepeatedBlocks.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Codes.IcosianGlueClassification

/-!
# IcosianGlueRepeatedBlocks

In characteristic two, two equal scalar blocks preserve glue precisely when
they are upper triangular and the third block is their diagonal part. The
proof specializes the general coefficient constraints.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/IcosianGlueRepeatedBlocks.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports, public module boundaries, and
proof syntax updated for the local APIs and linters.
-/

@[expose] public section


namespace Atlas.Codes
open scoped Matrix

theorem icosianGlue_preserves_of_coefficients {F : Type*} [Field F]
    (g : IcosianGlueBlocks F)
    (hl : ∀ i,g i 1 0=0) (ha : ∀ i,g i 0 0=g 2 0 0)
    (hd : ∀ i,g i 1 1=g 2 1 1)
    (hc : g 0 0 1+g 1 0 1+g 2 0 1=0) : IcosianGluePreserves g := by
  intro x hx
  rcases hx with ⟨hx0,hx1,hx2⟩
  simp only [mem_icosianGlue,icosianGlueBlock_apply,hl,ha,hd,zero_mul,zero_add]
  refine ⟨by rw [hx0],by rw [hx1],?_⟩
  rw [hx0,hx1]
  linear_combination (g 2 0 0)*hx2+(x 2 1)*hc

/-- When two scalar blocks coincide in characteristic two, preservation of the
full glue forces the third block to be their diagonal part. -/
theorem icosianGlue_repeated_blocks_iff {F : Type*} [Field F]
    (htwo : ∀ x : F,x+x=0) (a b : Matrix.SpecialLinearGroup (Fin 2) F) :
    IcosianGluePreserves ![b,a,a] ↔
      a 1 0=0 ∧ b 0 0=a 0 0 ∧ b 1 1=a 1 1 ∧ b 1 0=0 ∧ b 0 1=0 := by
  constructor
  · intro h
    obtain ⟨hl,ha,hd,hc⟩ := icosianGlue_coefficients ![b,a,a] h
    refine ⟨hl 1,ha 0,hd 0,hl 0,?_⟩
    change b 0 1+a 0 1+a 0 1=0 at hc
    simpa only [add_assoc,htwo,add_zero] using hc
  · rintro ⟨hl,ha,hd,hb,hc⟩
    apply icosianGlue_preserves_of_coefficients
    · intro i; fin_cases i
      · exact hb
      · exact hl
      · exact hl
    · intro i; fin_cases i <;> simp [ha]
    · intro i; fin_cases i <;> simp [hd]
    · change b 0 1+a 0 1+a 0 1=0
      rw [hc,zero_add]
      exact htwo (a 0 1)

end Atlas.Codes
