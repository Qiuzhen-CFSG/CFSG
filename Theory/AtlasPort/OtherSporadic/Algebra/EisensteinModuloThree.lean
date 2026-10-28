/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/EisensteinModuloThree.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.Eisenstein

/-!
# Eisenstein residue-one classes modulo three

The theta residue criterion reduces the residue-one class to three explicit lifts modulo three.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/EisensteinModuloThree.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.Algebra

/-- The residue-one theta class has exactly three lifts modulo three. -/
theorem eisenstein_residue_one_mod_three (z : Eisenstein) (hz : eisensteinResidue z=1) :
    (3 : Eisenstein) ∣ z-1 ∨ (3 : Eisenstein) ∣ z-eisensteinOmega ∨
      (3 : Eisenstein) ∣ z-(-1-eisensteinOmega) := by
  obtain ⟨d,hd⟩ := (eisensteinResidue_eq_zero (z-1)).mp (by simp [hz])
  let c : Fin 3 := ⟨(eisensteinResidue d).val,ZMod.val_lt _⟩
  have hc : eisensteinResidue (d-(c.val : Eisenstein))=0 := by
    simp [c]
  obtain ⟨e,he⟩ := (eisensteinResidue_eq_zero _).mp hc
  have hm : z=1+eisensteinTheta*(c.val : Eisenstein)-3*e := by
    linear_combination hd+eisensteinTheta*he+e*eisensteinTheta_sq
  have hcases : ∀ c : Fin 3,
      (3 : Eisenstein) ∣ (1+eisensteinTheta*(c.val : Eisenstein))-1 ∨
      (3 : Eisenstein) ∣ (1+eisensteinTheta*(c.val : Eisenstein))-eisensteinOmega ∨
      (3 : Eisenstein) ∣ (1+eisensteinTheta*(c.val : Eisenstein))-(-1-eisensteinOmega) := by
    intro k
    fin_cases k
    · exact Or.inl ⟨0,by simp⟩
    · right; right
      refine ⟨1+eisensteinOmega,?_⟩
      simp [eisensteinTheta]
      ring
    · right; left
      refine ⟨1+eisensteinOmega,?_⟩
      simp [eisensteinTheta]
      ring
  rcases hcases c with h|h|h
  · left
    rw [hm]
    convert dvd_sub h (dvd_mul_right (3 : Eisenstein) e) using 1; ring
  · right; left
    rw [hm]
    convert dvd_sub h (dvd_mul_right (3 : Eisenstein) e) using 1; ring
  · right; right
    rw [hm]
    convert dvd_sub h (dvd_mul_right (3 : Eisenstein) e) using 1; ring

end Atlas.Algebra
