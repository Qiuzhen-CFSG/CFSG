/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinResidueUnitForms.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.EisensteinSmallNorms
public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinPhases

/-!
# Eisenstein Residue Unit Forms

Small Eisenstein scalars with a prescribed residue admit explicit unit forms. The finite norm classification and residue arithmetic supply the cases.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinResidueUnitForms.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- Scalar representatives congruent to one modulo three, retaining both
associate types at norms seven and thirteen. -/
def eisensteinResidueOneForms (n : ℤ) : Finset Eisenstein :=
  if n=1 then {1} else if n=4 then {-2}
  else if n=7 then {1+3*eisensteinOmega,-2-3*eisensteinOmega}
  else if n=13 then {1-3*eisensteinOmega,4+3*eisensteinOmega}
  else if n=16 then {4} else ∅

/-- Every scalar of residue one and norm at most sixteen has one of the
normalized forms, up to an actual cubic phase. Only81 scalar coordinate pairs
are checked; no lattice vector or frame is enumerated. -/
theorem eisensteinResidueOne_normalize (z : Eisenstein) (hz : z.norm≤16)
    (hr : eisensteinResidue z=1) :
    ∃ r ∈ eisensteinResidueOneForms z.norm, ∃ a : ZMod 3, z=eisensteinPhase a*r := by
  have hn := eisenstein_norm z
  have hx : -4≤z.re ∧ z.re≤4 := by
    have h1 : 3*z.re^2≤4*z.norm := by nlinarith [sq_nonneg (z.re-2*z.im)]
    constructor <;> nlinarith
  have hy : -4≤z.im ∧ z.im≤4 := by
    have h1 : 3*z.im^2≤4*z.norm := by nlinarith [sq_nonneg (z.im-2*z.re)]
    constructor <;> nlinarith
  have hf : ∀ a b : Fin 9,
      let w : Eisenstein := ⟨(a.val : ℤ)-4,(b.val : ℤ)-4⟩
      w.norm≤16 → eisensteinResidue w=1 →
        w ∈ (eisensteinResidueOneForms w.norm).biUnion
          (fun r => Finset.univ.image (fun c : ZMod 3 => eisensteinPhase c*r)) := by decide +kernel
  let a : Fin 9 := ⟨(z.re+4).toNat,by omega⟩
  let b : Fin 9 := ⟨(z.im+4).toNat,by omega⟩
  have ha : (a.val : ℤ)-4=z.re := by dsimp [a]; omega
  have hb : (b.val : ℤ)-4=z.im := by dsimp [b]; omega
  have he : (⟨(a.val : ℤ)-4,(b.val : ℤ)-4⟩ : Eisenstein)=z := by ext <;> assumption
  have hh := hf a b
  simp only [he] at hh
  obtain ⟨r,hrr,hri⟩ := Finset.mem_biUnion.mp (hh hz hr)
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hri
  exact ⟨r,hrr,c,hc.symm⟩

end Atlas.Lattices
