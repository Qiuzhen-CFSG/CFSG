/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/EisensteinSmallNorms.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.Eisenstein

/-!
# Small Eisenstein norms

Bounded integral coordinates give a kernel-checked enumeration of unit orbits of scalars of norm at most twenty-seven.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/EisensteinSmallNorms.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

namespace Atlas.Algebra

/-- Representatives of the scalar unit orbits of norm at most twenty-seven.
The two representatives at split rational primes are retained separately. -/
def eisensteinSmallNormRepresentatives (n : ℤ) : Finset Eisenstein :=
  if n=0 then {0} else if n=1 then {1} else if n=3 then {eisensteinTheta}
  else if n=4 then {2} else if n=7 then {3+eisensteinOmega,2-eisensteinOmega}
  else if n=9 then {3} else if n=12 then {2*eisensteinTheta}
  else if n=13 then {4+eisensteinOmega,3-eisensteinOmega}
  else if n=16 then {4} else if n=19 then {5+2*eisensteinOmega,3-2*eisensteinOmega}
  else if n=21 then {eisensteinTheta*(3+eisensteinOmega),eisensteinTheta*(2-eisensteinOmega)}
  else if n=25 then {5} else if n=27 then {3*eisensteinTheta} else ∅

/-- Every small scalar lies in one of the displayed actual unit orbits.
Only the 169 pairs of bounded scalar coordinates are checked. -/
theorem eisenstein_small_norm_unit (z : Eisenstein) (hz : z.norm ≤ 27) :
    ∃ r ∈ eisensteinSmallNormRepresentatives z.norm, ∃ u : Eisensteinˣ, z = r*(u : Eisenstein) := by
  have hn := eisenstein_norm z
  have hr : -6 ≤ z.re ∧ z.re ≤ 6 := by
    have h1 : 3*z.re^2 ≤ 4*z.norm := by nlinarith [sq_nonneg (z.re-2*z.im)]
    constructor <;> nlinarith
  have hi : -6 ≤ z.im ∧ z.im ≤ 6 := by
    have h1 : 3*z.im^2 ≤ 4*z.norm := by nlinarith [sq_nonneg (z.im-2*z.re)]
    constructor <;> nlinarith
  have hfinite : ∀ a b : Fin 13,
      let w : Eisenstein := ⟨(a.val : ℤ)-6,(b.val : ℤ)-6⟩
      w.norm ≤ 27 → w ∈ (eisensteinSmallNormRepresentatives w.norm).biUnion
        (fun r => eisensteinUnitValues.image (fun u => r*u)) := by decide +kernel
  let a : Fin 13 := ⟨(z.re+6).toNat,by omega⟩
  let b : Fin 13 := ⟨(z.im+6).toNat,by omega⟩
  have ha : (a.val : ℤ)-6 = z.re := by dsimp [a]; omega
  have hb : (b.val : ℤ)-6 = z.im := by dsimp [b]; omega
  have he : (⟨(a.val : ℤ)-6,(b.val : ℤ)-6⟩ : Eisenstein) = z := by ext <;> assumption
  have h := hfinite a b
  simp only [he] at h
  obtain ⟨r,hr,hs⟩ := Finset.mem_biUnion.mp (h hz)
  obtain ⟨u,hu,he'⟩ := Finset.mem_image.mp hs
  obtain ⟨v,hv⟩ := (eisenstein_mem_unitValues u).mp hu
  exact ⟨r,hr,v,he'.symm.trans (congrArg (r*·) hv.symm)⟩

theorem eisenstein_norm_three_unit (z : Eisenstein) (hz : z.norm=3) :
    ∃ u : Eisensteinˣ, z = eisensteinTheta*(u : Eisenstein) := by
  obtain ⟨r,hr,u,hu⟩ := eisenstein_small_norm_unit z (by omega)
  have hr' : r=eisensteinTheta := by simpa [eisensteinSmallNormRepresentatives,hz] using hr
  exact ⟨u,hr' ▸ hu⟩

theorem eisenstein_norm_four_unit (z : Eisenstein) (hz : z.norm=4) :
    ∃ u : Eisensteinˣ, z = 2*(u : Eisenstein) := by
  obtain ⟨r,hr,u,hu⟩ := eisenstein_small_norm_unit z (by omega)
  have hr' : r=2 := by simpa [eisensteinSmallNormRepresentatives,hz] using hr
  exact ⟨u,hr' ▸ hu⟩

theorem eisenstein_norm_nine_unit (z : Eisenstein) (hz : z.norm=9) :
    ∃ u : Eisensteinˣ, z = 3*(u : Eisenstein) := by
  obtain ⟨r,hr,u,hu⟩ := eisenstein_small_norm_unit z (by omega)
  have hr' : r=3 := by simpa [eisensteinSmallNormRepresentatives,hz] using hr
  exact ⟨u,hr' ▸ hu⟩

theorem eisenstein_norm_twelve_unit (z : Eisenstein) (hz : z.norm=12) :
    ∃ u : Eisensteinˣ, z = (2*eisensteinTheta)*(u : Eisenstein) := by
  obtain ⟨r,hr,u,hu⟩ := eisenstein_small_norm_unit z (by omega)
  have hr' : r=2*eisensteinTheta := by simpa [eisensteinSmallNormRepresentatives,hz] using hr
  exact ⟨u,hr' ▸ hu⟩

theorem eisenstein_norm_twentyseven_unit (z : Eisenstein) (hz : z.norm=27) :
    ∃ u : Eisensteinˣ, z = (3*eisensteinTheta)*(u : Eisenstein) := by
  obtain ⟨r,hr,u,hu⟩ := eisenstein_small_norm_unit z (by omega)
  have hr' : r=3*eisensteinTheta := by simpa [eisensteinSmallNormRepresentatives,hz] using hr
  exact ⟨u,hr' ▸ hu⟩

end Atlas.Algebra
