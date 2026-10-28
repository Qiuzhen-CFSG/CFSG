/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinCongruence.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Algebra.Eisenstein
public import Theory.AtlasPort.Janko2.Codes.TernaryGolay

/-!
# Eisenstein Congruence

The integral Eisenstein Leech module is defined by ternary Golay and sum congruences. Closure follows from the code submodule and divisibility arithmetic.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinCongruence.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

abbrev EisensteinCoordinates := Fin 12 → Eisenstein

def eisensteinWordResidue (u : EisensteinCoordinates) : TernaryWord :=
  fun i => eisensteinResidue (u i)

/-- Witness form of the job's three congruences, without a partial division operator. -/
def EisensteinCongruence (z : EisensteinCoordinates) (m : Eisenstein) : Prop :=
  ∃ u : EisensteinCoordinates,
    (∀ i, z i = m + eisensteinTheta * u i) ∧
    eisensteinWordResidue u ∈ ternaryGolay ∧
    3 * eisensteinTheta ∣ (∑ i, z i) + 3 * m

theorem eisenstein_constant_residue_mem (a : Eisenstein) :
    (fun _ : Fin 12 => eisensteinResidue a) ∈ ternaryGolay := by
  convert ternaryGolay.smul_mem (eisensteinResidue a) ternaryGolay_one using 1
  ext i; simp

theorem eisensteinCongruence_change_lift (z : EisensteinCoordinates) (m a : Eisenstein) :
    EisensteinCongruence z m → EisensteinCongruence z (m + eisensteinTheta*a) := by
  rintro ⟨u, hu, hc, hd⟩
  refine ⟨fun i => u i-a, ?_, ?_, ?_⟩
  · intro i; rw [hu i]; ring
  · have h := ternaryGolay.sub_mem hc (eisenstein_constant_residue_mem a)
    convert h using 1
    ext i; simp [eisensteinWordResidue]
  · convert dvd_add hd (dvd_mul_right (3*eisensteinTheta) a) using 1; ring

theorem eisensteinCongruence_lift_independent (z : EisensteinCoordinates) (m a : Eisenstein) :
    EisensteinCongruence z (m + eisensteinTheta*a) ↔ EisensteinCongruence z m := by
  constructor
  · intro h
    simpa using eisensteinCongruence_change_lift z (m+eisensteinTheta*a) (-a) h
  · exact eisensteinCongruence_change_lift z m a

/-- The specified integral Eisenstein congruence module; comparison with Leech is separate. -/
def eisensteinLeechModule : Submodule Eisenstein EisensteinCoordinates where
  carrier := {z | ∃ m, EisensteinCongruence z m}
  zero_mem' := by
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · simp
    · have hz : eisensteinWordResidue 0 = 0 := by ext i; simp [eisensteinWordResidue]
      rw [hz]; exact ternaryGolay.zero_mem
    · simp
  add_mem' := by
    rintro z w ⟨m,u,hu,hc,hd⟩ ⟨n,v,hv,he,hf⟩
    refine ⟨m+n, u+v, ?_, ?_, ?_⟩
    · intro i; simp only [Pi.add_apply, hu i, hv i]; ring
    · convert ternaryGolay.add_mem hc he using 1
      ext i; simp [eisensteinWordResidue]
    · convert dvd_add hd hf using 1; simp [Finset.sum_add_distrib]; ring
  smul_mem' := by
    rintro c z ⟨m,u,hu,hc,hd⟩
    refine ⟨c*m, c • u, ?_, ?_, ?_⟩
    · intro i; simp only [Pi.smul_apply, smul_eq_mul, hu i]; ring
    · convert ternaryGolay.smul_mem (eisensteinResidue c) hc using 1
      ext i; simp [eisensteinWordResidue, Pi.smul_apply, smul_eq_mul]
    · convert hd.mul_left c using 1; simp [Finset.mul_sum, mul_add]; ring


theorem eisensteinLeechModule_contains_multiple (w : EisensteinCoordinates) :
    (3*eisensteinTheta) • w ∈ eisensteinLeechModule := by
  refine ⟨0, 3 • w, ?_, ?_, ?_⟩
  · intro i; simp only [Pi.smul_apply, smul_eq_mul, zero_add]; ring
  · have hz : eisensteinWordResidue (3 • w) = 0 := by
      ext i
      simp [eisensteinWordResidue, Pi.smul_apply,
        show eisensteinResidue 3 = 0 by decide +kernel]
    rw [hz]; exact ternaryGolay.zero_mem
  · simpa only [Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, ← Finset.mul_sum]
      using dvd_mul_right (3*eisensteinTheta) (∑ i, w i)

theorem eisensteinLeechModule_coordinate_frame (i : Fin 12) :
    Pi.single i (3*eisensteinTheta) ∈ eisensteinLeechModule := by
  convert eisensteinLeechModule_contains_multiple (Pi.single i 1) using 1
  funext j; by_cases h : j=i <;> simp [Pi.smul_apply, h]
end Atlas.Lattices
