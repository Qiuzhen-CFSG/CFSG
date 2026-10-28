/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/StabilizerOrbitTransport.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# StabilizerOrbitTransport

Acting by a group element transports suborbits to those of the conjugate stabilizer.
The action and its inverse give an explicit equivalence of the two orbits.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/StabilizerOrbitTransport.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory
open MulAction
variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

theorem stabilizer_orbit_smul (g : G) (a : X) (x y : Y)
    (h : y ∈ orbit (stabilizer G a) x) :
    g • y ∈ orbit (stabilizer G (g • a)) (g • x) := by
  obtain ⟨r,hr⟩ := mem_orbit_iff.mp h
  let s := stabilizerEquivStabilizer (rfl : g • a = g • a) r
  refine mem_orbit_iff.mpr ⟨s,?_⟩
  change (s.val : G) • (g • x) = g • y
  rw [stabilizerEquivStabilizer_apply]
  simp only [MulAut.conj_apply,mul_smul,inv_smul_smul]
  exact congrArg (fun z : Y => g • z) hr

def stabilizerOrbitTransport (g : G) (a : X) (x : Y) :
    orbit (stabilizer G a) x ≃ orbit (stabilizer G (g • a)) (g • x) where
  toFun y := ⟨g • y.val,stabilizer_orbit_smul g a x y.val y.prop⟩
  invFun y := ⟨g⁻¹ • y.val,by
    convert
      stabilizer_orbit_smul g⁻¹ (g • a) (g • x) y.val y.prop using 1
    rw [inv_smul_smul,inv_smul_smul]⟩
  left_inv y := Subtype.ext (inv_smul_smul g y.val)
  right_inv y := Subtype.ext (smul_inv_smul g y.val)

end Atlas.GroupTheory
