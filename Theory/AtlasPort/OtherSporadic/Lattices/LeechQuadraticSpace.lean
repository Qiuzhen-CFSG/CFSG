/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechQuadraticSpace.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechModTwoForms
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
The nondegenerate binary quadratic space obtained from the Leech lattice.
Self-duality forces a lift of every radical element to lie in twice the lattice.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

def leechPolarAdd (a : LeechModTwo) : LeechModTwo →+ Bit where
  toFun b := leechPolar a b
  map_zero' := by
    have h := leechPolar_add_right a 0 0
    rw [add_zero] at h
    exact add_eq_left.mp h.symm
  map_add' := leechPolar_add_right a

def leechPolarBilin : LinearMap.BilinForm Bit LeechModTwo :=
  (({
    toFun := fun a => (leechPolarAdd a).toZModLinearMap 2
    map_zero' := by
      ext b
      have h := leechPolar_add_left 0 0 b
      rw [add_zero] at h
      exact add_eq_left.mp h.symm
    map_add' := by intro a b; ext c; exact leechPolar_add_left a b c
  } : LeechModTwo →+ (LeechModTwo →ₗ[Bit] Bit)).toZModLinearMap 2)

def leechQuadraticForm : QuadraticForm Bit LeechModTwo where
  toFun := leechQuadratic
  toFun_smul c a := by
    rcases bit_cases c with rfl | rfl <;> simp [leechQuadratic_zero]
  exists_companion' := ⟨leechPolarBilin,leechQuadratic_add⟩

theorem leechPolar_radical_lift (x : leech)
    (hx : ∀ y : leech, (leechIntegralPairing x y : Bit) = 0) : x ∈ twiceLeech := by
  let w : RationalCoordinates := (1 / 2 : ℚ) • rationalEmbedding x.val
  have hw : w ∈ leechDual := by
    intro v hv
    obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hv
    have hd : 2 ∣ leechIntegralPairing x ⟨y,hy⟩ :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (hx ⟨y,hy⟩)
    obtain ⟨k,hk⟩ := hd
    apply Submodule.mem_one.mpr
    refine ⟨k,?_⟩
    change (k : ℚ) = rationalForm w (rationalEmbedding y)
    simp only [w,map_smul,LinearMap.smul_apply,smul_eq_mul]
    rw [← leechIntegralPairing_rational x ⟨y,hy⟩,hk]
    push_cast
    ring
  rw [leech_selfDual] at hw
  obtain ⟨y,hy,he⟩ := Submodule.mem_map.mp hw
  refine ⟨⟨y,hy⟩,?_⟩
  apply Subtype.ext
  ext i
  change 2 * y i = x.val i
  have hi := congrFun he i
  change (y i : ℚ) = (1 / 2 : ℚ) * (x.val i : ℚ) at hi
  exact_mod_cast (show (2 : ℚ) * (y i : ℚ) = (x.val i : ℚ) by linarith)

theorem leechPolar_nondegenerate (a : LeechModTwo) (ha : ∀ b, leechPolar a b = 0) : a = 0 := by
  obtain ⟨x,rfl⟩ := leechReduction_surjective a
  apply (leechReduction_eq_zero x).mpr
  apply (twiceLeech_mem x).mp
  apply leechPolar_radical_lift x
  intro y
  rw [← leechPolar_reduce]
  exact ha (leechReduction y)

theorem leechQuadraticForm_polar : leechQuadraticForm.polarBilin = leechPolarBilin := by
  ext a b
  change leechQuadratic (a+b) - leechQuadratic a - leechQuadratic b = leechPolar a b
  rw [leechQuadratic_add]
  ring

end Atlas.Lattices
