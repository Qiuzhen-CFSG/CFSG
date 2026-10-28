module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/FieldTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.Basic
set_option warningAsError false

/-!
# Field transport for split octonions and G₂

Coefficientwise transport preserves the integral octonion multiplication table.
Conjugating by it therefore identifies the full multiplication-preserving
linear automorphism groups, and intertwines their actual actions.
-/

@[expose] public section

namespace Atlas.SplitOctonion
variable {F K : Type*} [Field F] [Field K]

def mapCoefficients (e : F ≃+* K) (x : Carrier F) : Carrier K := fun i => e (x i)
@[simp] theorem mapCoefficients_add (e : F ≃+* K) (x y : Carrier F) :
    mapCoefficients e (x+y) = mapCoefficients e x + mapCoefficients e y := by
  ext i; exact e.map_add _ _
@[simp] theorem mapCoefficients_smul (e : F ≃+* K) (r : F) (x : Carrier F) :
    mapCoefficients e (r • x) = e r • mapCoefficients e x := by
  ext i; exact e.map_mul _ _
@[simp] theorem mapCoefficients_symm (e : F ≃+* K) (x : Carrier K) :
    mapCoefficients e (mapCoefficients e.symm x) = x := by
  ext i; exact e.apply_symm_apply _
@[simp] theorem mapCoefficients_symm' (e : F ≃+* K) (x : Carrier F) :
    mapCoefficients e.symm (mapCoefficients e x) = x := by
  ext i; exact e.symm_apply_apply _
@[simp] theorem mapCoefficients_mul (e : F ≃+* K) (x y : Carrier F) :
    mapCoefficients e (mul x y) = mul (mapCoefficients e x) (mapCoefficients e y) := by
  ext i; fin_cases i <;> simp [mapCoefficients,mul]

/-- Conjugating linear automorphisms by coefficientwise field transport. -/
def transportLinear (e : F ≃+* K) (g : Carrier F ≃ₗ[F] Carrier F) :
    Carrier K ≃ₗ[K] Carrier K where
  toFun x := mapCoefficients e (g (mapCoefficients e.symm x))
  invFun x := mapCoefficients e (g.symm (mapCoefficients e.symm x))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp] theorem transportLinear_apply (e : F ≃+* K) (g : Carrier F ≃ₗ[F] Carrier F)
    (x : Carrier K) : transportLinear e g x =
    mapCoefficients e (g (mapCoefficients e.symm x)) := rfl

/-- Transport of the full multiplication-preserving automorphism group. -/
def transportAutomorphism (e : F ≃+* K) (g : Automorphism F) : Automorphism K :=
  ⟨transportLinear e g.val, by
    intro x y
    change mapCoefficients e (g.val (mapCoefficients e.symm (mul x y))) = _
    rw [mapCoefficients_mul, automorphism_mul, mapCoefficients_mul]
    rfl⟩

@[simp] theorem transportAutomorphism_apply (e : F ≃+* K) (g : Automorphism F)
    (x : Carrier K) : (transportAutomorphism e g).val x =
    mapCoefficients e (g.val (mapCoefficients e.symm x)) := rfl
end Atlas.SplitOctonion

namespace Atlas.G2
open Atlas.SplitOctonion
variable {F K : Type*} [Field F] [Field K]
/-- The actual octonion automorphism models are transported coefficientwise. -/
def fieldEquiv (e : F ≃+* K) : Model F ≃* Model K where
  toFun := transportAutomorphism e
  invFun := transportAutomorphism e.symm
  left_inv g := by
    apply Atlas.Algebra.MultiplicativeLinearAut.ext
    intro x
    change mapCoefficients e.symm (mapCoefficients e (g.val
      (mapCoefficients e.symm (mapCoefficients e x)))) = g.val x
    simp
  right_inv g := by
    apply Atlas.Algebra.MultiplicativeLinearAut.ext
    intro x
    change mapCoefficients e (mapCoefficients e.symm (g.val
      (mapCoefficients e (mapCoefficients e.symm x)))) = g.val x
    simp
  map_mul' g h := by
    apply Atlas.Algebra.MultiplicativeLinearAut.ext
    intro x
    change mapCoefficients e (g.val (h.val (mapCoefficients e.symm x))) =
      mapCoefficients e (g.val (mapCoefficients e.symm (mapCoefficients e
        (h.val (mapCoefficients e.symm x)))))
    simp
/-- The comparison intertwines the actual actions through coefficient transport. -/
@[simp] theorem fieldEquiv_action (e : F ≃+* K) (g : Model F) (x : Carrier F) :
    (fieldEquiv e g).val (mapCoefficients e x) = mapCoefficients e (g.val x) := by
  change mapCoefficients e (g.val (mapCoefficients e.symm (mapCoefficients e x))) = _
  simp
end Atlas.G2
