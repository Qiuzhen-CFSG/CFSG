module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/Torus.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.RootGroups
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.FieldTheory.Finiteness

/-! Diagonal weights give the split torus of octonion automorphisms; coordinate identities verify multiplication preservation. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion
variable {K : Type*} [Field K]

def torusWeights (l m : Kˣ) : Fin 8 → Kˣ :=
  ![l,m,l*m⁻¹,1,1,l⁻¹*m,m⁻¹,l⁻¹]

def torusLinear (l m : Kˣ) : Carrier K →ₗ[K] Carrier K where
  toFun x i := (torusWeights l m i : K) * x i
  map_add' x y := by ext i; simp [_root_.mul_add]
  map_smul' r x := by ext i; simp [mul_left_comm]

def torusEquiv (l m : Kˣ) : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := torusLinear l m
  invFun x i := ((torusWeights l m i)⁻¹ : Kˣ) * x i
  left_inv x := by
    ext i
    change ((torusWeights l m i)⁻¹ : Kˣ) * ((torusWeights l m i : K) * x i) = x i
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    ext i
    change (torusWeights l m i : K) * (((torusWeights l m i)⁻¹ : Kˣ) * x i) = x i
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem torus_mul (l m : Kˣ) (x y : Carrier K) :
    torusEquiv l m (mul x y) = mul (torusEquiv l m x) (torusEquiv l m y) := by
  ext i; fin_cases i <;>
    simp [torusEquiv,torusLinear,torusWeights,mul] <;>
    field_simp

def torus (l m : Kˣ) : Model K := ⟨torusEquiv l m,torus_mul l m⟩

/-- The two-dimensional split torus in the actual automorphism group. -/
def torusHom : (Kˣ × Kˣ) →* Model K where
  toFun p := torus p.1 p.2
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext i; fin_cases i <;> simp [torus,torusEquiv,torusLinear,torusWeights]
  map_mul' p q := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    ext i; fin_cases i <;>
      simp [torus,torusEquiv,torusLinear,torusWeights,mul_comm,mul_left_comm,mul_assoc]

theorem torusHom_injective : Function.Injective (torusHom (K := K)) := by
  intro p q h
  have hl := congrArg (fun g : Model K => g.val (basisVector 0) 0) h
  have hm := congrArg (fun g : Model K => g.val (basisVector 1) 1) h
  apply Prod.ext
  · apply Units.ext
    simpa [torusHom,torus,torusEquiv,torusLinear,torusWeights,basisVector] using hl
  · apply Units.ext
    simpa [torusHom,torus,torusEquiv,torusLinear,torusWeights,basisVector] using hm

def splitTorus : Subgroup (Model K) := torusHom.range

noncomputable def torusParameterEquiv : (Kˣ × Kˣ) ≃* splitTorus (K := K) :=
  MulEquiv.ofBijective (torusHom.rangeRestrict) ⟨
    fun _ _ h => torusHom_injective (congrArg Subtype.val h), torusHom.rangeRestrict_surjective⟩

theorem card_splitTorus [Finite K] : Nat.card (splitTorus (K := K)) = (Nat.card K-1)^2 := by
  rw [← Nat.card_congr torusParameterEquiv.toEquiv,Nat.card_prod]
  rw [Nat.card_units]
  ring
end Atlas.G2

