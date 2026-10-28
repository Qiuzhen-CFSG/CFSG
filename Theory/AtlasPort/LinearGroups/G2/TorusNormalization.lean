module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/TorusNormalization.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.Torus
public import Theory.AtlasPort.LinearGroups.G2.Unipotent

/-! The split torus normalizes each displayed root group by its explicit root character. -/

@[expose] public section

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {K : Type*} [Field K]
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem torus_rootA (l m : Kˣ) (a : K) :
    torus l m * rootA a * (torus l m)⁻¹ = rootA (((l : K)*(m : K))*a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i; fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,rootA,rootAEquiv,
      rootALinear,rootAApply] <;> field_simp

theorem torus_rootB (l m : Kˣ) (a : K) :
    torus l m * rootB a * (torus l m)⁻¹ = rootB (((l : K)^2/(m : K))*a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i; fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,rootB,rootBEquiv,
      rootBLinear,rootBApply] <;> field_simp

theorem torus_rootC (l m : Kˣ) (a : K) :
    torus l m * rootC a * (torus l m)⁻¹ = rootC (((l : K))*a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i; fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,rootC,rootCEquiv,
      rootCLinear,rootCApply] <;> field_simp

theorem torus_rootD (l m : Kˣ) (a : K) :
    torus l m * rootD a * (torus l m)⁻¹ = rootD (((m : K))*a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i; fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,rootD,rootDEquiv,
      rootDLinear,rootDApply] <;> field_simp

theorem torus_rootE (l m : Kˣ) (a : K) :
    torus l m * rootE a * (torus l m)⁻¹ = rootE (((m : K)^2/(l : K))*a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i; fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,rootE,rootEEquiv,
      rootELinear,rootEApply] <;> field_simp

theorem torus_rootF (l m : Kˣ) (a : K) :
    torus l m * rootF a * (torus l m)⁻¹ = rootF (((l : K)/(m : K))*a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i; fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,rootF,rootFEquiv,
      rootFLinear,rootFApply] <;> field_simp

def torusUnipotentParameters (l m : Kˣ) (t : Fin 6 → K) : Fin 6 → K :=
  ![(l:K)*(m:K)*t 0,(l:K)^2/(m:K)*t 1,(l:K)*t 2,(m:K)*t 3,
    (m:K)^2/(l:K)*t 4,(l:K)/(m:K)*t 5]

theorem torus_unipotentProduct (l m : Kˣ) (t : Fin 6 → K) :
    torus l m * unipotentProduct t * (torus l m)⁻¹ =
      unipotentProduct (torusUnipotentParameters l m t) := by
  change MulAut.conj (torus l m) (unipotentProduct t) = _
  simp only [unipotentProduct, map_mul, MulAut.conj_apply]
  rw [torus_rootA,torus_rootB,torus_rootC,torus_rootD,torus_rootE,torus_rootF]
  rfl
end Atlas.G2
