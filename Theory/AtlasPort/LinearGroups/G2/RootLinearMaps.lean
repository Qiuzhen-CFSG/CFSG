module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/RootLinearMaps.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.Algebra.SplitOctonion.BasisChecks

/-! The six root families preserve split-octonion multiplication by coordinate polynomial identities. -/

@[expose] public section

namespace Atlas.G2.Explicit
open Atlas.SplitOctonion
variable {K : Type*} [CommRing K]
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Wilson root A in the fixed split coordinate basis. -/
def rootAApply (a : K) (x : Carrier K) : Carrier K :=
  ![x 0 - a*x 6,x 1+a*x 7,x 2,x 3,x 4,x 5,x 6,x 7]

def rootALinear (a : K) : Carrier K →ₗ[K] Carrier K where
  toFun := rootAApply a
  map_add' x y := by ext i; fin_cases i <;> simp [rootAApply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [rootAApply] <;> ring

theorem rootA_add (a b : K) (x : Carrier K) :
    rootAApply a (rootAApply b x) = rootAApply (a+b) x := by
  ext i; fin_cases i <;> simp [rootAApply] <;> ring

def rootAEquiv (a : K) : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := rootALinear a
  invFun := rootAApply (-a)
  left_inv x := by ext i; fin_cases i <;> simp [rootALinear,rootAApply]
  right_inv x := by ext i; fin_cases i <;> simp [rootALinear,rootAApply]

theorem rootA_mul (a : K) (x y : Carrier K) :
    rootAEquiv a (mul x y) = mul (rootAEquiv a x) (rootAEquiv a y) := by
  have h : ∀ u v : Carrier K, rootALinear a (mul u v) =
      mul (rootALinear a u) (rootALinear a v) := by
    intro u v
    ext k; fin_cases k <;> simp [rootALinear,rootAApply,mul] <;> ring
  exact map_mul_of_basis (rootALinear a) (fun i j => h (basisVector i) (basisVector j)) x y

/-- Wilson root B in the fixed split coordinate basis. -/
def rootBApply (a : K) (x : Carrier K) : Carrier K :=
  ![x 0 - a*x 5,x 1,x 2+a*x 7,x 3,x 4,x 5,x 6,x 7]

def rootBLinear (a : K) : Carrier K →ₗ[K] Carrier K where
  toFun := rootBApply a
  map_add' x y := by ext i; fin_cases i <;> simp [rootBApply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [rootBApply] <;> ring

theorem rootB_add (a b : K) (x : Carrier K) :
    rootBApply a (rootBApply b x) = rootBApply (a+b) x := by
  ext i; fin_cases i <;> simp [rootBApply] <;> ring

def rootBEquiv (a : K) : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := rootBLinear a
  invFun := rootBApply (-a)
  left_inv x := by ext i; fin_cases i <;> simp [rootBLinear,rootBApply]
  right_inv x := by ext i; fin_cases i <;> simp [rootBLinear,rootBApply]

theorem rootB_mul (a : K) (x y : Carrier K) :
    rootBEquiv a (mul x y) = mul (rootBEquiv a x) (rootBEquiv a y) := by
  have h : ∀ u v : Carrier K, rootBLinear a (mul u v) =
      mul (rootBLinear a u) (rootBLinear a v) := by
    intro u v
    ext k; fin_cases k <;> simp [rootBLinear,rootBApply,mul] <;> ring
  exact map_mul_of_basis (rootBLinear a) (fun i j => h (basisVector i) (basisVector j)) x y

/-- Wilson root C in the fixed split coordinate basis. -/
def rootCApply (a : K) (x : Carrier K) : Carrier K :=
  ![x 0-a*x 3+a*x 4+a^2*x 7,x 1-a*x 5,x 2+a*x 6,x 3-a*x 7,x 4+a*x 7,x 5,x 6,x 7]

def rootCLinear (a : K) : Carrier K →ₗ[K] Carrier K where
  toFun := rootCApply a
  map_add' x y := by ext i; fin_cases i <;> simp [rootCApply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [rootCApply] <;> ring

theorem rootC_add (a b : K) (x : Carrier K) :
    rootCApply a (rootCApply b x) = rootCApply (a+b) x := by
  ext i; fin_cases i <;> simp [rootCApply] <;> ring

def rootCEquiv (a : K) : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := rootCLinear a
  invFun := rootCApply (-a)
  left_inv x := by ext i; fin_cases i <;> simp [rootCLinear,rootCApply]; ring
  right_inv x := by ext i; fin_cases i <;> simp [rootCLinear,rootCApply]; ring

theorem rootC_mul (a : K) (x y : Carrier K) :
    rootCEquiv a (mul x y) = mul (rootCEquiv a x) (rootCEquiv a y) := by
  have h : ∀ u v : Carrier K, rootCLinear a (mul u v) =
      mul (rootCLinear a u) (rootCLinear a v) := by
    intro u v
    ext k; fin_cases k <;> simp [rootCLinear,rootCApply,mul] <;> ring
  exact map_mul_of_basis (rootCLinear a) (fun i j => h (basisVector i) (basisVector j)) x y

/-- Wilson root D in the fixed split coordinate basis. -/
def rootDApply (a : K) (x : Carrier K) : Carrier K :=
  ![x 0-a*x 2,x 1-a*x 3+a*x 4+a^2*x 6,x 2,x 3-a*x 6,x 4+a*x 6,x 5+a*x 7,x 6,x 7]

def rootDLinear (a : K) : Carrier K →ₗ[K] Carrier K where
  toFun := rootDApply a
  map_add' x y := by ext i; fin_cases i <;> simp [rootDApply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [rootDApply] <;> ring

theorem rootD_add (a b : K) (x : Carrier K) :
    rootDApply a (rootDApply b x) = rootDApply (a+b) x := by
  ext i; fin_cases i <;> simp [rootDApply] <;> ring

def rootDEquiv (a : K) : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := rootDLinear a
  invFun := rootDApply (-a)
  left_inv x := by ext i; fin_cases i <;> simp [rootDLinear,rootDApply]; ring
  right_inv x := by ext i; fin_cases i <;> simp [rootDLinear,rootDApply]; ring

theorem rootD_mul (a : K) (x y : Carrier K) :
    rootDEquiv a (mul x y) = mul (rootDEquiv a x) (rootDEquiv a y) := by
  have h : ∀ u v : Carrier K, rootDLinear a (mul u v) =
      mul (rootDLinear a u) (rootDLinear a v) := by
    intro u v
    ext k; fin_cases k <;> simp [rootDLinear,rootDApply,mul] <;> ring
  exact map_mul_of_basis (rootDLinear a) (fun i j => h (basisVector i) (basisVector j)) x y

/-- Wilson root E in the fixed split coordinate basis. -/
def rootEApply (a : K) (x : Carrier K) : Carrier K :=
  ![x 0,x 1-a*x 2,x 2,x 3,x 4,x 5+a*x 6,x 6,x 7]

def rootELinear (a : K) : Carrier K →ₗ[K] Carrier K where
  toFun := rootEApply a
  map_add' x y := by ext i; fin_cases i <;> simp [rootEApply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [rootEApply] <;> ring

theorem rootE_add (a b : K) (x : Carrier K) :
    rootEApply a (rootEApply b x) = rootEApply (a+b) x := by
  ext i; fin_cases i <;> simp [rootEApply] <;> ring

def rootEEquiv (a : K) : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := rootELinear a
  invFun := rootEApply (-a)
  left_inv x := by ext i; fin_cases i <;> simp [rootELinear,rootEApply]
  right_inv x := by ext i; fin_cases i <;> simp [rootELinear,rootEApply]

theorem rootE_mul (a : K) (x y : Carrier K) :
    rootEEquiv a (mul x y) = mul (rootEEquiv a x) (rootEEquiv a y) := by
  have h : ∀ u v : Carrier K, rootELinear a (mul u v) =
      mul (rootELinear a u) (rootELinear a v) := by
    intro u v
    ext k; fin_cases k <;> simp [rootELinear,rootEApply,mul] <;> ring
  exact map_mul_of_basis (rootELinear a) (fun i j => h (basisVector i) (basisVector j)) x y

/-- Wilson root F in the fixed split coordinate basis. -/
def rootFApply (a : K) (x : Carrier K) : Carrier K :=
  ![x 0-a*x 1,x 1,x 2+a*x 3-a*x 4+a^2*x 5,x 3+a*x 5,x 4-a*x 5,x 5,x 6+a*x 7,x 7]

def rootFLinear (a : K) : Carrier K →ₗ[K] Carrier K where
  toFun := rootFApply a
  map_add' x y := by ext i; fin_cases i <;> simp [rootFApply] <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp [rootFApply] <;> ring

theorem rootF_add (a b : K) (x : Carrier K) :
    rootFApply a (rootFApply b x) = rootFApply (a+b) x := by
  ext i; fin_cases i <;> simp [rootFApply] <;> ring

def rootFEquiv (a : K) : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := rootFLinear a
  invFun := rootFApply (-a)
  left_inv x := by ext i; fin_cases i <;> simp [rootFLinear,rootFApply]; ring
  right_inv x := by ext i; fin_cases i <;> simp [rootFLinear,rootFApply]; ring

theorem rootF_mul (a : K) (x y : Carrier K) :
    rootFEquiv a (mul x y) = mul (rootFEquiv a x) (rootFEquiv a y) := by
  have h : ∀ u v : Carrier K, rootFLinear a (mul u v) =
      mul (rootFLinear a u) (rootFLinear a v) := by
    intro u v
    ext k; fin_cases k <;> simp [rootFLinear,rootFApply,mul] <;> ring
  exact map_mul_of_basis (rootFLinear a) (fun i j => h (basisVector i) (basisVector j)) x y
end Atlas.G2.Explicit
