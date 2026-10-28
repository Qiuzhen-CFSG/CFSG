/-
The Golay basis and marked Leech coordinates are those of Gerald Höhn,
ATLAS revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
See LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.MatrixData

/-! Rational automorphisms associated with the two McLaughlin matrix witnesses.
Integer inverse identities are checked before transporting the matrices to the
rational Leech coordinate space. Lattice preservation and the marked point action
are separate obligations. -/

@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
open Atlas.Codes Atlas.Lattices
open scoped Matrix BigOperators
set_option maxRecDepth 100000
def linearAData : (Fin 24 → ℚ) →ₗ[ℚ] (Fin 24 → ℚ) := Matrix.toLin' matrixA
def linearAInvData : (Fin 24 → ℚ) →ₗ[ℚ] (Fin 24 → ℚ) := Matrix.toLin' matrixAInv
def linearBData : (Fin 24 → ℚ) →ₗ[ℚ] (Fin 24 → ℚ) := Matrix.toLin' matrixB
def linearBInvData : (Fin 24 → ℚ) →ₗ[ℚ] (Fin 24 → ℚ) := Matrix.toLin' matrixBInv

theorem matrixA_int : matrixAData * matrixAInvData = (16 : ℤ) • 1 := by decide +kernel
theorem matrixA_int' : matrixAInvData * matrixAData = (16 : ℤ) • 1 := by decide +kernel
theorem matrixA_left : matrixA * matrixAInv = 1 := by
  rw [matrixA, matrixAInv, Matrix.smul_mul, Matrix.mul_smul]
  rw [matrixADataQ, matrixAInvDataQ, ← Matrix.map_mul]
  rw [matrixA_int]
  have hmap : ((16 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ)).map (Int.castRingHom ℚ) = (16 : ℚ) • (1 : Matrix (Fin 24) (Fin 24) ℚ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.map, h]
  rw [hmap]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]; norm_num
 theorem matrixA_right : matrixAInv * matrixA = 1 := by
  rw [matrixA, matrixAInv, Matrix.smul_mul, Matrix.mul_smul]
  rw [matrixADataQ, matrixAInvDataQ, ← Matrix.map_mul]
  rw [matrixA_int']
  have hmap : ((16 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ)).map (Int.castRingHom ℚ) = (16 : ℚ) • (1 : Matrix (Fin 24) (Fin 24) ℚ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.map, h]
  rw [hmap]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]; norm_num
theorem matrixB_int : matrixBData * matrixBInvData = (64 : ℤ) • 1 := by decide +kernel
theorem matrixB_int' : matrixBInvData * matrixBData = (64 : ℤ) • 1 := by decide +kernel
theorem matrixB_left : matrixB * matrixBInv = 1 := by
  rw [matrixB, matrixBInv, Matrix.smul_mul, Matrix.mul_smul]
  rw [matrixBDataQ, matrixBInvDataQ, ← Matrix.map_mul]
  rw [matrixB_int]
  have hmap : ((64 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ)).map (Int.castRingHom ℚ) = (64 : ℚ) • (1 : Matrix (Fin 24) (Fin 24) ℚ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.map, h]
  rw [hmap]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]; norm_num
 theorem matrixB_right : matrixBInv * matrixB = 1 := by
  rw [matrixB, matrixBInv, Matrix.smul_mul, Matrix.mul_smul]
  rw [matrixBDataQ, matrixBInvDataQ, ← Matrix.map_mul]
  rw [matrixB_int']
  have hmap : ((64 : ℤ) • (1 : Matrix (Fin 24) (Fin 24) ℤ)).map (Int.castRingHom ℚ) = (64 : ℚ) • (1 : Matrix (Fin 24) (Fin 24) ℚ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.map, h]
  rw [hmap]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]; norm_num

def mapAData : (Fin 24 → ℚ) ≃ₗ[ℚ] (Fin 24 → ℚ) :=
  LinearEquiv.ofLinearMap linearAData linearAInvData (by
    apply LinearMap.ext
    intro x
    funext i
    simp only [linearAData,linearAInvData,LinearMap.comp_apply,LinearMap.id_apply,
      Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec,matrixA_left]
    simp) (by
    apply LinearMap.ext
    intro x
    funext i
    simp only [linearAData,linearAInvData,LinearMap.comp_apply,LinearMap.id_apply,
      Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec,matrixA_right]
    simp)

def mapBData : (Fin 24 → ℚ) ≃ₗ[ℚ] (Fin 24 → ℚ) :=
  LinearEquiv.ofLinearMap linearBData linearBInvData (by
    apply LinearMap.ext
    intro x
    funext i
    simp only [linearBData,linearBInvData,LinearMap.comp_apply,LinearMap.id_apply,
      Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec,matrixB_left]
    simp) (by
    apply LinearMap.ext
    intro x
    funext i
    simp only [linearBData,linearBInvData,LinearMap.comp_apply,LinearMap.id_apply,
      Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec,matrixB_right]
    simp)

def mapA : RationalCoordinates ≃ₗ[ℚ] RationalCoordinates :=
  reindex.symm.trans (mapAData.trans reindex)
def mapB : RationalCoordinates ≃ₗ[ℚ] RationalCoordinates :=
  reindex.symm.trans (mapBData.trans reindex)



end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
