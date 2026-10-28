module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.ParabolicCoordinates
public import Theory.Representation.BinaryOffender.Homogeneous.Basic

/-!
# The native Mathieu parabolic orbit

Four short words in the actual ATLAS generators preserve the native totally
singular six-space. Six images of the marked vector under these words have a
checked left inverse, so their binary span is the whole space. Consequently
the span of the full parabolic orbit of the marked line is exactly this space.

This is the orbit calculation for Aschbacher–Smith 14.4.12, printed pp.1011–1012.
All matrix identities are kernel checked. The original ATLAS data attribution
and conventions are retained by `ModuleGeometry.Native` and its imports.
-/

@[expose] public section
noncomputable section
open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu M22TripleCover M22TripleCover.Unitary
open M22TripleCover.Uniqueness.PointRestriction (fieldModule fieldTower)
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
namespace OrbitCertificates
local instance : Module F BinarySpace := fieldModule binaryRepresentation binaryRepresentation_faithful
local instance : IsScalarTower (ZMod 2) F BinarySpace := fieldTower binaryRepresentation binaryRepresentation_faithful

def generatorD : Group := ⟨unitD, unitD_mem_actionGroup⟩
def actor0 : Group := generatorD⁻¹ * outerInvolution * generatorD
theorem actor0_matrix : ((actor0 : Matrix12ˣ) : Matrix12) = fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639] := by
  change matrixDInv * matrixC * matrixD = _
  rw [show (matrixDInv) * matrixC = fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024] by decide +kernel]
  rw [show (fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024]) * matrixD = fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639] by decide +kernel]

def actor1 : Group := outerInvolution * generatorD⁻¹ * outerInvolution * generatorD * outerInvolution
theorem actor1_matrix : ((actor1 : Matrix12ˣ) : Matrix12) = fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907] := by
  change matrixC * matrixDInv * matrixC * matrixD * matrixC = _
  rw [show (matrixC) * matrixDInv = fromRows ![8, 31, 22, 938, 2666, 2, 4, 202, 3356, 32, 64, 1412] by decide +kernel]
  rw [show (fromRows ![8, 31, 22, 938, 2666, 2, 4, 202, 3356, 32, 64, 1412]) * matrixC = fromRows ![32, 100, 70, 1705, 3524, 1, 7, 561, 2074, 8, 16, 1799] by decide +kernel]
  rw [show (fromRows ![32, 100, 70, 1705, 3524, 1, 7, 561, 2074, 8, 16, 1799]) * matrixD = fromRows ![128, 400, 280, 3659, 1559, 4, 28, 2875, 2687, 2, 31, 1499] by decide +kernel]
  rw [show (fromRows ![128, 400, 280, 3659, 1559, 4, 28, 2875, 2687, 2, 31, 1499]) * matrixC = fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907] by decide +kernel]

def actor2 : Group := outerInvolution * generatorD⁻¹ * generatorD⁻¹ * outerInvolution
theorem actor2_matrix : ((actor2 : Matrix12ˣ) : Matrix12) = fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048] := by
  change matrixC * matrixDInv * matrixDInv * matrixC = _
  rw [show (matrixC) * matrixDInv = fromRows ![8, 31, 22, 938, 2666, 2, 4, 202, 3356, 32, 64, 1412] by decide +kernel]
  rw [show (fromRows ![8, 31, 22, 938, 2666, 2, 4, 202, 3356, 32, 64, 1412]) * matrixDInv = fromRows ![2, 16, 13, 778, 2048, 8, 1, 2624, 3163, 938, 2666, 3453] by decide +kernel]
  rw [show (fromRows ![2, 16, 13, 778, 2048, 8, 1, 2624, 3163, 938, 2666, 3453]) * matrixC = fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048] by decide +kernel]

def actor3 : Group := generatorD * outerInvolution * generatorD * outerInvolution * generatorD⁻¹ * outerInvolution * generatorD⁻¹
theorem actor3_matrix : ((actor3 : Matrix12ˣ) : Matrix12) = fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561] := by
  change matrixD * matrixC * matrixD * matrixC * matrixDInv * matrixC * matrixDInv = _
  rw [show (matrixD) * matrixC = fromRows ![7, 32, 64, 1, 100, 512, 1024, 1185, 3453, 3061, 412, 3524] by decide +kernel]
  rw [show (fromRows ![7, 32, 64, 1, 100, 512, 1024, 1185, 3453, 3061, 412, 3524]) * matrixD = fromRows ![28, 128, 256, 4, 400, 2976, 1639, 1513, 1412, 2891, 2823, 1559] by decide +kernel]
  rw [show (fromRows ![28, 128, 256, 4, 400, 2976, 1639, 1513, 1412, 2891, 2823, 1559]) * matrixC = fromRows ![103, 512, 1024, 7, 1600, 3061, 412, 1850, 1799, 2510, 2553, 452] by decide +kernel]
  rw [show (fromRows ![103, 512, 1024, 7, 1600, 3061, 412, 1850, 1799, 2510, 2553, 452]) * matrixDInv = fromRows ![2518, 202, 3356, 22, 1980, 2160, 103, 3634, 3456, 2817, 2233, 2571] by decide +kernel]
  rw [show (fromRows ![2518, 202, 3356, 22, 1980, 2160, 103, 3634, 3456, 2817, 2233, 2571]) * matrixC = fromRows ![2859, 561, 2074, 70, 2031, 3365, 28, 3252, 2685, 2559, 3863, 3550] by decide +kernel]
  rw [show (fromRows ![2859, 561, 2074, 70, 2031, 3365, 28, 3252, 2685, 2559, 3863, 3550]) * matrixDInv = fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561] by decide +kernel]

def packed (n : ℕ) : BinarySpace := fun i => if n.testBit i.val then 1 else 0
def orbitColumns : Fin 6 → BinarySpace := fun j => packed (![1327, 3725, 1133, 2907, 3916, 1668] j)
def orbitMatrix : Matrix (Fin 12) (Fin 6) (ZMod 2) := fun i j => orbitColumns j i
def orbitDecoder : Matrix (Fin 6) (Fin 12) (ZMod 2) := fun i j => if (![18, 49, 50, 16, 9, 28] i).testBit j.val then 1 else 0
theorem orbit_decode : orbitDecoder * orbitMatrix = 1 := by decide +kernel
theorem orbit_columns_mem : ∀ j, orbitColumns j ∈ parabolicSpace := by
  intro j
  let u := parabolicDecoder *ᵥ coordinateMap (orbitColumns j)
  refine ⟨u, ?_⟩
  apply coordinates.injective
  rw [coordinates_parabolicEmbedding]
  have h : ∀ j, parabolicMatrix *ᵥ (parabolicDecoder *ᵥ coordinateMap (orbitColumns j)) =
      coordinateMap (orbitColumns j) := by decide +kernel
  exact h j

def orbitEmbedding : (Fin 6 → ZMod 2) →ₗ[ZMod 2] BinarySpace := orbitMatrix.mulVecLin

theorem orbitEmbedding_injective : Function.Injective orbitEmbedding := by
  intro u v h
  have hh := congrArg (fun w => orbitDecoder *ᵥ w) h
  change orbitDecoder *ᵥ (orbitMatrix *ᵥ u) = orbitDecoder *ᵥ (orbitMatrix *ᵥ v) at hh
  simpa only [mulVec_mulVec, orbit_decode, one_mulVec] using hh

theorem orbit_range_le : orbitEmbedding.range ≤ parabolicSpace := by
  rintro v ⟨u, rfl⟩
  have he : orbitEmbedding u = ∑ j, u j • orbitColumns j := by
    ext i
    simp [orbitEmbedding, Matrix.mulVec, dotProduct, orbitMatrix, mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun j _ => parabolicSpace.smul_mem _ (orbit_columns_mem j)

theorem orbit_range_eq : orbitEmbedding.range = parabolicSpace := by
  apply Submodule.eq_of_le_of_finrank_eq orbit_range_le
  rw [LinearMap.finrank_range_of_inj orbitEmbedding_injective, parabolicSpace_finrank]
  simp
def actionMatrix0 : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun i j => if (![2, 1, 16, 32, 4, 8] i).testBit j.val then 1 else 0
theorem actor0_intertwines : (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) * orbitMatrix = orbitMatrix * actionMatrix0 := by decide +kernel
theorem actor0_mem : actor0 ∈ parabolic := by
  have hstable : ∀ v ∈ parabolicSpace, representation actor0 v ∈ parabolicSpace := by
    intro v hv
    rw [← orbit_range_eq] at hv ⊢
    obtain ⟨u, rfl⟩ := hv
    refine ⟨actionMatrix0 *ᵥ u, ?_⟩
    change orbitMatrix *ᵥ (actionMatrix0 *ᵥ u) =
      ((actor0 : Matrix12ˣ) : Matrix12) *ᵥ (orbitMatrix *ᵥ u)
    rw [actor0_matrix, mulVec_mulVec, mulVec_mulVec, actor0_intertwines]
  have hinj : Function.Injective (representation actor0) := by
    intro u v h
    have hh := congrArg (representation actor0⁻¹) h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hh
  intro v
  constructor
  · intro hv
    have hr : (parabolicSpace.map (representation actor0)) = parabolicSpace := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨v, hv, rfl⟩; exact hstable v hv
      · exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    have : representation actor0 v ∈ parabolicSpace.map (representation actor0) := by rwa [hr]
    obtain ⟨u, hu, he⟩ := this
    exact hinj he ▸ hu
  · exact hstable v
def actionMatrix1 : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun i j => if (![1, 27, 48, 16, 8, 12] i).testBit j.val then 1 else 0
theorem actor1_intertwines : (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) * orbitMatrix = orbitMatrix * actionMatrix1 := by decide +kernel
theorem actor1_mem : actor1 ∈ parabolic := by
  have hstable : ∀ v ∈ parabolicSpace, representation actor1 v ∈ parabolicSpace := by
    intro v hv
    rw [← orbit_range_eq] at hv ⊢
    obtain ⟨u, rfl⟩ := hv
    refine ⟨actionMatrix1 *ᵥ u, ?_⟩
    change orbitMatrix *ᵥ (actionMatrix1 *ᵥ u) =
      ((actor1 : Matrix12ˣ) : Matrix12) *ᵥ (orbitMatrix *ᵥ u)
    rw [actor1_matrix, mulVec_mulVec, mulVec_mulVec, actor1_intertwines]
  have hinj : Function.Injective (representation actor1) := by
    intro u v h
    have hh := congrArg (representation actor1⁻¹) h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hh
  intro v
  constructor
  · intro hv
    have hr : (parabolicSpace.map (representation actor1)) = parabolicSpace := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨v, hv, rfl⟩; exact hstable v hv
      · exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    have : representation actor1 v ∈ parabolicSpace.map (representation actor1) := by rwa [hr]
    obtain ⟨u, hu, he⟩ := this
    exact hinj he ▸ hu
  · exact hstable v
def actionMatrix2 : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun i j => if (![30, 8, 27, 2, 16, 32] i).testBit j.val then 1 else 0
theorem actor2_intertwines : (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) * orbitMatrix = orbitMatrix * actionMatrix2 := by decide +kernel
theorem actor2_mem : actor2 ∈ parabolic := by
  have hstable : ∀ v ∈ parabolicSpace, representation actor2 v ∈ parabolicSpace := by
    intro v hv
    rw [← orbit_range_eq] at hv ⊢
    obtain ⟨u, rfl⟩ := hv
    refine ⟨actionMatrix2 *ᵥ u, ?_⟩
    change orbitMatrix *ᵥ (actionMatrix2 *ᵥ u) =
      ((actor2 : Matrix12ˣ) : Matrix12) *ᵥ (orbitMatrix *ᵥ u)
    rw [actor2_matrix, mulVec_mulVec, mulVec_mulVec, actor2_intertwines]
  have hinj : Function.Injective (representation actor2) := by
    intro u v h
    have hh := congrArg (representation actor2⁻¹) h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hh
  intro v
  constructor
  · intro hv
    have hr : (parabolicSpace.map (representation actor2)) = parabolicSpace := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨v, hv, rfl⟩; exact hstable v hv
      · exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    have : representation actor2 v ∈ parabolicSpace.map (representation actor2) := by rwa [hr]
    obtain ⟨u, hu, he⟩ := this
    exact hinj he ▸ hu
  · exact hstable v
def actionMatrix3 : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun i j => if (![12, 2, 38, 39, 48, 32] i).testBit j.val then 1 else 0
theorem actor3_intertwines : (fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561]) * orbitMatrix = orbitMatrix * actionMatrix3 := by decide +kernel
theorem actor3_mem : actor3 ∈ parabolic := by
  have hstable : ∀ v ∈ parabolicSpace, representation actor3 v ∈ parabolicSpace := by
    intro v hv
    rw [← orbit_range_eq] at hv ⊢
    obtain ⟨u, rfl⟩ := hv
    refine ⟨actionMatrix3 *ᵥ u, ?_⟩
    change orbitMatrix *ᵥ (actionMatrix3 *ᵥ u) =
      ((actor3 : Matrix12ˣ) : Matrix12) *ᵥ (orbitMatrix *ᵥ u)
    rw [actor3_matrix, mulVec_mulVec, mulVec_mulVec, actor3_intertwines]
  have hinj : Function.Injective (representation actor3) := by
    intro u v h
    have hh := congrArg (representation actor3⁻¹) h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hh
  intro v
  constructor
  · intro hv
    have hr : (parabolicSpace.map (representation actor3)) = parabolicSpace := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨v, hv, rfl⟩; exact hstable v hv
      · exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    have : representation actor3 v ∈ parabolicSpace.map (representation actor3) := by rwa [hr]
    obtain ⟨u, hu, he⟩ := this
    exact hinj he ▸ hu
  · exact hstable v
def orbitWord : Fin 6 → Group := ![1, actor0, actor2, actor3, actor0 * actor2, actor1 * actor2]

theorem orbitWord_mem : ∀ j, orbitWord j ∈ parabolic := by
  intro j
  fin_cases j
  · exact parabolic.one_mem
  · exact actor0_mem
  · exact actor2_mem
  · exact actor3_mem
  · exact parabolic.mul_mem actor0_mem actor2_mem
  · exact parabolic.mul_mem actor1_mem actor2_mem

theorem orbitWord_apply : ∀ j, representation (orbitWord j) markedVector = orbitColumns j := by
  intro j
  fin_cases j
  · exact LinearMap.congr_fun representation.map_one markedVector
  · change (((actor0 : Matrix12ˣ) : Matrix12) *ᵥ markedVector) = _
    rw [actor0_matrix]
    decide +kernel
  · change (((actor2 : Matrix12ˣ) : Matrix12) *ᵥ markedVector) = _
    rw [actor2_matrix]
    decide +kernel
  · change (((actor3 : Matrix12ˣ) : Matrix12) *ᵥ markedVector) = _
    rw [actor3_matrix]
    decide +kernel
  · change representation (actor0 * actor2) markedVector = _
    rw [map_mul, Module.End.mul_apply]
    change (((actor0 : Matrix12ˣ) : Matrix12) *ᵥ
      (((actor2 : Matrix12ˣ) : Matrix12) *ᵥ markedVector)) = _
    rw [actor0_matrix, actor2_matrix]
    decide +kernel
  · change representation (actor1 * actor2) markedVector = _
    rw [map_mul, Module.End.mul_apply]
    change (((actor1 : Matrix12ˣ) : Matrix12) *ᵥ
      (((actor2 : Matrix12ˣ) : Matrix12) *ᵥ markedVector)) = _
    rw [actor1_matrix, actor2_matrix]
    decide +kernel

end OrbitCertificates
open OrbitCertificates

/-- The literal parabolic orbit of the Sylow-marked line generates the native six-space. -/
theorem parabolicSpace_eq_orbitSpan :
    parabolicSpace = Homogeneous.orbitSpan representation parabolic (binaryLine markedVector) := by
  apply le_antisymm
  · rw [← orbit_range_eq]
    rintro _ ⟨u, rfl⟩
    have he : orbitEmbedding u = ∑ j, u j • orbitColumns j := by
      ext i
      simp [orbitEmbedding, Matrix.mulVec, dotProduct, orbitMatrix, mul_comm]
    rw [he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [← orbitWord_apply j]
    exact (le_iSup (fun g : parabolic => (binaryLine markedVector).map (representation g))
      ⟨orbitWord j, orbitWord_mem j⟩) ⟨markedVector, Submodule.mem_span_singleton_self _, rfl⟩
  · exact Homogeneous.orbitSpan_le representation
      ((binaryLine_le_point _).trans markedPoint_le_parabolic) le_rfl

/-- The same six certified words give the source orbit span for any actual
    remaining two-local subgroup containing them. In particular, an actor
    catalogue can instantiate `D` with the literal subgroup generated by
    `TX₂` and `X₃` without replacing that position by the ambient parabolic. -/
theorem parabolicSpace_eq_orbitSpan_of_subgroup
    (D : Subgroup Group) (hD : D ≤ parabolic)
    (hwords : ∀ j, orbitWord j ∈ D) :
    parabolicSpace = Homogeneous.orbitSpan representation D (binaryLine markedVector) := by
  apply le_antisymm
  · rw [← orbit_range_eq]
    rintro _ ⟨u, rfl⟩
    have he : orbitEmbedding u = ∑ j, u j • orbitColumns j := by
      ext i
      simp [orbitEmbedding, Matrix.mulVec, dotProduct, orbitMatrix, mul_comm]
    rw [he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [← orbitWord_apply j]
    exact (le_iSup (fun g : D => (binaryLine markedVector).map (representation g))
      ⟨orbitWord j, hwords j⟩) ⟨markedVector, Submodule.mem_span_singleton_self _, rfl⟩
  · change Homogeneous.orbitSpan representation D (binaryLine markedVector) ≤ parabolicSpace
    apply Homogeneous.orbitSpan_le representation
    · exact (binaryLine_le_point _).trans markedPoint_le_parabolic
    · exact hD

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
