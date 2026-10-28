module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.Interface
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.NativeMap.Witnesses

/-!
# A nonzero native comparison for the degree-44 matrix certificate

Each saved column is the indicated wedge combination of the first eleven native
Golay rows modulo the constant line. Its coordinatewise contraction is zero,
so the resulting linear map takes values in the literal contraction kernel.
The checked row and exterior tables prove the two generator identities.

The quotient functionals given by a pivot coordinate plus the last pivot
coordinate descend through the constant line. Their determinant evaluates the
first column to one, proving that the comparison map is nonzero. No basis,
irreducibility, or generation premise is used.

Source context: James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), pp.57–111; GM02 Proposition 5.1, manuscript p.17.
The preserved native witnesses are in `KernelAbsolute/source/`.
-/

@[expose] public section
open scoped BigOperators
open Sporadic.Mathieu MathieuCode Representation
open Representation.MathieuM24Degree44.FiveSpace
noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.NativeMap
open CoordinateExterior

def rawRow (i : I) : golay := ⟨row i.castSucc, row_mem _⟩
def codeRow (i : I) : Code := codeLine.mkQ (rawRow i)

theorem constant_quotient_zero :
    codeLine.mkQ ⟨BinaryPermutation.allOne (Fin 24), allOne_mem⟩ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero codeLine).mpr
  exact Submodule.subset_span (Set.mem_singleton _)

theorem codeRow_action (j : Fin 2) (i : I) :
    codeRepresentation (nativeGenerator j) (codeRow i) =
      codeLift codeRow (Witnesses.codeColumn j i) := by
  have h : golayRepresentation (nativeGenerator j) (rawRow i) =
      (∑ a : I, Witnesses.codeColumn j i a • rawRow a) +
      Witnesses.actionDelta j i • ⟨BinaryPermutation.allOne (Fin 24), allOne_mem⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]
    change fullRepresentation (nativeGenerator j) (row i.castSucc) =
      (∑ a : I, Witnesses.codeColumn j i a • row a.castSucc) +
      Witnesses.actionDelta j i • BinaryPermutation.allOne (Fin 24)
    exact Witnesses.row_action_cert j i
  rw [codeRow, codeRepresentation_mk, h, map_add, map_smul,
    constant_quotient_zero, smul_zero, add_zero, map_sum]
  simp only [map_smul]
  rfl

theorem contraction_wedge_rows (i j : I) :
    contractionLinear (wedge (codeRow i) (codeRow j)) =
      codeInCore.mkQ (productCore (rawRow i) (rawRow j)) := by
  change contractionLinear (exteriorPower.ιMulti F 2 ![codeRow i, codeRow j]) = _
  rw [contractionLinear, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem contraction_lift (t : T) :
    contractionLinear (lift codeRow t) =
      codeInCore.mkQ (∑ p : P, t p • productCore (rawRow p.1) (rawRow p.2)) := by
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    contraction_wedge_rows]

theorem candidate_mem (k : Fin 44) :
    lift codeRow (Witnesses.coeff k) ∈ kernel.toSubmodule := by
  change contractionLinear (lift codeRow (Witnesses.coeff k)) = 0
  rw [contraction_lift]
  have h : (∑ p : P, Witnesses.coeff k p • productCore (rawRow p.1) (rawRow p.2)) = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero]
    funext q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact congrFun (Witnesses.contraction_cert k) q
  rw [h, map_zero]

def ambientMap : Data.Space →ₗ[F] Ext Code :=
  (lift codeRow).comp (combine Witnesses.coeff)

theorem ambientMap_mem (v : Data.Space) : ambientMap v ∈ kernel.toSubmodule := by
  change lift codeRow (∑ k, v k • Witnesses.coeff k) ∈ kernel.toSubmodule
  rw [map_sum]
  apply kernel.toSubmodule.sum_mem
  intro k _
  rw [map_smul]
  exact kernel.toSubmodule.smul_mem (v k) (candidate_mem k)

/-- The saved binary coordinates mapped into the actual Golay exterior kernel. -/
def comparisonMap : Data.Space →ₗ[ZMod 2] Kernel :=
  ambientMap.codRestrict kernel.toSubmodule ambientMap_mem

def rawCoord (i : I) : golay →ₗ[F] F where
  toFun v := v.val (pivot i.castSucc) + v.val (pivot 11)
  map_add' v w := by dsimp; ring
  map_smul' c v := by dsimp; ring

theorem rawCoord_line (i : I) : codeLine ≤ (rawCoord i).ker := by
  intro v hv
  change v.val ∈ BinaryPermutation.constants (Fin 24) at hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  change v.val (pivot i.castSucc) + v.val (pivot 11) = 0
  rw [← hc]
  change c * 1 + c * 1 = 0
  simp [CharTwo.add_self_eq_zero]

def codeCoord (i : I) : Code →ₗ[F] F := codeLine.liftQ (rawCoord i) (rawCoord_line i)

theorem codeCoord_row (i j : I) : codeCoord i (codeRow j) = if j = i then 1 else 0 := by
  change row j.castSucc (pivot i.castSucc) + row j.castSucc (pivot 11) = _
  have hn : j.castSucc ≠ (11 : Fin 12) := Fin.ne_of_lt j.castSucc_lt_last
  simp [row_pivot, hn]

def separator : Ext Code →ₗ[F] F :=
  exteriorPower.pairingDual F Code 2 (exteriorPower.ιMulti F 2 ![codeCoord 0, codeCoord 1])

theorem separator_wedge_rows (i j : I) :
    separator (wedge (codeRow i) (codeRow j)) =
      (if i = 0 then 1 else 0) * (if j = 1 then 1 else 0) -
      (if i = 1 then 1 else 0) * (if j = 0 then 1 else 0) := by
  change exteriorPower.pairingDual F Code 2 (exteriorPower.ιMulti F 2 _)
    (exteriorPower.ιMulti F 2 _) = _
  rw [exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp [codeCoord_row]

theorem separator_lift (t : T) : separator (lift codeRow t) = t (0,1) - t (1,0) := by
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    separator_wedge_rows, smul_eq_mul, Fintype.sum_prod_type]
  simp [mul_sub, Finset.sum_sub_distrib, mul_ite]

/-- The pivot determinant detects the first saved column. -/
theorem comparisonMap_ne_zero : comparisonMap ≠ 0 := by
  intro h
  have hz := congrArg (fun f : Data.Space →ₗ[F] Kernel =>
    separator (f (Pi.single 0 1)).val) h
  simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, map_zero] at hz
  change separator (ambientMap (Pi.single 0 1)) = 0 at hz
  change separator (lift codeRow (combine Witnesses.coeff (Pi.single 0 1))) = 0 at hz
  rw [combine_single, one_smul, separator_lift] at hz
  have hc : Witnesses.coeff 0 (0,1) - Witnesses.coeff 0 (1,0) = 1 := by decide +kernel
  rw [hc] at hz
  exact one_ne_zero hz

theorem coordinate_action (j : Fin 2) :
    (coordsAction (Witnesses.codeColumn j)).comp (combine Witnesses.coeff) =
      (combine Witnesses.coeff).comp (Data.matrix j).mulVecLin := by
  apply (Pi.basisFun F (Fin 44)).ext
  intro k
  simp only [Pi.basisFun_apply, LinearMap.comp_apply, combine_single, one_smul,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact Witnesses.action_cert j k

/-- The exact native generators act by the saved column-vector matrices. -/
theorem comparisonMap_action (j : Fin 2) (v : Data.Space) :
    comparisonMap ((Data.matrix j).mulVec v) =
      kernelRepresentation (nativeGenerator j) (comparisonMap v) := by
  apply Subtype.ext
  change lift codeRow (combine Witnesses.coeff ((Data.matrix j).mulVec v)) =
    exteriorPower.map 2 (codeRepresentation (nativeGenerator j))
      (lift codeRow (combine Witnesses.coeff v))
  rw [lift_action codeRow _ _ (codeRow_action j)]
  exact congrArg (lift codeRow) (LinearMap.congr_fun (coordinate_action j) v).symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.NativeMap
