module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Data
public import Theory.Representation.MathieuCodeRestriction.Actions
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Native Golay code coordinates

The coefficient of the last Golay row is eliminated modulo the constant line.
The first eleven rows therefore give a basis of the literal quotient. Computing
at the certified pivot coordinates identifies the two native generator matrices.
This supplies the eleven-dimensional input to the trace-zero adjoint construction
of James's degree-120 module (J. Algebra 27 (1973), 57–111).
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
open MathieuCode Sporadic.Mathieu
open scoped BigOperators

abbrev CodeCoordinates := Fin 11 → ZMod 2

/-- Remove the final Golay coefficient, which represents the constant line. -/
def reduceCode : Full →ₗ[ZMod 2] CodeCoordinates where
  toFun v i := v (pivot i.castSucc) - v (pivot 11)
  map_add' v w := by ext i; simp; ring
  map_smul' c v := by ext i; simp [mul_sub]

lemma reduceCode_constant (c : ZMod 2) :
    reduceCode (c • BinaryPermutation.allOne (Fin 24)) = 0 := by
  ext i
  simp [reduceCode, BinaryPermutation.allOne]

lemma codeLine_le_reduceCode_ker : codeLine ≤ (reduceCode.comp golay.subtype).ker := by
  intro v hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  change reduceCode v.val = 0
  change c • BinaryPermutation.allOne (Fin 24) = v.val at hc
  rw [← hc, reduceCode_constant]

/-- Eleven pivot differences on the actual code quotient. -/
def codeCoordinates : Code →ₗ[ZMod 2] CodeCoordinates :=
  codeLine.liftQ (reduceCode.comp golay.subtype) codeLine_le_reduceCode_ker

lemma codeCoordinates_mk (v : golay) :
    codeCoordinates (codeLine.mkQ v) = reduceCode v.val := rfl

def codeRow (j : Fin 11) : golay := ⟨row j.castSucc, row_mem j.castSucc⟩

lemma reduceCode_row (j : Fin 11) : reduceCode (codeRow j).val = Pi.single j 1 := by
  ext i
  have hj : j.castSucc ≠ (11 : Fin 12) := Fin.ne_of_lt j.castSucc_lt_last
  simp [reduceCode, codeRow, row_pivot, Pi.single_apply, hj, eq_comm]

def codeSection : CodeCoordinates →ₗ[ZMod 2] Code :=
  ∑ j, (LinearMap.proj j).smulRight (codeLine.mkQ (codeRow j))

lemma codeSection_single (j : Fin 11) :
    codeSection (Pi.single j 1) = codeLine.mkQ (codeRow j) := by
  simp [codeSection, Pi.single_apply]

lemma pi_ext_one {n : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {f g : (Fin n → ZMod 2) →ₗ[ZMod 2] W}
    (h : ∀ j, f (Pi.single j 1) = g (Pi.single j 1)) : f = g := by
  apply LinearMap.pi_ext
  intro j c
  have he : Pi.single j c = c • (Pi.single j 1 : Fin n → ZMod 2) := by
    simp [← Pi.single_smul]
  rw [he, map_smul, map_smul, h]

lemma codeCoordinates_section : codeCoordinates.comp codeSection = LinearMap.id := by
  apply pi_ext_one
  intro j
  simp only [LinearMap.comp_apply, codeSection_single, codeCoordinates_mk,
    reduceCode_row, LinearMap.id_apply]

lemma codeCoordinates_surjective : Function.Surjective codeCoordinates := by
  intro v
  exact ⟨codeSection v, LinearMap.congr_fun codeCoordinates_section v⟩

/-- The source basis, with no arbitrary choice of eleven-dimensional model. -/
def codeEquiv : Code ≃ₗ[ZMod 2] CodeCoordinates :=
  LinearEquiv.ofBijective codeCoordinates ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_code]; simp [CodeCoordinates])).mpr codeCoordinates_surjective,
    codeCoordinates_surjective⟩

lemma codeEquiv_symm_single (j : Fin 11) :
    codeEquiv.symm (Pi.single j 1) = codeLine.mkQ (codeRow j) := by
  apply codeEquiv.injective
  simp only [LinearEquiv.apply_symm_apply]
  exact (reduceCode_row j).symm

/-- Golay rows 0 through 10 modulo the constant line. -/
def codeBasis : Module.Basis (Fin 11) (ZMod 2) Code := Module.Basis.ofEquivFun codeEquiv

lemma codeBasis_apply (j : Fin 11) : codeBasis j = codeLine.mkQ (codeRow j) := by
  simpa only [codeBasis, Module.Basis.coe_ofEquivFun] using codeEquiv_symm_single j

/-- The native code representation in the certified quotient coordinates. -/
def coordinateCodeRepresentation : Representation (ZMod 2) M24 CodeCoordinates :=
  codeEquiv.conjRingEquiv.toMonoidHom.comp codeRepresentation

lemma coordinateCodeRepresentation_single (g : M24) (j : Fin 11) :
    coordinateCodeRepresentation g (Pi.single j 1) =
      reduceCode (fullRepresentation g (row j.castSucc)) := by
  change codeEquiv (codeRepresentation g (codeEquiv.symm (Pi.single j 1))) = _
  rw [codeEquiv_symm_single, codeRepresentation_mk]
  rfl

/-- The literal two generator matrices, in column convention. -/
theorem coordinateCodeRepresentation_actor (a : Fin 2) :
    LinearMap.toMatrix' (coordinateCodeRepresentation (actor a)) = codeMatrix a := by
  ext i j
  rw [LinearMap.toMatrix'_apply, coordinateCodeRepresentation_single]
  change row j.castSucc ((actor a).val.symm (pivot i.castSucc)) -
    row j.castSucc ((actor a).val.symm (pivot 11)) = codeMatrix a i j
  dsimp only [codeMatrix, packedMatrix]
  revert a i j
  decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
