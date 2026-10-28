module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Coordinate comparison adapted from ATLAS, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Identification.Locals
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Mathlib.Algebra.Module.ZMod

/-!
# The exceptional images of the split binary pair

Every automorphism of the elementary abelian binary four-space is linear.
Its coordinate matrix has determinant one, so the genuine exterior-square /
deleted-module comparison gives a faithful map to A₈. The four given generators
have images (45)(67), (02)(67), (012), and (056)(247), respectively.

The certificates compare the six basis vectors of the split quadratic module.
They retain the correction by the final coordinate: permutation of an even word
is compared modulo the constant line, not as an equality of eight-coordinate
words. The resulting orthogonal-action equalities determine the permutation
images by faithfulness of the deleted module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 14.4.4,
printed p.1007. Coordinates and the exceptional comparison come from the
attributed ATLAS port in `Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8`.
-/

@[expose] public section
namespace BinaryFourSplitPair.JoinedIdentification
open BinaryFourSplitPair Matrix
open Atlas.Order20160A8
open scoped MatrixGroups

/-- An automorphism of the elementary abelian group is automatically binary linear. -/
def linearHom : MulAut E →* (V →ₗ[ZMod 2] V) where
  toFun g := (AddEquiv.toMultiplicative.symm g).toAddMonoidHom.toZModLinearMap 2
  map_one' := by ext v i; rfl
  map_mul' g h := by ext v i; rfl

def matrixHom : MulAut E →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp linearHom

theorem matrixHom_action (g : MulAut E) (v : V) :
    matrixHom g *ᵥ v = (g (Multiplicative.ofAdd v)).toAdd := by
  exact congrArg (fun f : V →ₗ[ZMod 2] V => f v)
    (Matrix.toLin'_toMatrix' (linearHom g))

def toSL : MulAut E →* SL(4,ZMod 2) where
  toFun g := ⟨matrixHom g, by
    have h := congrArg Matrix.det (map_mul matrixHom g g⁻¹)
    rw [mul_inv_cancel, map_one, Matrix.det_one, Matrix.det_mul] at h
    rcases Atlas.Codes.bit_cases (Matrix.det (matrixHom g)) with h0 | h1
    · simp [h0] at h
    · exact h1⟩
  map_one' := Subtype.ext (map_one matrixHom)
  map_mul' g h := Subtype.ext (map_mul matrixHom g h)

theorem toSL_injective : Function.Injective toSL := by
  intro g h he
  apply MulEquiv.ext
  intro v
  have hm := congrArg (fun a : SL(4,ZMod 2) => a.val *ᵥ v.toAdd) he
  change matrixHom g *ᵥ v.toAdd = matrixHom h *ᵥ v.toAdd at hm
  rw [matrixHom_action, matrixHom_action] at hm
  exact congrArg Multiplicative.ofAdd hm

noncomputable def toAlt8 : MulAut E →* alternatingGroup (Fin 8) :=
  ((Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.toMonoidHom).comp
    sl4TwoEquivPSL.toMonoidHom).comp toSL

theorem toAlt8_injective : Function.Injective toAlt8 :=
  Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.injective.comp
    (sl4TwoEquivPSL.injective.comp toSL_injective)

/-- The exceptional image intertwines the two genuine quadratic actions. -/
theorem toAlt8_orthogonal (g : MulAut E) :
    DeletedEight.orthogonalHom (toAlt8 g).val = Exterior.toOrthogonal (toSL g) :=
  Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8_orthogonal (toSL g)

open Equiv

def rowPerm : Perm (Fin 8) := swap 4 5 * swap 6 7

def rowMatrix : SL(4,ZMod 2) :=
  ⟨!![1,0,1,0; 0,1,0,1; 0,0,1,0; 0,0,0,1], by decide +kernel⟩

theorem toSL_row : toSL row = rowMatrix := by
  apply Subtype.ext
  change matrixHom row = rowMatrix.val
  ext i j
  change (row (Multiplicative.ofAdd (Pi.single j 1))).toAdd i = rowMatrix.val i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem orthogonal_eq_of_raw (g : SL(4,ZMod 2)) (p : Perm (Fin 8))
    (h : ∀ x : DeletedEight.D, ∀ i : Fin 8,
      DeletedEight.raw (Exterior.onD g x) i =
        DeletedEight.raw x (p.symm i) + DeletedEight.raw x (p.symm 7)) :
    DeletedEight.orthogonalHom p = Exterior.toOrthogonal g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply DeletedEight.splitEquiv.injective
  change DeletedEight.splitEquiv
      (DeletedEight.splitEquiv.symm (DeletedEight.quotientPerm p (DeletedEight.splitEquiv x))) = _
  rw [LinearEquiv.apply_symm_apply]
  change Submodule.Quotient.mk (DeletedEight.evenPerm p (DeletedEight.intoEven x)) =
    Submodule.Quotient.mk (DeletedEight.intoEven (Exterior.onD g x))
  apply (Submodule.Quotient.eq DeletedEight.constants).mpr
  apply Submodule.mem_span_singleton.mpr
  refine ⟨DeletedEight.raw x (p.symm 7), ?_⟩
  apply Subtype.ext
  funext i
  change DeletedEight.raw x (p.symm 7) * 1 =
    DeletedEight.raw x (p.symm i) - DeletedEight.raw (Exterior.onD g x) i
  rw [h, mul_one]
  have hb : ∀ a b : ZMod 2, a = b - (b + a) := by decide +kernel
  exact hb _ _

private def normalizedRaw (p : Perm (Fin 8)) : DeletedEight.D →ₗ[ZMod 2] DeletedEight.V where
  toFun x i := DeletedEight.raw x (p.symm i) + DeletedEight.raw x (p.symm 7)
  map_add' x y := by
    ext i
    simp only [map_add, Pi.add_apply]
    abel
  map_smul' a x := by
    ext i
    simp only [map_smul, Pi.smul_apply, smul_add, RingHom.id_apply]

private theorem raw_identity_of_basis (g : SL(4,ZMod 2)) (p : Perm (Fin 8))
    (h : ∀ j : ClassicalOrthogonal.Index 3, ∀ i : Fin 8,
      DeletedEight.raw (Exterior.onD g (Pi.single j 1)) i =
        DeletedEight.raw (Pi.single j 1) (p.symm i) +
          DeletedEight.raw (Pi.single j 1) (p.symm 7)) :
    ∀ x : DeletedEight.D, ∀ i : Fin 8,
      DeletedEight.raw (Exterior.onD g x) i =
        DeletedEight.raw x (p.symm i) + DeletedEight.raw x (p.symm 7) := by
  have hl : DeletedEight.raw.comp (Exterior.onD g).toLinearMap = normalizedRaw p := by
    apply (Pi.basisFun (ZMod 2) (ClassicalOrthogonal.Index 3)).ext
    intro j
    ext i
    simpa [Pi.basisFun_apply, normalizedRaw] using h j i
  intro x i
  exact congrFun (DFunLike.congr_fun hl x) i

theorem row_raw : ∀ x : DeletedEight.D, ∀ i : Fin 8,
    DeletedEight.raw (Exterior.onD rowMatrix x) i =
      DeletedEight.raw x (rowPerm.symm i) + DeletedEight.raw x (rowPerm.symm 7) := by
  apply raw_identity_of_basis
  decide +kernel

theorem toAlt8_row : (toAlt8 row).val = rowPerm := by
  apply DeletedEight.orthogonalHom_injective
  rw [toAlt8_orthogonal]
  rw [toSL_row]
  exact (orthogonal_eq_of_raw _ _ row_raw).symm



def columnPerm : Perm (Fin 8) := swap 0 2 * swap 6 7

def columnMatrix : SL(4,ZMod 2) :=
  ⟨!![1,0,0,0; 1,1,0,0; 0,0,1,0; 0,0,1,1], by decide +kernel⟩

theorem toSL_column : toSL column = columnMatrix := by
  apply Subtype.ext
  change matrixHom column = columnMatrix.val
  ext i j
  change (column (Multiplicative.ofAdd (Pi.single j 1))).toAdd i = columnMatrix.val i j
  fin_cases i <;> fin_cases j <;> rfl

theorem column_raw : ∀ x : DeletedEight.D, ∀ i : Fin 8,
    DeletedEight.raw (Exterior.onD columnMatrix x) i =
      DeletedEight.raw x (columnPerm.symm i) + DeletedEight.raw x (columnPerm.symm 7) := by
  apply raw_identity_of_basis
  decide +kernel

theorem toAlt8_column : (toAlt8 column).val = columnPerm := by
  apply DeletedEight.orthogonalHom_injective
  rw [toAlt8_orthogonal]
  rw [toSL_column]
  exact (orthogonal_eq_of_raw _ _ column_raw).symm

def columnCubicPerm : Perm (Fin 8) := swap 0 1 * swap 1 2

def columnCubicMatrix : SL(4,ZMod 2) :=
  ⟨!![0,1,0,0; 1,1,0,0; 0,0,0,1; 0,0,1,1], by decide +kernel⟩

theorem toSL_columnCubic : toSL columnCubic = columnCubicMatrix := by
  apply Subtype.ext
  change matrixHom columnCubic = columnCubicMatrix.val
  ext i j
  change (columnCubic (Multiplicative.ofAdd (Pi.single j 1))).toAdd i = columnCubicMatrix.val i j
  fin_cases i <;> fin_cases j <;> rfl

theorem columnCubic_raw : ∀ x : DeletedEight.D, ∀ i : Fin 8,
    DeletedEight.raw (Exterior.onD columnCubicMatrix x) i =
      DeletedEight.raw x (columnCubicPerm.symm i) + DeletedEight.raw x (columnCubicPerm.symm 7) := by
  apply raw_identity_of_basis
  decide +kernel

theorem toAlt8_columnCubic : (toAlt8 columnCubic).val = columnCubicPerm := by
  apply DeletedEight.orthogonalHom_injective
  rw [toAlt8_orthogonal]
  rw [toSL_columnCubic]
  exact (orthogonal_eq_of_raw _ _ columnCubic_raw).symm

def normalizingCubicPerm : Perm (Fin 8) := (swap 0 5 * swap 5 6) * (swap 2 4 * swap 4 7)

def normalizingCubicMatrix : SL(4,ZMod 2) :=
  ⟨!![0,0,0,1; 0,1,0,1; 0,0,1,0; 1,0,0,1], by decide +kernel⟩

theorem toSL_normalizingCubic : toSL normalizingCubic = normalizingCubicMatrix := by
  apply Subtype.ext
  change matrixHom normalizingCubic = normalizingCubicMatrix.val
  ext i j
  change (normalizingCubic (Multiplicative.ofAdd (Pi.single j 1))).toAdd i = normalizingCubicMatrix.val i j
  fin_cases i <;> fin_cases j <;> rfl

theorem normalizingCubic_raw : ∀ x : DeletedEight.D, ∀ i : Fin 8,
    DeletedEight.raw (Exterior.onD normalizingCubicMatrix x) i =
      DeletedEight.raw x (normalizingCubicPerm.symm i) + DeletedEight.raw x (normalizingCubicPerm.symm 7) := by
  apply raw_identity_of_basis
  decide +kernel

theorem toAlt8_normalizingCubic : (toAlt8 normalizingCubic).val = normalizingCubicPerm := by
  apply DeletedEight.orthogonalHom_injective
  rw [toAlt8_orthogonal]
  rw [toSL_normalizingCubic]
  exact (orthogonal_eq_of_raw _ _ normalizingCubic_raw).symm

end BinaryFourSplitPair.JoinedIdentification
