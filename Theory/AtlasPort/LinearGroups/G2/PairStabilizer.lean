module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/PairStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The full opposite-vector stabilizer is SL2

The subgroup consists of actual split-octonion automorphisms fixing the vectors
x1 and x8 (Lean indices 0 and 7). Their products determine x4 and x5. The Peirce
identities then put the images of x6 and x7 in their original two-dimensional
plane. Their product forces determinant one, and multiplication by x1 determines
the images of x2 and x3. Conversely each determinant-one matrix gives the explicit
multiplication-preserving block map. This proves the full stabilizer statement
without a group-order or simplicity assumption, in every characteristic.
-/
noncomputable section

namespace Atlas.G2.PairStabilizer
open Atlas.SplitOctonion Matrix
open scoped MatrixGroups
variable {F : Type*} [Field F]

abbrev E (i : Fin 8) : Carrier F := basisVector i

def blockLinear (M : Matrix (Fin 2) (Fin 2) F) : Carrier F →ₗ[F] Carrier F where
  toFun x := ![x 0, M 0 0*x 1-M 0 1*x 2, -M 1 0*x 1+M 1 1*x 2,
    x 3, x 4, M 0 0*x 5+M 0 1*x 6, M 1 0*x 5+M 1 1*x 6, x 7]
  map_add' x y := by
    funext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by
    funext i; fin_cases i <;> simp <;> ring

theorem blockLinear_mul (M N : Matrix (Fin 2) (Fin 2) F) (x : Carrier F) :
    blockLinear (M*N) x = blockLinear M (blockLinear N x) := by
  funext i
  fin_cases i <;> simp [blockLinear, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem blockLinear_one (x : Carrier F) : blockLinear (1 : Matrix (Fin 2) (Fin 2) F) x = x := by
  funext i
  fin_cases i <;> simp [blockLinear]

def blockEquiv (M : SL(2,F)) : Carrier F ≃ₗ[F] Carrier F where
  toLinearMap := blockLinear M.val
  invFun := blockLinear M⁻¹.val
  left_inv x := by
    change blockLinear (M⁻¹).val (blockLinear M.val x) = x
    rw [← blockLinear_mul]
    have h : M⁻¹.val*M.val = 1 := congrArg Subtype.val (inv_mul_cancel M)
    rw [h,blockLinear_one]
  right_inv x := by
    change blockLinear M.val (blockLinear (M⁻¹).val x) = x
    rw [← blockLinear_mul]
    have h : M.val*M⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel M)
    rw [h,blockLinear_one]

theorem block_preserves_mul (M : SL(2,F)) (x y : Carrier F) :
    blockLinear M.val (mul x y) = mul (blockLinear M.val x) (blockLinear M.val y) := by
  have hd : M.val 0 0 * M.val 1 1 - M.val 0 1 * M.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.prop
  funext i
  fin_cases i
  · simp [blockLinear, mul]
    linear_combination (x 1 * y 2 - x 2 * y 1) * hd
  · simp [blockLinear, mul]; ring
  · simp [blockLinear, mul]; ring
  · simp [blockLinear, mul]
    linear_combination (x 5 * y 2 + x 6 * y 1) * hd
  · simp [blockLinear, mul]
    linear_combination (x 1 * y 6 + x 2 * y 5) * hd
  · simp [blockLinear, mul]; ring
  · simp [blockLinear, mul]; ring
  · simp [blockLinear, mul]
    linear_combination (x 6 * y 5 - x 5 * y 6) * hd

def blockHom : SL(2,F) →* Model F where
  toFun M := ⟨blockEquiv M,block_preserves_mul M⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact blockLinear_one
  map_mul' M N := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact blockLinear_mul M.val N.val

/-- The actual subgroup fixing the two specified opposite singular vectors. -/
def fixingPair : Subgroup (Model F) where
  carrier := {g | g.val (E 0) = E 0 ∧ g.val (E 7) = E 7}
  one_mem' := ⟨rfl,rfl⟩
  mul_mem' {g h} hg hh := by
    constructor
    · change g.val (h.val (E 0)) = E 0
      rw [hh.1,hg.1]
    · change g.val (h.val (E 7)) = E 7
      rw [hh.2,hg.2]
  inv_mem' {g} hg := by
    constructor
    · apply g.val.injective
      change g.val (g.val.symm (E 0)) = g.val (E 0)
      rw [g.val.apply_symm_apply,hg.1]
    · apply g.val.injective
      change g.val (g.val.symm (E 7)) = g.val (E 7)
      rw [g.val.apply_symm_apply,hg.2]

theorem block_mem_fixingPair (M : SL(2,F)) : blockHom M ∈ fixingPair := by
  constructor <;> funext i <;> fin_cases i <;> simp [blockHom,blockEquiv,blockLinear,E,basisVector]

def blockToPair : SL(2,F) →* fixingPair (F := F) :=
  blockHom.codRestrict fixingPair block_mem_fixingPair


theorem plane_of_products (x : Carrier F)
    (h3 : mul (E 3) x = x) (h7 : mul (E 7) x = 0) :
    x = ![0,0,0,0,0,x 5,x 6,0] := by
  have h1 : x 1 = 0 := by simpa [mul,E,basisVector] using (congrFun h3 1).symm
  have h2 : x 2 = 0 := by simpa [mul,E,basisVector] using (congrFun h3 2).symm
  have h4 : x 4 = 0 := by simpa [mul,E,basisVector] using (congrFun h3 4).symm
  have h7' : x 7 = 0 := by simpa [mul,E,basisVector] using (congrFun h3 7).symm
  have h0 : x 0 = 0 := by simpa [mul,E,basisVector] using congrFun h7 4
  have ht : x 3 = 0 := by simpa [mul,E,basisVector] using congrFun h7 7
  funext i
  fin_cases i <;> simp [h1,h2,h4,h7',h0,ht]

theorem pair_fixes_diagonal (g : fixingPair (F := F)) :
    g.val.val (E 3) = E 3 ∧ g.val.val (E 4) = E 4 := by
  have hp03 : mul (E 0 : Carrier F) (E 7) = -E 3 := by
    funext i; fin_cases i <;> simp [mul,E,basisVector]
  have hp74 : mul (E 7 : Carrier F) (E 0) = -E 4 := by
    funext i; fin_cases i <;> simp [mul,E,basisVector]
  constructor
  · have h := automorphism_mul g.val (E 0) (E 7)
    rw [hp03,map_neg,g.prop.1,g.prop.2,hp03] at h
    exact neg_injective h
  · have h := automorphism_mul g.val (E 7) (E 0)
    rw [hp74,map_neg,g.prop.2,g.prop.1,hp74] at h
    exact neg_injective h

theorem pair_image_plane (g : fixingPair (F := F)) (j : Fin 8)
    (h3 : mul (E 3 : Carrier F) (E j) = E j)
    (h7 : mul (E 7 : Carrier F) (E j) = 0) :
    g.val.val (E j) = ![0,0,0,0,0,g.val.val (E j) 5,g.val.val (E j) 6,0] := by
  apply plane_of_products
  · have h := automorphism_mul g.val (E 3) (E j)
    rw [h3,(pair_fixes_diagonal g).1] at h
    exact h.symm
  · have h := automorphism_mul g.val (E 7) (E j)
    rw [h7,map_zero,g.prop.2] at h
    exact h.symm

theorem pair_image_five (g : fixingPair (F := F)) :
    g.val.val (E 5) = ![0,0,0,0,0,g.val.val (E 5) 5,g.val.val (E 5) 6,0] :=
  pair_image_plane g 5
    (by funext i; fin_cases i <;> simp [mul,E,basisVector])
    (by funext i; fin_cases i <;> simp [mul,E,basisVector])

theorem pair_image_six (g : fixingPair (F := F)) :
    g.val.val (E 6) = ![0,0,0,0,0,g.val.val (E 6) 5,g.val.val (E 6) 6,0] :=
  pair_image_plane g 6
    (by funext i; fin_cases i <;> simp [mul,E,basisVector])
    (by funext i; fin_cases i <;> simp [mul,E,basisVector])

def imageMatrix (g : fixingPair (F := F)) : Matrix (Fin 2) (Fin 2) F :=
  !![g.val.val (E 5) 5, g.val.val (E 6) 5;
     g.val.val (E 5) 6, g.val.val (E 6) 6]

theorem imageMatrix_det (g : fixingPair (F := F)) : (imageMatrix g).det = 1 := by
  have hp : mul (E 5 : Carrier F) (E 6) = E 7 := by
    funext i; fin_cases i <;> simp [mul,E,basisVector]
  have h := automorphism_mul g.val (E 5) (E 6)
  rw [hp,g.prop.2,pair_image_five,pair_image_six] at h
  have he := congrFun h 7
  have he' : (1 : F) = g.val.val (E 5) 5 * g.val.val (E 6) 6 -
    g.val.val (E 5) 6 * g.val.val (E 6) 5 := by simpa [mul,E,basisVector] using he
  simp [imageMatrix,Matrix.det_fin_two]
  linear_combination -he'

def imageSL (g : fixingPair (F := F)) : SL(2,F) := ⟨imageMatrix g,imageMatrix_det g⟩

theorem block_image_basis (g : fixingPair (F := F)) (i : Fin 8) :
    g.val.val (E i) = blockLinear (imageMatrix g) (E i) := by
  have h5 := pair_image_five g
  have h6 := pair_image_six g
  have h1 : g.val.val (E 1) = mul (E 0) (g.val.val (E 5)) := by
    have hp : mul (E 0 : Carrier F) (E 5) = E 1 := by
      funext i; fin_cases i <;> simp [mul,E,basisVector]
    have h := automorphism_mul g.val (E 0) (E 5)
    rwa [hp,g.prop.1] at h
  have h2 : g.val.val (E 2) = -mul (E 0) (g.val.val (E 6)) := by
    have hp : mul (E 0 : Carrier F) (E 6) = -E 2 := by
      funext i; fin_cases i <;> simp [mul,E,basisVector]
    have h := automorphism_mul g.val (E 0) (E 6)
    rw [hp,map_neg,g.prop.1] at h
    simpa using congrArg Neg.neg h
  fin_cases i
  · change g.val.val (E 0) = blockLinear (imageMatrix g) (E 0)
    rw [g.prop.1]; funext j; fin_cases j <;> simp [blockLinear,imageMatrix,E,basisVector]
  · change g.val.val (E 1) = blockLinear (imageMatrix g) (E 1)
    rw [h1,h5]; funext j; fin_cases j <;> simp [mul,blockLinear,imageMatrix,E,basisVector]
  · change g.val.val (E 2) = blockLinear (imageMatrix g) (E 2)
    rw [h2,h6]; funext j; fin_cases j <;> simp [mul,blockLinear,imageMatrix,E,basisVector]
  · change g.val.val (E 3) = blockLinear (imageMatrix g) (E 3)
    rw [(pair_fixes_diagonal g).1]
    funext j; fin_cases j <;> simp [blockLinear,imageMatrix,E,basisVector]
  · change g.val.val (E 4) = blockLinear (imageMatrix g) (E 4)
    rw [(pair_fixes_diagonal g).2]
    funext j; fin_cases j <;> simp [blockLinear,imageMatrix,E,basisVector]
  · change g.val.val (E 5) = blockLinear (imageMatrix g) (E 5)
    rw [h5]; funext j; fin_cases j <;> simp [blockLinear,imageMatrix,E,basisVector]
  · change g.val.val (E 6) = blockLinear (imageMatrix g) (E 6)
    rw [h6]; funext j; fin_cases j <;> simp [blockLinear,imageMatrix,E,basisVector]
  · change g.val.val (E 7) = blockLinear (imageMatrix g) (E 7)
    rw [g.prop.2]; funext j; fin_cases j <;> simp [blockLinear,imageMatrix,E,basisVector]

theorem block_imageSL (g : fixingPair (F := F)) : blockToPair (imageSL g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun F (Fin 8)).ext
  intro i
  change blockLinear (imageMatrix g) ((Pi.basisFun F (Fin 8)) i) =
    g.val.val ((Pi.basisFun F (Fin 8)) i)
  simpa [Pi.basisFun_apply,E,basisVector] using
    (block_image_basis g i).symm

theorem blockToPair_injective : Function.Injective (blockToPair (F := F)) := by
  intro M N h
  have h55 := congrArg (fun g : fixingPair (F := F) => g.val.val (E 5) 5) h
  have h56 := congrArg (fun g : fixingPair (F := F) => g.val.val (E 6) 5) h
  have h65 := congrArg (fun g : fixingPair (F := F) => g.val.val (E 5) 6) h
  have h66 := congrArg (fun g : fixingPair (F := F) => g.val.val (E 6) 6) h
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j
  · simpa [blockToPair,blockHom,blockEquiv,blockLinear,E,basisVector] using h55
  · simpa [blockToPair,blockHom,blockEquiv,blockLinear,E,basisVector] using h56
  · simpa [blockToPair,blockHom,blockEquiv,blockLinear,E,basisVector] using h65
  · simpa [blockToPair,blockHom,blockEquiv,blockLinear,E,basisVector] using h66

/-- The full two-vector stabilizer in the actual octonion automorphism group is SL2. -/
def fixingPairEquivSL2 : fixingPair (F := F) ≃* SL(2,F) :=
  (MulEquiv.ofBijective blockToPair ⟨blockToPair_injective,
    fun g => ⟨imageSL g,block_imageSL g⟩⟩).symm

end Atlas.G2.PairStabilizer
