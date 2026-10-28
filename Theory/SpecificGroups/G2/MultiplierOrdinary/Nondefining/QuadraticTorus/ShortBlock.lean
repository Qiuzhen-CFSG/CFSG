module

public import Theory.AtlasPort.LinearGroups.G2.PairStabilizer
public import Mathlib.Algebra.CharP.Two
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Commuting rank-one factors in the split-octonion G₂ model

The short factor conjugates the split-quaternion matrix
`[[x₃,x₀],[-x₇,x₄]]` and acts on the remaining two two-dimensional blocks.
Its coordinate multiplication defects are multiples of `det M - 1`.
It commutes with the existing long-root `PairStabilizer.blockHom` in every
characteristic. In characteristic two their product is faithful: its action
on the quaternion block recovers the squares of the four short-factor entries,
and the long factor is already faithful.

The consumer in `QuadraticTorus` inserts the two quadratic norm-one tori and
an independent Frobenius reflection into these actual octonion automorphisms.
This supplies geometry for Aschbacher–Smith I.1.3–I.1.4, printed pp.407–408,
and GLS3 §6.1. The coordinate conventions and long-root block come from the
licensed ATLAS port `G2.PairStabilizer`; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`. The short-factor formulas extend its method.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.PairStabilizer Atlas.SplitOctonion Matrix
open scoped MatrixGroups CharTwo

namespace Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus
variable {F : Type*} [Field F]

def shortApply (M : Matrix (Fin 2) (Fin 2) F) (x : Carrier F) : Carrier F :=
    ![M 0 0 ^ 2 * x 0 - M 0 0 * M 0 1 * x 3 + M 0 0 * M 0 1 * x 4 + M 0 1 ^ 2 * x 7,
      M 0 0 * x 1 - M 0 1 * x 5,
      M 0 0 * x 2 + M 0 1 * x 6,
      M 0 0 * M 1 1 * x 3 - M 0 1 * M 1 0 * x 4 - M 0 0 * M 1 0 * x 0 - M 0 1 * M 1 1 * x 7,
      -M 0 1 * M 1 0 * x 3 + M 0 0 * M 1 1 * x 4 + M 0 0 * M 1 0 * x 0 + M 0 1 * M 1 1 * x 7,
      -M 1 0 * x 1 + M 1 1 * x 5,
      M 1 0 * x 2 + M 1 1 * x 6,
      M 1 0 ^ 2 * x 0 - M 1 0 * M 1 1 * x 3 + M 1 0 * M 1 1 * x 4 + M 1 1 ^ 2 * x 7]
def shortLinear (M : Matrix (Fin 2) (Fin 2) F) : Carrier F →ₗ[F] Carrier F where
  toFun := shortApply M
  map_add' x y := by funext i; fin_cases i <;> simp [shortApply] <;> ring
  map_smul' r x := by funext i; fin_cases i <;> simp [shortApply] <;> ring

theorem shortLinear_mul (M N : Matrix (Fin 2) (Fin 2) F) (x : Carrier F) :
    shortLinear (M * N) x = shortLinear M (shortLinear N x) := by
  change shortApply (M * N) x = shortApply M (shortApply N x)
  funext i
  fin_cases i <;> simp [shortApply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem shortLinear_one (x : Carrier F) : shortLinear (1 : Matrix (Fin 2) (Fin 2) F) x = x := by
  funext i
  fin_cases i <;> simp [shortLinear, shortApply]

def shortEquiv (M : SL(2,F)) : Carrier F ≃ₗ[F] Carrier F where
  toLinearMap := shortLinear M.val
  invFun := shortLinear M⁻¹.val
  left_inv x := by
    change shortLinear (M⁻¹).val (shortLinear M.val x) = x
    rw [← shortLinear_mul]
    have h : M⁻¹.val * M.val = 1 := congrArg Subtype.val (inv_mul_cancel M)
    rw [h, shortLinear_one]
  right_inv x := by
    change shortLinear M.val (shortLinear (M⁻¹).val x) = x
    rw [← shortLinear_mul]
    have h : M.val * M⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel M)
    rw [h, shortLinear_one]

theorem short_preserves_mul (M : SL(2,F)) (x y : Carrier F) :
    shortLinear M.val (mul x y) = mul (shortLinear M.val x) (shortLinear M.val y) := by
  have hd : M.val 0 0 * M.val 1 1 - M.val 0 1 * M.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using M.prop
  change shortApply M.val (mul x y) = mul (shortApply M.val x) (shortApply M.val y)
  funext i
  fin_cases i
  · dsimp [shortApply, mul]
    linear_combination (-M.val 0 0 ^ 2 * x 0 * y 4 - M.val 0 0 ^ 2 * x 3 * y 0 - M.val 0 0 * M.val 0 1 * x 0 * y 7
      + M.val 0 0 * M.val 0 1 * x 3 * y 3 - M.val 0 0 * M.val 0 1 * x 4 * y 4
      + M.val 0 0 * M.val 0 1 * x 7 * y 0 - M.val 0 1 ^ 2 * x 4 * y 7 - M.val 0 1 ^ 2 * x 7 * y 3) * hd
  · dsimp [shortApply, mul]
    linear_combination (-M.val 0 0 * x 0 * y 5 - M.val 0 0 * x 1 * y 3 - M.val 0 0 * x 4 * y 1
      + M.val 0 0 * x 5 * y 0 + M.val 0 1 * x 1 * y 7 + M.val 0 1 * x 3 * y 5
      + M.val 0 1 * x 5 * y 4 - M.val 0 1 * x 7 * y 1) * hd
  · dsimp [shortApply, mul]
    linear_combination (M.val 0 0 * x 0 * y 6 - M.val 0 0 * x 2 * y 3 - M.val 0 0 * x 4 * y 2 - M.val 0 0 * x 6 * y 0
      + M.val 0 1 * x 2 * y 7 - M.val 0 1 * x 3 * y 6 - M.val 0 1 * x 6 * y 4 - M.val 0 1 * x 7 * y 2) * hd
  · dsimp [shortApply, mul]
    linear_combination (M.val 0 0 * M.val 1 0 * x 0 * y 4 + M.val 0 0 * M.val 1 0 * x 3 * y 0
      + M.val 0 0 * M.val 1 1 * x 0 * y 7 - M.val 0 0 * M.val 1 1 * x 3 * y 3
      + M.val 0 1 * M.val 1 0 * x 4 * y 4 - M.val 0 1 * M.val 1 0 * x 7 * y 0
      + M.val 0 1 * M.val 1 1 * x 4 * y 7 + M.val 0 1 * M.val 1 1 * x 7 * y 3) * hd
  · dsimp [shortApply, mul]
    linear_combination (-M.val 0 0 * M.val 1 0 * x 0 * y 4 - M.val 0 0 * M.val 1 0 * x 3 * y 0 - M.val 0 0 * M.val 1 1 * x 4 * y 4
      + M.val 0 0 * M.val 1 1 * x 7 * y 0 - M.val 0 1 * M.val 1 0 * x 0 * y 7
      + M.val 0 1 * M.val 1 0 * x 3 * y 3 - M.val 0 1 * M.val 1 1 * x 4 * y 7 - M.val 0 1 * M.val 1 1 * x 7 * y 3) * hd
  · dsimp [shortApply, mul]
    linear_combination (M.val 1 0 * x 0 * y 5 + M.val 1 0 * x 1 * y 3
      + M.val 1 0 * x 4 * y 1 - M.val 1 0 * x 5 * y 0 - M.val 1 1 * x 1 * y 7 - M.val 1 1 * x 3 * y 5 - M.val 1 1 * x 5 * y 4
      + M.val 1 1 * x 7 * y 1) * hd
  · dsimp [shortApply, mul]
    linear_combination (M.val 1 0 * x 0 * y 6 - M.val 1 0 * x 2 * y 3 - M.val 1 0 * x 4 * y 2 - M.val 1 0 * x 6 * y 0
      + M.val 1 1 * x 2 * y 7 - M.val 1 1 * x 3 * y 6 - M.val 1 1 * x 6 * y 4 - M.val 1 1 * x 7 * y 2) * hd
  · dsimp [shortApply, mul]
    linear_combination (-M.val 1 0 ^ 2 * x 0 * y 4 - M.val 1 0 ^ 2 * x 3 * y 0 - M.val 1 0 * M.val 1 1 * x 0 * y 7
      + M.val 1 0 * M.val 1 1 * x 3 * y 3 - M.val 1 0 * M.val 1 1 * x 4 * y 4
      + M.val 1 0 * M.val 1 1 * x 7 * y 0 - M.val 1 1 ^ 2 * x 4 * y 7 - M.val 1 1 ^ 2 * x 7 * y 3) * hd

def shortHom : SL(2,F) →* Model F where
  toFun M := ⟨shortEquiv M, short_preserves_mul M⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact shortLinear_one
  map_mul' M N := by
    apply Subtype.ext
    apply LinearEquiv.ext
    exact shortLinear_mul M.val N.val

theorem short_block_commute (M N : SL(2,F)) : Commute (shortHom M) (blockHom N) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change shortLinear M.val (blockLinear N.val x) = blockLinear N.val (shortLinear M.val x)
  change shortApply M.val (blockLinear N.val x) = blockLinear N.val (shortApply M.val x)
  have hb (A : Matrix (Fin 2) (Fin 2) F) (y : Carrier F) :
      blockLinear A y = ![y 0, A 0 0*y 1-A 0 1*y 2, -A 1 0*y 1+A 1 1*y 2,
        y 3, y 4, A 0 0*y 5+A 0 1*y 6, A 1 0*y 5+A 1 1*y 6, y 7] := rfl
  simp only [hb]
  funext i
  fin_cases i <;> dsimp [shortApply] <;> ring

def pairHom : SL(2,F) × SL(2,F) →* Model F :=
  shortHom.noncommCoprod blockHom short_block_commute

theorem pairHom_injective [CharP F 2] : Function.Injective (pairHom (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨M, N⟩ h
  have h00 := congrArg (fun g : Model F => g.val (basisVector 0) 0) h
  have h10 := congrArg (fun g : Model F => g.val (basisVector 0) 7) h
  have h01 := congrArg (fun g : Model F => g.val (basisVector 7) 0) h
  have h11 := congrArg (fun g : Model F => g.val (basisVector 7) 7) h
  change shortApply M.val (blockLinear N.val (basisVector 0)) 0 = 1 at h00
  change shortApply M.val (blockLinear N.val (basisVector 0)) 7 = 0 at h10
  change shortApply M.val (blockLinear N.val (basisVector 7)) 0 = 0 at h01
  change shortApply M.val (blockLinear N.val (basisVector 7)) 7 = 1 at h11
  have hb0 : blockLinear N.val (basisVector 0) = basisVector 0 :=
    (block_mem_fixingPair N).1
  have hb7 : blockLinear N.val (basisVector 7) = basisVector 7 :=
    (block_mem_fixingPair N).2
  rw [hb0] at h00 h10
  rw [hb7] at h01 h11
  simp [shortApply, basisVector] at h00 h10 h01 h11
  have hM : M = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> apply CharTwo.sq_inj.mp
    · simpa using h00
    · simpa using h01
    · simpa using h10
    · simpa using h11
  have hN : N = 1 := by
    apply blockToPair_injective
    apply Subtype.ext
    change blockHom N = blockHom 1
    change shortHom M * blockHom N = 1 at h
    simpa only [hM, map_one, one_mul] using h
  exact Prod.ext hM hN

end Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus

end
