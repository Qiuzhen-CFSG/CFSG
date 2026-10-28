module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.HighestVector
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Algebra.Bilinear

/-!
# Polynomial orbit coefficients for binary SL₃ tensor words

Write an upper-unitriangular matrix as `!![1,x,z; 0,1,y; 0,0,1]`.
Its first row and the last column of its inverse in characteristic two are
`(1,x,z)` and `(xy+z,y,1)`. Contracting them against the natural, dual,
and trace-zero adjoint coordinates gives concrete polynomial coefficient maps.
Tensor products multiply these coefficients, with successive factors using
squared variables. Evaluation is proved to equal the actual word-action
coefficient, and the highest tensor has constant coefficient polynomial one.
The literal upper subgroup fixes each seed, hence also their tensor products.

The filtered space `flagSpace K a b` and binary pair `wordWeight w` provide
shared interfaces for two further results: injectivity of `wordPolynomial`
and finite-grid interpolation. Neither injectivity is asserted here.

Source: GLS III, 2.8.6(a), 2.8.9 and 2.8.10(c), in
`refs/KGroup/GLS3/chapter2.tex`. These coordinate calculations implement the
concrete trace-zero model of the binary adjoint factor.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct MatrixGroups
open Matrix
open MvPolynomial Matrix.PSL3Even.UnipotentGeometry
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
variable (K : Type*) [Field K]
abbrev Polynomial := MvPolynomial (Fin 3) K

def leftRow : Fin 3 → Polynomial K := ![1, X 0, X 2]
def rightColumn : Fin 3 → Polynomial K := ![X 0 * X 1 + X 2, X 1, 1]

def dualEntry (i : Fin 3) : Module.Dual K (Fin 3 → K) →ₗ[K] K where
  toFun f := f (Pi.single i 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def adjointEntry (i j : Fin 3) : AdjointSpace K →ₗ[K] K where
  toFun f := f.val (Pi.single j 1) i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def factorPolynomial : (a : Factor) → Space K a →ₗ[K] Polynomial K
  | .trivial => (Algebra.ofId K (Polynomial K)).toLinearMap
  | .natural => ∑ i, (LinearMap.proj i).smulRight (leftRow K i)
  | .dual => ∑ j, (dualEntry K j).smulRight (rightColumn K j)
  | .adjoint => ∑ i, ∑ j, (adjointEntry K i j).smulRight (leftRow K i * rightColumn K j)

def squareVariables : Polynomial K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval (fun i => X i ^ 2)

def wordPolynomial : (w : List Factor) → WordSpace K w →ₗ[K] Polynomial K
  | [] => (Algebra.ofId K (Polynomial K)).toLinearMap
  | a :: w => LinearMap.mul' K (Polynomial K) ∘ₗ
      TensorProduct.map (factorPolynomial K a)
        ((squareVariables K).toLinearMap ∘ₗ wordPolynomial w)

@[simp] theorem wordPolynomial_tmul (a : Factor) (w : List Factor)
    (v : Space K a) (z : WordSpace K w) :
    wordPolynomial K (a :: w) (v ⊗ₜ[K] z) =
      factorPolynomial K a v * squareVariables K (wordPolynomial K w z) := by
  change (LinearMap.mul' K (Polynomial K))
    (_root_.TensorProduct.map (factorPolynomial K a)
      ((squareVariables K).toLinearMap ∘ₗ wordPolynomial K w) (v ⊗ₜ[K] z)) = _
  rw [_root_.TensorProduct.map_tmul, LinearMap.mul'_apply]
  rfl

/-- A filtered coordinate space on the big cell of the flag variety. -/
def flagSpace (a b : ℕ) : Submodule K (Polynomial K) :=
  Submodule.span K {p | ∃ i j k l : ℕ, i + j ≤ a ∧ k + l ≤ b ∧
    p = X 0 ^ i * X 2 ^ j * X 1 ^ k * (X 0 * X 1 + X 2) ^ l}

/-- Binary digits of the two fundamental highest weights. -/
def wordWeight : List Factor → ℕ × ℕ
  | [] => (0, 0)
  | a :: w =>
      ( (if a = .natural ∨ a = .adjoint then 1 else 0) + 2 * (wordWeight w).1,
        (if a = .dual ∨ a = .adjoint then 1 else 0) + 2 * (wordWeight w).2 )

theorem wordWeight_lt (w : List Factor) :
    (wordWeight w).1 < 2 ^ w.length ∧ (wordWeight w).2 < 2 ^ w.length := by
  induction w with
  | nil => decide
  | cons a w ih =>
    have hp : 2 ^ (a :: w).length = 2 * 2 ^ w.length := by
      simp [pow_succ, Nat.mul_comm]
    rw [hp]
    cases a <;> simp only [wordWeight, reduceCtorEq, or_false, false_or,
      or_self, ite_true, ite_false] <;> omega

@[simp] theorem factorPolynomial_seed (a : Factor) :
    factorPolynomial K a (factorSeed K a) = 1 := by
  cases a with
  | trivial => exact map_one (Algebra.ofId K (Polynomial K))
  | natural =>
    change (∑ i : Fin 3, (Pi.single 0 (1 : K) : Fin 3 → K) i • leftRow K i) = 1
    simp [leftRow]
  | dual => simp [factorPolynomial, factorSeed, dualEntry, rightColumn, Fin.sum_univ_three]
  | adjoint => simp [factorPolynomial, factorSeed, adjointEntry, leftRow, rightColumn,
      Fin.sum_univ_three]


@[simp] theorem wordPolynomial_seed (w : List Factor) :
    wordPolynomial K w (wordSeed K w) = 1 := by
  induction w with
  | nil => exact map_one (Algebra.ofId K (Polynomial K))
  | cons a w ih =>
    change wordPolynomial K (a :: w) (factorSeed K a ⊗ₜ[K] wordSeed K w) = 1
    rw [wordPolynomial_tmul, factorPolynomial_seed, ih, map_one, one_mul]

variable {K}
variable {F : Type*} [Field F] [CharP K 2]

def point (ι : F →+* K) (u : U F) : Fin 3 → K := ![ι u.x, ι u.y, ι u.c]

omit [CharP K 2] in
private theorem natural_upper (ι : F →+* K) (u : U F) (v : Fin 3 → K) :
    natural ι (specialLinear F u) v =
      ![v 0 + ι u.x * v 1 + ι u.c * v 2, v 1 + ι u.y * v 2, v 2] := by
  change (matrix F u).map ι *ᵥ v = _
  ext i
  fin_cases i <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

omit [CharP K 2] in
private theorem vector_expansion (v : Fin 3 → K) :
    v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
  ext i
  fin_cases i <;> simp

private theorem natural_upper_inv_last (ι : F →+* K) (u : U F) :
    natural ι (specialLinear F u)⁻¹ (Pi.single 2 1) =
      ![ι u.x * ι u.y + ι u.c, ι u.y, 1] := by
  rw [← map_inv, natural_upper]
  have hx : (u⁻¹).x = -u.x := rfl
  have hy : (u⁻¹).y = -u.y := rfl
  have hc : (u⁻¹).c = u.x * u.y - u.c := rfl
  simp [hx, hy, hc, CharTwo.neg_eq, sub_eq_add_neg]

private def factorCoefficient : (a : Factor) → Space K a →ₗ[K] K
  | .trivial => LinearMap.id
  | .natural => LinearMap.proj 0
  | .dual => dualEntry K 2
  | .adjoint => adjointEntry K 0 2

omit [CharP K 2] in
private theorem factorPolynomial_zero (a : Factor) (v : Space K a) :
    MvPolynomial.eval (0 : Fin 3 → K) (factorPolynomial K a v) =
      factorCoefficient a v := by
  cases a with
  | trivial =>
    change K at v
    change MvPolynomial.eval _ (C v) = v
    simp
  | natural => simp [factorPolynomial, factorCoefficient, leftRow, Fin.sum_univ_three]
  | dual => simp [factorPolynomial, factorCoefficient, rightColumn, Fin.sum_univ_three]
  | adjoint => simp [factorPolynomial, factorCoefficient, leftRow, rightColumn, Fin.sum_univ_three]

/-- The polynomial is the actual highest-coordinate orbit coefficient. -/
theorem factorPolynomial_eval (ι : F →+* K) (a : Factor) (v : Space K a) (u : U F) :
    MvPolynomial.eval (point ι u) (factorPolynomial K a v) =
      MvPolynomial.eval (0 : Fin 3 → K)
        (factorPolynomial K a (factorRep ι a (specialLinear F u) v)) := by
  rw [factorPolynomial_zero]
  cases a with
  | trivial =>
    change K at v
    change MvPolynomial.eval _ (C v) = v
    simp
  | natural =>
    change (Fin 3 → K) at v
    change _ = (natural ι (specialLinear F u) v) 0
    rw [natural_upper]
    change MvPolynomial.eval (point ι u) (∑ i : Fin 3, v i • leftRow K i) = _
    simp [leftRow, point, Fin.sum_univ_three, mul_comm]
  | dual =>
    change Module.Dual K (Fin 3 → K) at v
    change _ = v (natural ι (specialLinear F u)⁻¹ (Pi.single 2 1))
    rw [natural_upper_inv_last, vector_expansion ![ι u.x * ι u.y + ι u.c, ι u.y, 1]]
    simp [factorPolynomial, dualEntry, rightColumn, point, Fin.sum_univ_three]
    ring
  | adjoint =>
    change AdjointSpace K at v
    change _ = (natural ι (specialLinear F u)
      (v.val (natural ι (specialLinear F u)⁻¹ (Pi.single 2 1)))) 0
    rw [natural_upper, natural_upper_inv_last, vector_expansion ![ι u.x * ι u.y + ι u.c, ι u.y, 1]]
    simp [factorPolynomial, adjointEntry, leftRow, rightColumn, point,
      Fin.sum_univ_three]
    ring

omit [CharP K 2] in
private theorem eval_squareVariables (x : Fin 3 → K) (p : Polynomial K) :
    MvPolynomial.eval x (squareVariables K p) =
      MvPolynomial.eval (fun i => x i ^ 2) p := by
  have h : (MvPolynomial.aeval x).comp (squareVariables K) =
      MvPolynomial.aeval (fun i => x i ^ 2) := by
    ext i
    simp [squareVariables]
  exact AlgHom.congr_fun h p

/-- Evaluation recovers the actual orbit coefficient for every tensor word. -/
theorem wordPolynomial_eval (ι : F →+* K) (w : List Factor)
    (v : WordSpace K w) (u : U F) :
    MvPolynomial.eval (point ι u) (wordPolynomial K w v) =
      MvPolynomial.eval (0 : Fin 3 → K)
        (wordPolynomial K w (wordRep ι w (specialLinear F u) v)) := by
  induction w generalizing ι with
  | nil =>
    change K at v
    change MvPolynomial.eval _ (C v) = MvPolynomial.eval _ (C v)
    simp
  | cons a w ih =>
    induction v using _root_.TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v z =>
      change MvPolynomial.eval (point ι u) (wordPolynomial K (a :: w) (v ⊗ₜ[K] z)) =
        MvPolynomial.eval (0 : Fin 3 → K) (wordPolynomial K (a :: w)
          (factorRep ι a (specialLinear F u) v ⊗ₜ[K]
            wordRep ((frobenius K 2).comp ι) w (specialLinear F u) z))
      rw [wordPolynomial_tmul, wordPolynomial_tmul]
      simp only [map_mul, eval_squareVariables]
      have hp : (fun i => point ι u i ^ 2) = point ((frobenius K 2).comp ι) u := by
        ext i
        fin_cases i <;> simp [point, frobenius_def]
      have hz : (fun i : Fin 3 => (0 : Fin 3 → K) i ^ 2) = 0 := by ext i; simp
      rw [hp, hz, factorPolynomial_eval, ih]
    | add x y hx hy => simp only [map_add, hx, hy]

omit [CharP K 2] in
private theorem natural_upper_first (ι : F →+* K) (u : U F) :
    natural ι (specialLinear F u) (Pi.single 0 1) = Pi.single 0 1 := by
  rw [natural_upper]
  ext i
  fin_cases i <;> simp

omit [CharP K 2] in
/-- Each concrete highest vector is fixed by the literal upper subgroup. -/
theorem factorSeed_fixed (ι : F →+* K) (a : Factor) (u : U F) :
    factorRep ι a (specialLinear F u) (factorSeed K a) = factorSeed K a := by
  cases a with
  | trivial => rfl
  | natural => exact natural_upper_first ι u
  | dual =>
    apply LinearMap.ext
    intro v
    change (natural ι (specialLinear F u)⁻¹ v) 2 = v 2
    rw [← map_inv, natural_upper]
    rfl
  | adjoint =>
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change natural ι (specialLinear F u)
      ((natural ι (specialLinear F u)⁻¹ v) 2 • Pi.single 0 1) = v 2 • Pi.single 0 1
    rw [map_smul, natural_upper_first, ← map_inv, natural_upper]
    rfl

/-- The actual recursive highest tensor is fixed by the upper subgroup. -/
theorem wordSeed_fixed (ι : F →+* K) (w : List Factor) (u : U F) :
    wordRep ι w (specialLinear F u) (wordSeed K w) = wordSeed K w := by
  induction w generalizing ι with
  | nil => rfl
  | cons a w ih =>
    change factorRep ι a (specialLinear F u) (factorSeed K a) ⊗ₜ[K]
      wordRep ((frobenius K 2).comp ι) w (specialLinear F u) (wordSeed K w) =
        factorSeed K a ⊗ₜ[K] wordSeed K w
    rw [factorSeed_fixed, ih]

end Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
