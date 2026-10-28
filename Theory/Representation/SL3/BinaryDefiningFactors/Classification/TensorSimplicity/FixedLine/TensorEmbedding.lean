module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.PolynomialModel
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic

/-!
# Embedding binary SL₃ tensor words in flag polynomials

The concrete coefficient map is injective and has image in the flag space
specified by the two binary highest weights. The filtration bound follows by
multiplying flag generators and doubling their exponents under squared-variable
substitution.

For injectivity, the trace-zero relation gives the adjoint coefficient family
`1, x, y, z, xy, xz + x²y, yz, xyz + z²`. Partial derivatives annihilate the
squared-variable tails and recover the eight coefficients in triangular order.
The natural, dual and trivial factors embed in the same coordinate family.
Tensoring these coordinate embeddings and inducting proves the result for every
word, including the empty word, over any field of characteristic two.

These are coordinate lemmas for the concrete modules in GLS III, 2.8.6(a),
2.8.9 and 2.8.10(c), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
open MvPolynomial
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
variable (K : Type*) [Field K]

private theorem flagSpace_generator (a b i j k l : ℕ) (ha : i + j ≤ a) (hb : k + l ≤ b) :
    X 0 ^ i * X 2 ^ j * X 1 ^ k * (X 0 * X 1 + X 2) ^ l ∈ flagSpace K a b :=
  Submodule.subset_span ⟨i, j, k, l, ha, hb, rfl⟩

private theorem flagSpace_one (a b : ℕ) : (1 : Polynomial K) ∈ flagSpace K a b := by
  simpa using flagSpace_generator K a b 0 0 0 0 (by omega) (by omega)

private theorem flagSpace_mul {a b c d : ℕ} {p q : Polynomial K}
    (hp : p ∈ flagSpace K a b) (hq : q ∈ flagSpace K c d) :
    p * q ∈ flagSpace K (a + c) (b + d) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i,j,k,l,ha,hb,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨i',j',k',l',hc,hd,rfl⟩ := hq
      have h := flagSpace_generator K (a + c) (b + d) (i+i') (j+j') (k+k') (l+l')
        (by omega) (by omega)
      convert h using 1
      ring
    | zero => simp
    | add x y hx hy hx' hy' =>
      simpa only [mul_add] using (flagSpace K (a + c) (b + d)).add_mem hx' hy'
    | smul r x hx hx' =>
      simpa only [mul_smul_comm] using (flagSpace K (a + c) (b + d)).smul_mem r hx'
  | zero => simp
  | add x y hx hy hx' hy' =>
    simpa only [add_mul] using (flagSpace K (a + c) (b + d)).add_mem hx' hy'
  | smul r x hx hx' =>
    simpa only [smul_mul_assoc] using (flagSpace K (a + c) (b + d)).smul_mem r hx'

private theorem leftRow_mem (i : Fin 3) : leftRow K i ∈ flagSpace K 1 0 := by
  fin_cases i
  · exact flagSpace_one K 1 0
  · simpa [leftRow] using flagSpace_generator K 1 0 1 0 0 0 (by decide) (by decide)
  · simpa [leftRow] using flagSpace_generator K 1 0 0 1 0 0 (by decide) (by decide)

private theorem rightColumn_mem (i : Fin 3) : rightColumn K i ∈ flagSpace K 0 1 := by
  fin_cases i
  · simpa [rightColumn] using flagSpace_generator K 0 1 0 0 0 1 (by decide) (by decide)
  · simpa [rightColumn] using flagSpace_generator K 0 1 0 0 1 0 (by decide) (by decide)
  · exact flagSpace_one K 0 1

private theorem factorPolynomial_mem (a : Factor) (v : Space K a) :
    factorPolynomial K a v ∈ flagSpace K
      (if a = .natural ∨ a = .adjoint then 1 else 0)
      (if a = .dual ∨ a = .adjoint then 1 else 0) := by
  cases a with
  | trivial =>
    change K at v
    change C v ∈ flagSpace K 0 0
    simpa only [Algebra.smul_def, algebraMap_eq, mul_one] using
      (flagSpace K 0 0).smul_mem v (flagSpace_one K 0 0)
  | natural =>
    change (∑ i : Fin 3, v i • leftRow K i) ∈ flagSpace K 1 0
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (leftRow_mem K i)
  | dual =>
    change (∑ i : Fin 3, dualEntry K i v • rightColumn K i) ∈ flagSpace K 0 1
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (rightColumn_mem K i)
  | adjoint =>
    simp only [factorPolynomial, LinearMap.sum_apply, LinearMap.smulRight_apply,
      reduceCtorEq]
    change (∑ i : Fin 3, ∑ j : Fin 3,
      adjointEntry K i j v • (leftRow K i * rightColumn K j)) ∈ flagSpace K 1 1
    apply (flagSpace K 1 1).sum_mem
    intro i _
    apply (flagSpace K 1 1).sum_mem
    intro j _
    apply (flagSpace K 1 1).smul_mem
    exact flagSpace_mul K (a := 1) (b := 0) (c := 0) (d := 1)
      (leftRow_mem K i) (rightColumn_mem K j)

variable [CharP K 2]
private theorem squareVariables_flagSpace {a b : ℕ} {p : Polynomial K}
    (hp : p ∈ flagSpace K a b) : squareVariables K p ∈ flagSpace K (2 * a) (2 * b) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i,j,k,l,ha,hb,rfl⟩ := hp
    have hs : X (0 : Fin 3) ^ 2 * X 1 ^ 2 + X 2 ^ 2 =
        (X 0 * X 1 + X 2 : Polynomial K) ^ 2 := by
      rw [CharTwo.add_sq, mul_pow]
    simpa [squareVariables, hs, ← pow_mul, Nat.mul_comm] using
      flagSpace_generator K (2 * a) (2 * b) (2 * i) (2 * j) (2 * k) (2 * l) (by omega) (by omega)
  | zero => simp
  | add x y hx hy hx' hy' => simpa using (flagSpace K (2 * a) (2 * b)).add_mem hx' hy'
  | smul r x hx hx' => simpa using (flagSpace K (2 * a) (2 * b)).smul_mem r hx'

/-- Every tensor coefficient lies in the flag filtration of its binary highest weight. -/
theorem wordPolynomial_mem_flagSpace (w : List Factor) (v : WordSpace K w) :
    wordPolynomial K w v ∈ flagSpace K (wordWeight w).1 (wordWeight w).2 := by
  induction w with
  | nil =>
    change K at v
    change C v ∈ flagSpace K 0 0
    simpa only [Algebra.smul_def, algebraMap_eq, mul_one] using
      (flagSpace K 0 0).smul_mem v (flagSpace_one K 0 0)
  | cons a w ih =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | tmul v z =>
      rw [wordPolynomial_tmul]
      exact flagSpace_mul K (factorPolynomial_mem K a v) (squareVariables_flagSpace K (ih z))
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

private theorem squareVariables_injective : Function.Injective (squareVariables K) := by
  have hf (p : Polynomial K) :
      MvPolynomial.map (frobenius K 2) (squareVariables K p) = p ^ 2 := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [show squareVariables K (C c) = C c by simp [squareVariables], MvPolynomial.map_C]
      change C (c ^ 2) = C c ^ 2
      exact map_pow C c 2
    | add p q hp hq => simp [map_add, hp, hq, CharTwo.add_sq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp]
      simp [squareVariables, mul_pow]
  intro p q h
  have he : p ^ 2 = q ^ 2 := by rw [← hf p, ← hf q, h]
  exact CharTwo.sq_injective he

private theorem pderiv_squareVariables (i : Fin 3) (p : Polynomial K) :
    pderiv i (squareVariables K p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [squareVariables]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
    rw [map_mul, show squareVariables K (X j) = X j ^ 2 by simp [squareVariables], pderiv_mul, hp]
    simp [CharTwo.two_eq_zero]

private def headMonomials : Fin 8 → Polynomial K :=
  ![1, X 0, X 1, X 2, X 0 * X 1, X 0 * X 2 + X 0 ^ 2 * X 1,
    X 1 * X 2, X 0 * X 1 * X 2 + X 2 ^ 2]

private def mix : (Fin 8 → Polynomial K) →ₗ[K] Polynomial K :=
  ∑ i, (LinearMap.mulLeft K (headMonomials K i)) ∘ₗ
    (squareVariables K).toLinearMap ∘ₗ LinearMap.proj i

omit [CharP K 2] in
private theorem mix_apply (p : Fin 8 → Polynomial K) :
    mix K p = ∑ i, headMonomials K i * squareVariables K (p i) := by
  simp [mix]

/-- The eight head polynomials are independent over the squared-variable subring.
Mixed partial derivatives recover their coefficients in descending degree. -/
private theorem mix_injective : Function.Injective (mix K) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  have h : squareVariables K (p 0) + X 0 * squareVariables K (p 1) +
      X 1 * squareVariables K (p 2) + X 2 * squareVariables K (p 3) +
      (X 0 * X 1) * squareVariables K (p 4) +
      (X 0 * X 2 + X 0 ^ 2 * X 1) * squareVariables K (p 5) +
      (X 1 * X 2) * squareVariables K (p 6) +
      (X 0 * X 1 * X 2 + X 2 ^ 2) * squareVariables K (p 7) = 0 := by
    simpa [mix_apply, headMonomials, Fin.sum_univ_succ, add_assoc] using hp
  have h7 : squareVariables K (p 7) = 0 := by
    simpa [pderiv_mul, pderiv_pow, pderiv_squareVariables,
      CharTwo.two_eq_zero] using
      congrArg (fun q => pderiv (0 : Fin 3) (pderiv 1 (pderiv 2 q))) h
  have h5 : squareVariables K (p 5) = 0 := by
    rw [h7, mul_zero, add_zero] at h
    simpa [pderiv_mul, pderiv_pow, pderiv_squareVariables,
      CharTwo.two_eq_zero] using
      congrArg (fun q => pderiv (0 : Fin 3) (pderiv 2 q)) h
  have h6 : squareVariables K (p 6) = 0 := by
    rw [h7, mul_zero, add_zero] at h
    simpa [pderiv_mul, pderiv_pow, pderiv_squareVariables,
      CharTwo.two_eq_zero] using
      congrArg (fun q => pderiv (1 : Fin 3) (pderiv 2 q)) h
  have h4 : squareVariables K (p 4) = 0 := by
    rw [h7, mul_zero, add_zero] at h
    simpa [pderiv_mul, pderiv_pow, pderiv_squareVariables,
      CharTwo.two_eq_zero] using
      congrArg (fun q => pderiv (0 : Fin 3) (pderiv 1 q)) h
  simp only [h7, h6, h5, h4, mul_zero, add_zero] at h
  have h1 : squareVariables K (p 1) = 0 := by
    simpa [pderiv_mul, pderiv_squareVariables] using congrArg (pderiv (0 : Fin 3)) h
  have h2 : squareVariables K (p 2) = 0 := by
    simpa [pderiv_mul, pderiv_squareVariables] using congrArg (pderiv (1 : Fin 3)) h
  have h3 : squareVariables K (p 3) = 0 := by
    simpa [pderiv_mul, pderiv_squareVariables] using congrArg (pderiv (2 : Fin 3)) h
  have h0 : squareVariables K (p 0) = 0 := by simpa [h1, h2, h3] using h
  funext i
  apply squareVariables_injective K
  change squareVariables K (p i) = squareVariables K 0
  rw [map_zero]
  fin_cases i <;> assumption

private def factorCoordinates : (a : Factor) → Space K a →ₗ[K] (Fin 8 → K)
  | .trivial => LinearMap.pi ![LinearMap.id, 0, 0, 0, 0, 0, 0, 0]
  | .natural => LinearMap.pi ![LinearMap.proj 0, LinearMap.proj 1, 0,
      LinearMap.proj 2, 0, 0, 0, 0]
  | .dual => LinearMap.pi ![dualEntry K 2, 0, dualEntry K 1,
      dualEntry K 0, dualEntry K 0, 0, 0, 0]
  | .adjoint => LinearMap.pi ![adjointEntry K 0 2, adjointEntry K 1 2,
      adjointEntry K 0 1, adjointEntry K 1 1,
      adjointEntry K 0 0 + adjointEntry K 1 1,
      adjointEntry K 1 0, adjointEntry K 2 1, adjointEntry K 2 0]

private theorem adjoint_diagonal (v : AdjointSpace K) :
    adjointEntry K 2 2 v = adjointEntry K 0 0 v + adjointEntry K 1 1 v := by
  have ht := v.property
  change LinearMap.trace K (Fin 3 → K) v.val = 0 at ht
  rw [← Matrix.toLin'_toMatrix' v.val, Matrix.trace_toLin'_eq] at ht
  have ht' : adjointEntry K 0 0 v + adjointEntry K 1 1 v + adjointEntry K 2 2 v = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_three, adjointEntry, LinearMap.toMatrix'_apply] using ht
  exact (CharTwo.add_eq_zero.mp ht').symm

private theorem factorCoordinates_injective (a : Factor) :
    Function.Injective (factorCoordinates K a) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hc (i : Fin 8) : factorCoordinates K a v i = 0 := congrFun hv i
  cases a with
  | trivial => exact hc 0
  | natural =>
    change (Fin 3 → K) at v
    funext i
    fin_cases i
    · exact hc 0
    · exact hc 1
    · exact hc 3
  | dual =>
    change Module.Dual K (Fin 3 → K) at v
    apply (Pi.basisFun K (Fin 3)).ext
    intro i
    simp only [Pi.basisFun_apply, LinearMap.zero_apply]
    fin_cases i
    · exact hc 3
    · exact hc 2
    · exact hc 0
  | adjoint =>
    change AdjointSpace K at v
    have h00 : adjointEntry K 0 0 v = 0 := by
      have h4 := hc 4
      change adjointEntry K 0 0 v + adjointEntry K 1 1 v = 0 at h4
      simpa only [show adjointEntry K 1 1 v = 0 from hc 3, add_zero] using h4
    have h22 : adjointEntry K 2 2 v = 0 := by
      rw [adjoint_diagonal K v, h00, show adjointEntry K 1 1 v = 0 from hc 3, add_zero]
    apply Subtype.ext
    apply (Pi.basisFun K (Fin 3)).ext
    intro j
    simp only [Pi.basisFun_apply]
    ext i
    fin_cases i <;> fin_cases j
    · exact h00
    · exact hc 2
    · exact hc 0
    · exact hc 5
    · exact hc 3
    · exact hc 1
    · exact hc 7
    · exact hc 6
    · exact h22

private theorem factorPolynomial_coordinates (a : Factor) (v : Space K a) :
    factorPolynomial K a v = ∑ i, factorCoordinates K a v i • headMonomials K i := by
  cases a with
  | trivial =>
    simp [factorPolynomial, factorCoordinates, headMonomials, Fin.sum_univ_succ,
      Algebra.smul_def]
    rfl
  | natural =>
    simp [factorPolynomial, factorCoordinates, headMonomials, leftRow, Fin.sum_univ_succ]
  | dual =>
    change Module.Dual K (Fin 3 → K) at v
    let c : Fin 3 → K := fun j => dualEntry K j v
    change (∑ j : Fin 3, c j • rightColumn K j) =
      ∑ i : Fin 8, (![c 2, 0, c 1, c 0, c 0, 0, 0, 0] : Fin 8 → K) i • headMonomials K i
    simp [headMonomials, rightColumn, Fin.sum_univ_succ, Algebra.smul_def]
    ring
  | adjoint =>
    change AdjointSpace K at v
    let c : Fin 3 → Fin 3 → K := fun i j => adjointEntry K i j v
    change (∑ i : Fin 3, ∑ j : Fin 3, c i j • (leftRow K i * rightColumn K j)) =
      ∑ i : Fin 8, (![c 0 2, c 1 2, c 0 1, c 1 1, c 0 0 + c 1 1,
        c 1 0, c 2 1, c 2 0] : Fin 8 → K) i • headMonomials K i
    have hd : c 2 2 = c 0 0 + c 1 1 := adjoint_diagonal K v
    simp [headMonomials, leftRow, rightColumn, Fin.sum_univ_succ, hd,
      Algebra.smul_def, map_add]
    ring_nf
    simp [CharTwo.two_eq_zero]

private def tensorCoordinates (a : Factor) (w : List Factor) :
    WordSpace K (a :: w) →ₗ[K] (Fin 8 → Polynomial K) :=
  (TensorProduct.piScalarRight K K (Polynomial K) (Fin 8)).toLinearMap ∘ₗ
    TensorProduct.map (wordPolynomial K w) (factorCoordinates K a) ∘ₗ
      (TensorProduct.comm K (Space K a) (WordSpace K w)).toLinearMap

private theorem wordPolynomial_factorization (a : Factor) (w : List Factor) :
    wordPolynomial K (a :: w) = mix K ∘ₗ tensorCoordinates K a w := by
  apply TensorProduct.ext'
  intro v z
  erw [wordPolynomial_tmul]
  simp [tensorCoordinates, mix_apply,
    factorPolynomial_coordinates, Finset.sum_mul]

/-- The concrete polynomial orbit coefficient embeds every Frobenius tensor word. -/
theorem wordPolynomial_injective (w : List Factor) :
    Function.Injective (wordPolynomial K w) := by
  induction w with
  | nil =>
    change Function.Injective (MvPolynomial.C : K → Polynomial K)
    exact MvPolynomial.C_injective (Fin 3) K
  | cons a w ih =>
    rw [wordPolynomial_factorization]
    apply (mix_injective K).comp
    exact (TensorProduct.piScalarRight K K (Polynomial K) (Fin 8)).injective.comp
      ((TensorProduct.map_injective_of_flat_flat _ _ ih (factorCoordinates_injective K a)).comp
        (TensorProduct.comm K (Space K a) (WordSpace K w)).injective)

end Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
