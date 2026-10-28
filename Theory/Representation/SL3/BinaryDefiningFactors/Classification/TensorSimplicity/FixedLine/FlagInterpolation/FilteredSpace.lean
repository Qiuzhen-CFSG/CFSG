module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.PolynomialModel
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A cubic spanning bound for flag polynomials

Writing `t = xy+z`, the identity `xy=t-z` straightens each filtered generator
until either its x exponent or its y exponent is zero. At equal weights `(m,m)`,
the two triangular families fit into a cube with `(m+1)^3` entries. This proves
finite dimensionality and the bound used by finite-grid interpolation without
any assumption about irreducible representations.

Source context: GLS III, 2.8.6(a), 2.8.9 and 2.8.10(c), in
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MvPolynomial Matrix.PSL3Even.UnipotentGeometry
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
variable {K : Type*} [Field K]


lemma flagSpace_mono {a b c d : ℕ} (h : a ≤ c) (h' : b ≤ d) :
    flagSpace K a b ≤ flagSpace K c d := by
  apply Submodule.span_mono
  rintro p ⟨i,j,k,l,ha,hb,rfl⟩
  exact ⟨i,j,k,l,ha.trans h,hb.trans h',rfl⟩

lemma mul_mem_flagSpace {a b c d : ℕ} {p q : Polynomial K}
    (hp : p ∈ flagSpace K a b) (hq : q ∈ flagSpace K c d) :
    p * q ∈ flagSpace K (a+c) (b+d) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    induction hq using Submodule.span_induction with
    | mem q hq =>
      rcases hp with ⟨i,j,k,l,ha,hb,rfl⟩
      rcases hq with ⟨i',j',k',l',hc,hd,rfl⟩
      apply Submodule.subset_span
      refine ⟨i+i',j+j',k+k',l+l',by omega,by omega,?_⟩
      simp only [pow_add]
      ring
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [mul_add]
      exact Submodule.add_mem _ ihx ihy
    | smul r x hx ih =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r ih
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [add_mul]
    exact Submodule.add_mem _ ihx ihy
  | smul r x hx ih =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r ih

lemma one_mem_flagSpace_zero : (1 : Polynomial K) ∈ flagSpace K 0 0 := by
  apply Submodule.subset_span
  exact ⟨0,0,0,0,by omega,by omega,by simp⟩

lemma pow_mem_flagSpace {a b : ℕ} {p : Polynomial K} (hp : p ∈ flagSpace K a b) (m : ℕ) :
    p ^ m ∈ flagSpace K (a*m) (b*m) := by
  induction m with
  | zero => simpa using one_mem_flagSpace_zero (K := K)
  | succ m ih =>
    simpa [pow_succ, Nat.mul_succ, Nat.add_comm] using mul_mem_flagSpace ih hp

private def cubePolynomial (m : ℕ) (v : Fin (m+1) × Fin (m+1) × Fin (m+1)) : Polynomial K :=
  if v.1.val + v.2.1.val ≤ m then
    X 0 ^ v.1.val * X 2 ^ v.2.1.val * (X 0 * X 1 + X 2) ^ v.2.2.val
  else
    X 2 ^ v.2.2.val * X 1 ^ (v.1.val + v.2.1.val - m) *
      (X 0 * X 1 + X 2) ^ (m - v.1.val)

private lemma standard_mem_cube (m i j k l : ℕ) (hi : i+j ≤ m) (hk : k+l ≤ m)
    (h : i = 0 ∨ k = 0) :
    X 0 ^ i * X 2 ^ j * X 1 ^ k * (X 0 * X 1 + X 2) ^ l ∈
      Submodule.span K (Set.range (cubePolynomial (K := K) m)) := by
  apply Submodule.subset_span
  by_cases hz : k = 0
  · subst k
    refine ⟨(⟨i,by omega⟩,⟨j,by omega⟩,⟨l,by omega⟩), ?_⟩
    simp [cubePolynomial, hi]
  · have hi0 : i = 0 := h.resolve_right hz
    subst i
    refine ⟨(⟨m-l,by omega⟩,⟨k+l,by omega⟩,⟨j,by omega⟩), ?_⟩
    have hn : ¬ (m-l)+(k+l) ≤ m := by omega
    have he : m-l+(k+l)-m = k := by omega
    have he' : m-(m-l) = l := by omega
    simp [cubePolynomial, hn, he, he']

private lemma monomial_mem_cube (m i j k l : ℕ) (hi : i+j ≤ m) (hk : k+l ≤ m) :
    X 0 ^ i * X 2 ^ j * X 1 ^ k * (X 0 * X 1 + X 2) ^ l ∈
      Submodule.span K (Set.range (cubePolynomial (K := K) m)) := by
  induction i generalizing j k l with
  | zero => exact standard_mem_cube m 0 j k l hi hk (Or.inl rfl)
  | succ i ih =>
    cases k with
    | zero => exact standard_mem_cube m (i+1) j 0 l hi hk (Or.inr rfl)
    | succ k =>
      have h₁ := ih j k (l+1) (by omega) (by omega)
      have h₂ := ih (j+1) k l (by omega) (by omega)
      have he : (X 0 : Polynomial K) ^ (i+1) * X 2 ^ j * X 1 ^ (k+1) *
          (X 0 * X 1 + X 2) ^ l =
          X 0 ^ i * X 2 ^ j * X 1 ^ k * (X 0 * X 1 + X 2) ^ (l+1) -
          X 0 ^ i * X 2 ^ (j+1) * X 1 ^ k * (X 0 * X 1 + X 2) ^ l := by
        simp only [pow_succ]
        ring
      rw [he]
      exact Submodule.sub_mem _ h₁ h₂

private lemma flagSpace_le_cube (m : ℕ) : flagSpace K m m ≤
    Submodule.span K (Set.range (cubePolynomial (K := K) m)) := by
  apply Submodule.span_le.mpr
  rintro p ⟨i,j,k,l,hi,hk,rfl⟩
  exact monomial_mem_cube m i j k l hi hk

instance flagSpace_finiteDimensional (a b : ℕ) : FiniteDimensional K (flagSpace K a b) := by
  let m := max a b
  have h : flagSpace K a b ≤
      Submodule.span K (Set.range (cubePolynomial (K := K) m)) :=
    (flagSpace_mono (Nat.le_max_left _ _) (Nat.le_max_right _ _)).trans (flagSpace_le_cube m)
  let := FiniteDimensional.span_of_finite K (Set.finite_range (cubePolynomial (K := K) m))
  exact FiniteDimensional.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

lemma finrank_flagSpace_le_cube (m : ℕ) : Module.finrank K (flagSpace K m m) ≤ (m+1)^3 := by
  let := FiniteDimensional.span_of_finite K (Set.finite_range (cubePolynomial (K := K) m))
  refine (Submodule.finrank_mono (flagSpace_le_cube m)).trans ?_
  have h := finrank_range_le_card (R := K) (cubePolynomial (K := K) m)
  simpa [Set.finrank, Fintype.card_prod, Fintype.card_fin, pow_succ, mul_assoc] using h
end Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
