module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Arithmetic

/-!
# Low-rank detection of simple binary matrix actions

A cyclic dual vector detects a nonzero vector in every nonzero invariant
subspace. A preserved operator of rank at most two sends that detected vector
to one of two specified cyclic vectors. Either vector then generates the
whole space. The degree-32 application needs rank two because its commuting
field is F₄; the proof does not assert absolute irreducibility.
The certificates below are used for James's M₁₁ eleven-coset factors.
-/

public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity
open Matrix

variable {n : ℕ}

@[expose] def Preserves (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop := ∀ v ∈ U, M.mulVec v ∈ U

theorem preserves_one (U : Submodule (ZMod 2) (Fin n → ZMod 2)) : Preserves U 1 := by
  intro v hv
  simpa only [one_mulVec] using hv

theorem preserves_add {U : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {A B : Matrix (Fin n) (Fin n) (ZMod 2)}
    (ha : Preserves U A) (hb : Preserves U B) : Preserves U (A + B) := by
  intro v hv
  rw [add_mulVec]
  exact U.add_mem (ha v hv) (hb v hv)

theorem preserves_mul {U : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {A B : Matrix (Fin n) (Fin n) (ZMod 2)}
    (ha : Preserves U A) (hb : Preserves U B) : Preserves U (A * B) := by
  intro v hv
  rw [← mulVec_mulVec]
  exact ha _ (hb v hv)

theorem preserves_packed_mul {U : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (a b c : Fin n → ℕ) (ha : Preserves U (matrix a))
    (hb : Preserves U (matrix b)) (h : product a b = c) :
    Preserves U (matrix c) := by
  rw [← h, matrix_product]
  exact preserves_mul ha hb

theorem preserves_packed_add {U : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (a b c : Fin n → ℕ) (ha : Preserves U (matrix a))
    (hb : Preserves U (matrix b)) (h : plus a b = c) :
    Preserves U (matrix c) := by
  rw [← h, matrix_plus]
  exact preserves_add ha hb

/-- A checked orbit basis supplies all vectors of the invariant subspace. -/
theorem eq_top_of_column_orbit
    (U : Submodule (ZMod 2) (Fin (n+1) → ZMod 2))
    (A : Fin 2 → Fin (n+1) → ℕ) (hA : ∀ s, Preserves U (matrix (A s)))
    (cols ci : Fin (n+1) → ℕ) (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, act (A (a i)) (cols (p i)) = cols i.succ)
    (hi : product cols ci = identity (n+1))
    (hseed : vector (cols 0) ∈ U) : U = ⊤ := by
  have hmem (i : Fin (n+1)) : vector (cols i) ∈ U := by
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      cases i using Fin.cases with
      | zero => exact hseed
      | succ j =>
        rw [← hs j, vector_act]
        exact hA (a j) _ (ih (p j) (hp j))
  apply top_unique
  intro v _
  have hv : (matrix cols).mulVec ((matrix ci).mulVec v) = v := by
    rw [mulVec_mulVec, product_eq_one cols ci hi, one_mulVec]
  rw [← hv, mulVec_eq_sum]
  simp only [op_smul_eq_smul]
  exact U.sum_mem fun j _ => U.smul_mem _ (hmem j)

/-- Only two nonzero images need to be cyclic, even for a rank-two operator. -/
theorem top_of_peak
    (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (P : Matrix (Fin n) (Fin n) (ZMod 2)) (hP : Preserves U P)
    (u w r t : Fin n → ZMod 2)
    (he : P = vecMulVec u r + vecMulVec w t)
    (hu : u ∈ U → U = ⊤) (hw : u + w ∈ U → U = ⊤)
    (v : Fin n → ZMod 2) (hv : v ∈ U) (hr : r ⬝ᵥ v ≠ 0) : U = ⊤ := by
  have binary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hfirst : r ⬝ᵥ v = 1 := (binary _).resolve_left hr
  have hmem := hP v hv
  rw [he, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec] at hmem
  simp only [op_smul_eq_smul, hfirst, one_smul] at hmem
  rcases binary (t ⬝ᵥ v) with h | h
  · exact hu (by simpa only [h, zero_smul, add_zero] using hmem)
  · exact hw (by simpa only [h, one_smul] using hmem)

/-- The cyclic dual basis ensures that a peak functional detects every
nonzero invariant subspace. -/
theorem simple_of_row_orbit
    (U : Submodule (ZMod 2) (Fin (n+1) → ZMod 2))
    (A AT : Fin 2 → Fin (n+1) → ℕ)
    (hA : ∀ s, Preserves U (matrix (A s)))
    (hAT : ∀ s, matrix (m := n+1) (AT s) = (matrix (A s)).transpose)
    (rows ri : Fin (n+1) → ℕ) (p : Fin n → Fin (n+1)) (a : Fin n → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, act (AT (a i)) (rows (p i)) = rows i.succ)
    (hi : product rows ri = identity (n+1))
    (hbase : ∀ v ∈ U, vector (rows 0) ⬝ᵥ v ≠ 0 → U = ⊤) : U = ⊥ ∨ U = ⊤ := by
  have extract (i : Fin (n+1)) :
      ∀ v ∈ U, vector (rows i) ⬝ᵥ v ≠ 0 → U = ⊤ := by
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      cases i using Fin.cases with
      | zero => exact hbase
      | succ j =>
        intro v hv hn
        rw [← hs j, vector_act, hAT, mulVec_transpose, ← dotProduct_mulVec] at hn
        exact ih (p j) (hp j) _ (hA (a j) v hv) hn
  by_cases hu : U = ⊥
  · exact Or.inl hu
  right
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hu
  have hex : ∃ i, vector (rows i) ⬝ᵥ v ≠ 0 := by
    by_contra! h
    have hr : (matrix rows).transpose.mulVec v = 0 := funext h
    have he := congrArg (fun w => (matrix ri).transpose.mulVec w) hr
    rw [mulVec_mulVec, ← transpose_mul, product_eq_one rows ri hi,
      transpose_one, one_mulVec, mulVec_zero] at he
    exact hn he
  obtain ⟨i, hi⟩ := hex
  exact extract i v hv hi

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity
