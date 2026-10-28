module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CertificateInterface
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate

/-!
# Binary simplicity from a small image and orbit bases

A row of a generated-algebra element detects every nonzero invariant subspace
when its dual orbit spans. A nonzero image vector then generates the whole
space when its column orbit spans. Over F₂ a two-dimensional image has only
three nonzero vectors, so three orbit bases suffice without absolute
irreducibility. Packed orbit inverses are interpreted by the existing
Hermitian-filtration arithmetic API.

Application: the literal binary adjoint M22 factors used in Guralnick--Malle I,
Proposition 5.1, pp.15--16; Aschbacher--Smith, printed pp.451--452 and 457.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.SimpleFactors

open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.MatrixChecks

open Certificate

/-- Matrices preserving one binary subspace form an algebra. -/
def preserving {n : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Subalgebra (ZMod 2) (Mat n) where
  carrier := {M | ∀ x ∈ W, M.mulVec x ∈ W}
  zero_mem' := by intro x _; simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' := by intro M N hM hN x hx; simpa only [add_mulVec] using W.add_mem (hM x hx) (hN x hx)
  mul_mem' := by intro M N hM hN x hx; simpa only [← mulVec_mulVec] using hM _ (hN x hx)
  algebraMap_mem' := by
    intro r x hx
    simpa only [Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec] using W.smul_mem r hx

/-- A seed is cyclic for the two specified column actions. -/
def Cyclic {n : ℕ} (A : Fin 2 → Mat n) (u : Fin n → ZMod 2) : Prop :=
  ∀ W : Submodule (ZMod 2) (Fin n → ZMod 2),
    (∀ j, A j ∈ preserving W) → u ∈ W → W = ⊤

/-- A dual orbit detects each nonzero invariant subspace. -/
def Detects {n : ℕ} (A : Fin 2 → Mat n) (r : Fin n → ZMod 2) : Prop :=
  ∀ W : Submodule (ZMod 2) (Fin n → ZMod 2),
    (∀ j, A j ∈ preserving W) → (∀ x ∈ W, r ⬝ᵥ x = 0) → W = ⊥

/-- The checked predecessor tree and inverse exhibit a cyclic vector. -/
theorem cyclic_of_orbit {m : ℕ} (A : Fin 2 → Mat (m+1))
    (xs xi : List ℕ) (p : Fin m → Fin (m+1)) (a : Fin m → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, (A (a i)).mulVec (vector (entry xs (p i).val)) =
      vector (entry xs i.succ.val))
    (hlen : xs.length = m+1)
    (hi : ∀ i : Fin (m+1), combineList xs (entry xi i.val) = 2 ^ i.val) :
    Cyclic A (vector (entry xs 0)) := by
  intro W hA hu
  have hmem : ∀ i : Fin (m+1), vector (entry xs i.val) ∈ W := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      cases i using Fin.cases with
      | zero => exact hu
      | succ i => rw [← hs i]; exact hA (a i) _ (ih (p i) (hp i))
  apply top_unique
  rw [← span_rows_of_inverse xs xi hlen hi]
  exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)

/-- The checked dual predecessor tree and inverse give detection. -/
theorem detects_of_orbit {m : ℕ} (A : Fin 2 → Mat (m+1))
    (xs xi : List ℕ) (p : Fin m → Fin (m+1)) (a : Fin m → Fin 2)
    (hp : ∀ i, p i < i.succ)
    (hs : ∀ i, vecMul (vector (entry xs (p i).val)) (A (a i)) =
      vector (entry xs i.succ.val))
    (hlen : xs.length = m+1)
    (hi : ∀ i : Fin (m+1), combineList xs (entry xi i.val) = 2 ^ i.val) :
    Detects A (vector (entry xs 0)) := by
  intro W hA hr
  have hzero : ∀ i : Fin (m+1), ∀ x ∈ W, vector (entry xs i.val) ⬝ᵥ x = 0 := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      cases i using Fin.cases with
      | zero => exact hr
      | succ i =>
        intro x hx
        rw [← hs i, ← dotProduct_mulVec]
        exact ih (p i) (hp i) _ (hA (a i) x hx)
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply dotProduct_eq_zero
  intro y
  have hy : y ∈ Submodule.span (ZMod 2) (Set.range (matrix (n := m+1) xs)) := by
    rw [span_rows_of_inverse xs xi hlen hi]; trivial
  have h : y ⬝ᵥ x = 0 := by
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hzero i x hx
    | zero => exact zero_dotProduct x
    | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_dotProduct, hy, smul_zero]
  rwa [dotProduct_comm] at h

/-- A detecting row supplies a nonzero image inside a nonzero invariant subspace. -/
theorem exists_nonzero_image {n : ℕ} (A : Fin 2 → Mat n) (P : Mat n)
    (r : Fin n) (hd : Detects A (P r))
    (W : Submodule (ZMod 2) (Fin n → ZMod 2)) (hA : ∀ j, A j ∈ preserving W)
    (hW : W ≠ ⊥) : ∃ x ∈ W, P.mulVec x ≠ 0 := by
  by_contra h
  push Not at h
  apply hW
  apply hd W hA
  intro x hx
  exact congrFun (h x hx) r

/-- A rank-two binary image has just three possible nonzero vectors. -/
theorem rank_two_simple {n : ℕ} (A : Fin 2 → Mat n)
    (u v r s : Fin n → ZMod 2)
    (hP : ∀ Q : Subalgebra (ZMod 2) (Mat n), (∀ j, A j ∈ Q) →
      vecMulVec u r + vecMulVec v s ∈ Q)
    (i : Fin n) (hd : Detects A ((vecMulVec u r + vecMulVec v s) i))
    (hu : Cyclic A u) (hv : Cyclic A v) (huv : Cyclic A (u+v)) :
    ∀ W : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ j, A j ∈ preserving W) → W = ⊥ ∨ W = ⊤ := by
  intro W hA
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨x, hx, hn⟩ := exists_nonzero_image A _ i hd W hA hW
  have hm := hP (preserving W) hA x hx
  have hb (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide +kernel
  rw [add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec] at hm hn
  rcases hb (r ⬝ᵥ x) with hr | hr <;> rcases hb (s ⬝ᵥ x) with hs | hs
  · simp [hr, hs] at hn
  · exact hv W hA (by simpa [hr, hs] using hm)
  · exact hu W hA (by simpa [hr, hs] using hm)
  · exact huv W hA (by simpa [hr, hs] using hm)

/-- Full matrix-algebra density implies simplicity of invariant subspaces. -/
theorem simple_of_full {n : ℕ} (A : Fin 2 → Mat n)
    (hfull : ∀ Q : Subalgebra (ZMod 2) (Mat n), (∀ j, A j ∈ Q) → Q = ⊤) :
    ∀ W : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ j, A j ∈ preserving W) → W = ⊥ ∨ W = ⊤ := by
  intro W hA
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  have hQ := hfull (preserving W) hA
  obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  have hi1 : x i = 1 := by
    have hb : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    exact (hb (x i)).resolve_left hi
  apply top_unique
  intro y _
  have hM : vecMulVec y (Pi.single i 1) ∈ preserving W := by rw [hQ]; trivial
  have h := hM x hx
  simpa [vecMulVec_mulVec, hi1] using h

/-- Packed rows of the certificate are compared to the literal saved columns. -/
theorem factorMatrix_entry_shift (t : Factor) (j : Fin 2) (x y : Fin (degree t)) :
    Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.bit
      ((actionColumns j)[(blockIndex t y).val]! >>> cut t.val) x.val =
      factorMatrix t j x y := by
  simp only [Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.bit,
    bit, Nat.testBit_shiftRight, factorMatrix, actionMatrix, blockIndex]
  rfl

/-- A packed sum of two outer products is a genuine rank-at-most-two operator. -/
theorem rankTwo_eq {n : ℕ} (xs : List ℕ) (u v r s : ℕ)
    (h : ∀ i : Fin n, entry xs i.val =
      (if u.testBit i.val then r else 0) ^^^ (if v.testBit i.val then s else 0)) :
    matrix (n := n) xs = vecMulVec (vector u) (vector r) + vecMulVec (vector v) (vector s) := by
  ext i j
  change Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.bit (entry xs i.val) j.val = _
  rw [h i, bit_xor]
  simp only [Matrix.add_apply, vecMulVec_apply, vector,
    Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.bit]
  cases u.testBit i.val <;> cases v.testBit i.val <;> simp

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.SimpleFactors
