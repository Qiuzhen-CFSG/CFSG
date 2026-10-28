module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Cyclic

/-!
# Checked cyclic and generator orbits

Strong induction recovers each generator word from an earlier-parent
certificate. Left column orbits use transposed raw row matrices. A separate
successor recurrence identifies the cyclic rows v C^i; together with a
checked inverse these supply the cyclic-centralizer lemma. The concrete
applications are the ATLAS degree-220 M24 pairs, attributed in source/README.md.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Packed
open Matrix

def checkCyclic (n c rows seed : ℕ) : Bool :=
  (rowAt n rows 0 == seed) && (List.range (n-1)).all fun i =>
    row n (rowAt n rows i) c n == rowAt n rows (i+1)

theorem cyclic_sound (n c rows seed : ℕ) (h : checkCyclic n c rows seed = true) :
    ∀ i : Fin n, decodePacked n rows i =
      vecMul (vector n seed) ((decodePacked n c) ^ i.val) := by
  simp only [checkCyclic, Bool.and_eq_true, beq_iff_eq] at h
  have hs : ∀ k, k < n → vector n (rowAt n rows k) =
      vecMul (vector n seed) ((decodePacked n c) ^ k) := by
    intro k
    induction k with
    | zero => intro _; rw [h.1, pow_zero, vecMul_one]
    | succ k ih =>
      intro hk
      have hp : k < n - 1 := by omega
      have he : row n (rowAt n rows k) c n = rowAt n rows (k+1) :=
        of_decide_eq_true (List.all_eq_true.mp h.2 k (List.mem_range.mpr hp))
      rw [← he, vector_row, ih (by omega), pow_succ, vecMul_vecMul]
  intro i
  exact hs i.val i.isLt

def checkOrbit (n a b rows root : ℕ) (parents : Array ℕ) (letters : Array Bool) : Bool :=
  (List.range n).all fun i => if i = 0 then rowAt n rows i == root else
    parents[i]! < i &&
      row n (rowAt n rows parents[i]!) (if letters[i]! then b else a) n == rowAt n rows i

theorem orbit_induction (n a b rows root : ℕ) (parents : Array ℕ) (letters : Array Bool)
    (h : checkOrbit n a b rows root parents letters = true)
    (P : ℕ → Prop) (hroot : P root)
    (ha : ∀ x, P x → P (row n x a n))
    (hb : ∀ x, P x → P (row n x b n)) :
    ∀ i : Fin n, P (rowAt n rows i.val) := by
  suffices hs : ∀ i, i < n → P (rowAt n rows i) from fun i => hs i.val i.isLt
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hin
    have hi := List.all_eq_true.mp h i (List.mem_range.mpr hin)
    by_cases hz : i = 0
    · simp only [hz, ↓reduceIte] at hi
      have he : rowAt n rows 0 = root := of_decide_eq_true hi
      simpa only [hz, he] using hroot
    · simp only [hz, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hi
      have hj := ih parents[i]! hi.1 (lt_trans hi.1 hin)
      have he : row n (rowAt n rows parents[i]!) (if letters[i]! then b else a) n =
          rowAt n rows i := of_decide_eq_true hi.2
      rw [← he]
      cases hs : letters[i]!
      · exact ha _ hj
      · exact hb _ hj

theorem row_reachable (n a b rows root : ℕ) (parents : Array ℕ) (letters : Array Bool)
    (h : checkOrbit n a b rows root parents letters = true)
    (S : Subalgebra (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (ha : decodePacked n a ∈ S) (hb : decodePacked n b ∈ S) (i : Fin n) :
    ∃ W ∈ S, vecMul (vector n root) W = decodePacked n rows i := by
  apply orbit_induction n a b rows root parents letters h
    (fun x => ∃ W ∈ S, vecMul (vector n root) W = vector n x) ?_ ?_ ?_ i
  · exact ⟨1, S.one_mem, Matrix.vecMul_one _⟩
  · intro x hx
    obtain ⟨W, hW, he⟩ := hx
    exact ⟨W * decodePacked n a, S.mul_mem hW ha,
      by rw [← vecMul_vecMul, he, ← vector_row]⟩
  · intro x hx
    obtain ⟨W, hW, he⟩ := hx
    exact ⟨W * decodePacked n b, S.mul_mem hW hb,
      by rw [← vecMul_vecMul, he, ← vector_row]⟩

theorem column_reachable (n a b rows p root : ℕ) (parents : Array ℕ) (letters : Array Bool)
    (hp : decodePacked n rows = (decodePacked n p).transpose)
    (h : checkOrbit n a b rows root parents letters = true)
    (S : Subalgebra (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (ha : (decodePacked n a).transpose ∈ S)
    (hb : (decodePacked n b).transpose ∈ S) (i : Fin n) :
    ∃ W ∈ S, W.mulVec (vector n root) = fun k => decodePacked n p k i := by
  have horbit : ∀ i : Fin n, ∃ W ∈ S,
      W.mulVec (vector n root) = vector n (rowAt n rows i.val) := by
    apply orbit_induction n a b rows root parents letters h
      (fun x => ∃ W ∈ S, W.mulVec (vector n root) = vector n x)
    · exact ⟨1, S.one_mem, Matrix.one_mulVec _⟩
    · intro x hx
      obtain ⟨W, hW, he⟩ := hx
      refine ⟨(decodePacked n a).transpose * W, S.mul_mem ha hW, ?_⟩
      rw [← mulVec_mulVec, he, vector_row, ← vecMul_transpose, transpose_transpose]
    · intro x hx
      obtain ⟨W, hW, he⟩ := hx
      refine ⟨(decodePacked n b).transpose * W, S.mul_mem hb hW, ?_⟩
      rw [← mulVec_mulVec, he, vector_row, ← vecMul_transpose, transpose_transpose]
  obtain ⟨W, hW, he⟩ := horbit i
  refine ⟨W, hW, he.trans ?_⟩
  exact congrFun hp i

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Packed
