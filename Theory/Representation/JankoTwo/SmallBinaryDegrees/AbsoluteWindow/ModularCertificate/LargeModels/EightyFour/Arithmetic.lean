module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Arithmetic and orbit recurrences for the degree-84 certificate

Packed XOR sums and row products are interpreted through the canonical map
from the binary field. Orbit recurrences are checked one vector at a time.
The left recurrence uses transposed matrices, hence reverses discovery words.
Source: ATLAS J2G1-f2r84B0, ../source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.EightyFour
open Thompson.BinaryMatrix
open Binary
open Matrix

variable (F : Type*) [Field F] [CharP F 2]

def vector (n : ℕ) (x : ℕ) : Fin n → F :=
  fun j => ZMod.castHom (dvd_refl 2) F (bit x j.val)

def checkAdd (n : ℕ) (a b c : Array ℕ) : Bool :=
  (List.range n).all fun i => a[i]! ^^^ b[i]! == c[i]!

theorem eval_add (n : ℕ) (a b c : Array ℕ) (h : checkAdd n a b c = true) :
    eval F n a + eval F n b = eval F n c := by
  ext i j
  have hi : a[i.val]! ^^^ b[i.val]! = c[i.val]! :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  change _ + _ = (ZMod.castHom (dvd_refl 2) F) (bit c[i.val]! j.val)
  rw [← hi, bit_xor, map_add]
  rfl

def checkOne (n : ℕ) (a : Array ℕ) : Bool :=
  (List.range n).all fun i => a[i]! == 2 ^ i

theorem eval_one (n : ℕ) (a : Array ℕ) (h : checkOne n a = true) : eval F n a = 1 := by
  ext i j
  have hi : a[i.val]! = 2 ^ i.val :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  simp [eval_apply, hi, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]

def checkTranspose (n : ℕ) (a b : Array ℕ) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    a[i]!.testBit j == b[j]!.testBit i

theorem eval_transpose (n : ℕ) (a b : Array ℕ)
    (h : checkTranspose n a b = true) : eval F n a = (eval F n b)ᵀ := by
  ext i j
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have hij : a[i.val]!.testBit j.val = b[j.val]!.testBit i.val :=
    of_decide_eq_true (List.all_eq_true.mp hi j.val (List.mem_range.mpr j.isLt))
  simp only [transpose_apply, eval_apply, hij]

def checkOuter (n : ℕ) (a : Array ℕ) (v l : ℕ) : Bool :=
  (List.range n).all fun i => a[i]! == if v.testBit i then l else 0

theorem eval_outer (n : ℕ) (a : Array ℕ) (v l : ℕ)
    (h : checkOuter n a v l = true) :
    eval F n a = vecMulVec (vector F n v) (vector F n l) := by
  ext i j
  have hi : a[i.val]! = if v.testBit i.val then l else 0 :=
    of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
  simp only [eval_apply, vecMulVec_apply, vector, bit]
  rw [hi]
  cases hv : v.testBit i.val <;> cases hl : l.testBit j.val <;> simp [hl]

theorem vector_rowProduct (n : ℕ) (x : ℕ) (a : Array ℕ) :
    vector F n (rowProduct x a n) = vecMul (vector F n x) (eval F n a) := by
  funext j
  change (ZMod.castHom (dvd_refl 2) F) (bit (rowProduct x a n) j.val) = _
  rw [bit_rowProduct, map_sum]
  simp only [vecMul, dotProduct, vector, eval, RingHom.mapMatrix_apply,
    Matrix.map_apply, decode]
  rw [Fin.sum_univ_eq_sum_range (fun k => (ZMod.castHom (dvd_refl 2) F) (bit x k) * (ZMod.castHom (dvd_refl 2) F) (bit a[k]! j.val))]
  apply Finset.sum_congr rfl
  intro k _
  exact map_mul _ _ _

def checkOrbit (n : ℕ) (a b rows : Array ℕ) (root : ℕ)
    (parents : Array ℕ) (letters : Array Bool) : Bool :=
  (List.range n).all fun i => if i = 0 then rows[i]! == root else
    parents[i]! < i && rowProduct rows[parents[i]!]! (if letters[i]! then b else a) n == rows[i]!

/-- The same checked recurrence can be used with any property closed under its
chosen generator step. In particular this avoids evaluating long orbit words. -/
theorem orbit_induction (n : ℕ) (a b rows : Array ℕ) (root : ℕ)
    (parents : Array ℕ) (letters : Array Bool)
    (h : checkOrbit n a b rows root parents letters = true)
    (P : ℕ → Prop) (hroot : P root)
    (ha : ∀ x, P x → P (rowProduct x a n))
    (hb : ∀ x, P x → P (rowProduct x b n)) :
    ∀ i : Fin n, P rows[i.val]! := by
  suffices hs : ∀ i, i < n → P rows[i]! from fun i => hs i.val i.isLt
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hin
    have hi := List.all_eq_true.mp h i (List.mem_range.mpr hin)
    by_cases hz : i = 0
    · simp only [hz, ↓reduceIte] at hi
      have he : rows[0]! = root := of_decide_eq_true hi
      simpa only [hz, he] using hroot
    · simp only [hz, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hi
      have hj := ih parents[i]! hi.1 (lt_trans hi.1 hin)
      have he : rowProduct rows[parents[i]!]! (if letters[i]! then b else a) n = rows[i]! :=
        of_decide_eq_true hi.2
      rw [← he]
      cases hs : letters[i]!
      · exact ha _ hj
      · exact hb _ hj

/-- Right orbit words multiply in their displayed order. -/
theorem row_reachable (n : ℕ) (a b rows : Array ℕ) (root : ℕ)
    (parents : Array ℕ) (letters : Array Bool)
    (h : checkOrbit n a b rows root parents letters = true)
    (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (ha : eval F n a ∈ S) (hb : eval F n b ∈ S) (i : Fin n) :
    ∃ W ∈ S, vecMul (vector F n root) W = eval F n rows i := by
  apply orbit_induction n a b rows root parents letters h
    (fun x => ∃ W ∈ S, vecMul (vector F n root) W = vector F n x) ?_ ?_ ?_ i
  · exact ⟨1, S.one_mem, Matrix.vecMul_one _⟩
  · intro x hx
    obtain ⟨W, hW, he⟩ := hx
    exact ⟨W * eval F n a, S.mul_mem hW ha, by rw [← vecMul_vecMul, he, ← vector_rowProduct]⟩
  · intro x hx
    obtain ⟨W, hW, he⟩ := hx
    exact ⟨W * eval F n b, S.mul_mem hW hb, by rw [← vecMul_vecMul, he, ← vector_rowProduct]⟩

/-- Transposed row recurrences give left column orbits, with words reversed. -/
theorem column_reachable (n : ℕ) (a b ta tb rows p : Array ℕ) (root : ℕ)
    (parents : Array ℕ) (letters : Array Bool)
    (hat : eval F n ta = (eval F n a)ᵀ)
    (hbt : eval F n tb = (eval F n b)ᵀ)
    (hp : eval F n rows = (eval F n p)ᵀ)
    (h : checkOrbit n ta tb rows root parents letters = true)
    (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (ha : eval F n a ∈ S) (hb : eval F n b ∈ S) (i : Fin n) :
    ∃ W ∈ S, W.mulVec (vector F n root) = fun k => eval F n p k i := by
  have horbit : ∀ i : Fin n, ∃ W ∈ S,
      W.mulVec (vector F n root) = vector F n rows[i.val]! := by
    apply orbit_induction n ta tb rows root parents letters h
      (fun x => ∃ W ∈ S, W.mulVec (vector F n root) = vector F n x)
    · exact ⟨1, S.one_mem, Matrix.one_mulVec _⟩
    · intro x hx
      obtain ⟨W, hW, he⟩ := hx
      refine ⟨eval F n a * W, S.mul_mem ha hW, ?_⟩
      rw [← mulVec_mulVec, he, vector_rowProduct, hat, vecMul_transpose]
    · intro x hx
      obtain ⟨W, hW, he⟩ := hx
      refine ⟨eval F n b * W, S.mul_mem hb hW, ?_⟩
      rw [← mulVec_mulVec, he, vector_rowProduct, hbt, vecMul_transpose]
  obtain ⟨W, hW, he⟩ := horbit i
  refine ⟨W, hW, he.trans ?_⟩
  exact congrFun hp i

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.EightyFour
