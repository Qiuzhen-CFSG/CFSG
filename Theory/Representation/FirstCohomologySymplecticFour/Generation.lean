module
public import Theory.Representation.SymplecticNatural
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Elementary generation of the matrix symplectic four-space

The eight standard type-C₂ root families generate `Matrix.symplecticGroup
(Fin 2) K` over every field. In particular the theorem applies to finite fields
and to the binary field.

The roots are indexed in the following order: upper/lower long roots on the
first coordinate pair (0, 1), upper/lower long roots on the second pair (2, 3),
symmetric upper/lower off-diagonal roots (4, 5), and the two mixed roots (6, 7).
The last two have opposite signs in the two diagonal blocks.

The proof is direct symplectic Gaussian elimination. A nonzero entry in the
first column supplies a pivot, and five root operations normalize that column.
The symplectic equations then fix its paired row. Four more operations normalize
the second column, after a possible pivot change. The remaining matrix is a
symmetric upper unipotent, explicitly a product of three root elements. Only
nonzero pivots are divided by; there are no restrictions on characteristic or
field size.

This supplies the generation input for the natural-module cohomology calculation
in Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma I.1.6(5),
printed p.408. The elimination here takes place entirely in the matrix group.
-/

@[expose] public section
namespace Representation.OneCohomology.SymplecticFour
open Matrix
variable {K : Type*} [Field K]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

/-- The eight standard type-C₂ root matrices, in the order of the two
upper/lower long-root pairs, the upper/lower short roots, and the mixed roots. -/
def rootMatrix (r : Fin 8) (t : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ![fromBlocks 1 (single 0 0 t) 0 1, fromBlocks 1 0 (single 0 0 t) 1,
    fromBlocks 1 (single 1 1 t) 0 1, fromBlocks 1 0 (single 1 1 t) 1,
    fromBlocks 1 (single 0 1 t + single 1 0 t) 0 1,
    fromBlocks 1 0 (single 0 1 t + single 1 0 t) 1,
    fromBlocks (1 + single 0 1 t) 0 0 (1 - single 1 0 t),
    fromBlocks (1 + single 1 0 t) 0 0 (1 - single 0 1 t)] r

/-- Each of the eight matrices preserves the standard alternating form. -/
lemma rootMatrix_mem (r : Fin 8) (t : K) :
    rootMatrix r t ∈ Matrix.symplecticGroup (Fin 2) K := by
  rw [SymplecticGroup.mem_iff]
  fin_cases r <;>
    simp [rootMatrix, Matrix.J, fromBlocks_multiply, fromBlocks_transpose,
      transpose_add, transpose_sub, transpose_single, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub] <;> abel

/-- A standard root element of the matrix symplectic group. -/
def rootElement (r : Fin 8) (t : K) : Matrix.symplecticGroup (Fin 2) K :=
  ⟨rootMatrix r t, rootMatrix_mem r t⟩

private lemma root_mul_apply (r : Fin 8) (t : K)
    (g : Matrix.symplecticGroup (Fin 2) K) (i j : Fin 2 ⊕ Fin 2) :
    (rootElement r t * g).val i j =
    ![Sum.elim ![g.val a j + t * g.val c j, g.val b j] ![g.val c j, g.val d j],
      Sum.elim ![g.val a j, g.val b j] ![g.val c j + t * g.val a j, g.val d j],
      Sum.elim ![g.val a j, g.val b j + t * g.val d j] ![g.val c j, g.val d j],
      Sum.elim ![g.val a j, g.val b j] ![g.val c j, g.val d j + t * g.val b j],
      Sum.elim ![g.val a j + t * g.val d j, g.val b j + t * g.val c j]
        ![g.val c j, g.val d j],
      Sum.elim ![g.val a j, g.val b j]
        ![g.val c j + t * g.val b j, g.val d j + t * g.val a j],
      Sum.elim ![g.val a j + t * g.val b j, g.val b j]
        ![g.val c j, g.val d j - t * g.val c j],
      Sum.elim ![g.val a j, g.val b j + t * g.val a j]
        ![g.val c j - t * g.val d j, g.val d j]] r i := by
  change (rootMatrix r t * g.val) i j = _
  fin_cases r <;> rcases i with i | i <;> fin_cases i <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.one_apply, Matrix.fromBlocks, sub_mul, add_comm]

private lemma pairing_rows (g : Matrix.symplecticGroup (Fin 2) K) (i j : Fin 2 ⊕ Fin 2) :
    g.val i a * g.val j c + g.val i b * g.val j d -
      g.val i c * g.val j a - g.val i d * g.val j b = -Matrix.J (Fin 2) K i j := by
  have h := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M i j) g.property
  simp [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, Matrix.one_apply, Matrix.transpose_apply] at h ⊢
  linear_combination -h

private lemma pairing_cols (g : Matrix.symplecticGroup (Fin 2) K) (i j : Fin 2 ⊕ Fin 2) :
    g.val a i * g.val c j + g.val b i * g.val d j -
      g.val c i * g.val a j - g.val d i * g.val b j = -Matrix.J (Fin 2) K i j :=
  pairing_rows ⟨g.val.transpose, SymplecticGroup.transpose_mem g.property⟩ i j

private lemma row_c (g : Matrix.symplecticGroup (Fin 2) K)
    (h : ∀ i, g.val i a = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i a)
    (j : Fin 2 ⊕ Fin 2) :
    g.val c j = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) c j := by
  have hp := pairing_cols g a j
  simp [h, Matrix.J, Matrix.fromBlocks] at hp
  rcases j with j | j <;> fin_cases j <;> simpa [Matrix.one_apply] using hp

private lemma cancel_root (H : Subgroup (Matrix.symplecticGroup (Fin 2) K))
    (hroot : ∀ r t, rootElement r t ∈ H) (r : Fin 8) (t : K)
    (g : Matrix.symplecticGroup (Fin 2) K) (h : rootElement r t * g ∈ H) : g ∈ H := by
  simpa using H.mul_mem (H.inv_mem (hroot r t)) h

private lemma mem_of_left_columns (H : Subgroup (Matrix.symplecticGroup (Fin 2) K))
    (hroot : ∀ r t, rootElement r t ∈ H) (g : Matrix.symplecticGroup (Fin 2) K)
    (ha : ∀ i, g.val i a = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i a)
    (hb : ∀ i, g.val i b = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i b) :
    g ∈ H := by
  have hc := row_c g ha
  have hd (j : Fin 2 ⊕ Fin 2) :
      g.val d j = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) d j := by
    have hp := pairing_cols g b j
    simp [hb, Matrix.J, Matrix.fromBlocks] at hp
    rcases j with j | j <;> fin_cases j <;> simpa [Matrix.one_apply] using hp
  have hsym : g.val b c = g.val a d := by
    have hp := pairing_cols g c d
    simpa [hc, hd, Matrix.J, Matrix.fromBlocks, sub_eq_zero] using hp
  have heq : g = rootElement 0 (g.val a c) *
      (rootElement 2 (g.val b d) * (rootElement 4 (g.val a d) * 1)) := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp only [root_mul_apply]
    all_goals simp [ha, hb, hc, hd, hsym]
  rw [heq]
  exact H.mul_mem (hroot _ _) (H.mul_mem (hroot _ _) (H.mul_mem (hroot _ _) H.one_mem))

private lemma mem_of_second_pivot (H : Subgroup (Matrix.symplecticGroup (Fin 2) K))
    (hroot : ∀ r t, rootElement r t ∈ H) (g : Matrix.symplecticGroup (Fin 2) K)
    (ha : ∀ i, g.val i a = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i a)
    (hx : g.val b b ≠ 0) : g ∈ H := by
  have hc := row_c g ha
  let g₁ := rootElement 3 ((1 - g.val d b) / g.val b b) * g
  let g₂ := rootElement 2 (1 - g.val b b) * g₁
  let g₃ := rootElement 3 (-1) * g₂
  let g₄ := rootElement 6 (-g.val a b) * g₃
  apply cancel_root H hroot 3 _ g
  apply cancel_root H hroot 2 _ g₁
  apply cancel_root H hroot 3 _ g₂
  apply cancel_root H hroot 6 _ g₃
  apply mem_of_left_columns H hroot g₄
  · intro i
    rcases i with i | i <;> fin_cases i <;>
      simp [g₄, g₃, g₂, g₁, root_mul_apply, ha, Matrix.one_apply]
  · intro i
    rcases i with i | i <;> fin_cases i <;>
      simp [g₄, g₃, g₂, g₁, root_mul_apply, hc, Matrix.one_apply] <;>
      field_simp [hx] <;> ring

private lemma mem_of_first_column (H : Subgroup (Matrix.symplecticGroup (Fin 2) K))
    (hroot : ∀ r t, rootElement r t ∈ H) (g : Matrix.symplecticGroup (Fin 2) K)
    (ha : ∀ i, g.val i a = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i a) :
    g ∈ H := by
  by_cases hx : g.val b b = 0
  · have hc := row_c g ha
    have hy : g.val d b ≠ 0 := by
      intro hy
      have hp := pairing_cols g b d
      simp [hc, hx, hy, Matrix.J, Matrix.fromBlocks] at hp
    apply cancel_root H hroot 2 1 g
    apply mem_of_second_pivot H hroot (rootElement 2 1 * g)
    · intro i
      rcases i with i | i <;> fin_cases i <;>
        simp [root_mul_apply, ha, Matrix.one_apply]
    · simpa [root_mul_apply, hx] using hy
  · exact mem_of_second_pivot H hroot g ha hx

private lemma mem_of_first_pivot (H : Subgroup (Matrix.symplecticGroup (Fin 2) K))
    (hroot : ∀ r t, rootElement r t ∈ H) (g : Matrix.symplecticGroup (Fin 2) K)
    (hx : g.val a a ≠ 0) : g ∈ H := by
  let x := g.val a a
  let y := g.val b a
  let z := g.val c a
  let w := g.val d a
  let g₁ := rootElement 7 (-y / x) * g
  let g₂ := rootElement 5 (-w / x) * g₁
  let g₃ := rootElement 1 ((1 - z - y * w / x) / x) * g₂
  let g₄ := rootElement 0 (1 - x) * g₃
  let g₅ := rootElement 1 (-1) * g₄
  apply cancel_root H hroot 7 _ g
  apply cancel_root H hroot 5 _ g₁
  apply cancel_root H hroot 1 _ g₂
  apply cancel_root H hroot 0 _ g₃
  apply cancel_root H hroot 1 _ g₄
  apply mem_of_first_column H hroot g₅
  intro i
  rcases i with i | i <;> fin_cases i <;>
    simp [g₅, g₄, g₃, g₂, g₁, root_mul_apply, x, y, z, w, Matrix.one_apply] <;>
    field_simp [hx] <;> ring

/-- Every subgroup containing the eight root families is the full symplectic group.
The row elimination works over any field, including the binary field. -/
theorem eq_top_of_rootElement_mem (H : Subgroup (Matrix.symplecticGroup (Fin 2) K))
    (hroot : ∀ r t, rootElement r t ∈ H) : H = ⊤ := by
  apply top_unique
  intro g _
  by_cases ha : g.val a a = 0
  · by_cases hc : g.val c a = 0
    · by_cases hb : g.val b a = 0
      · have hd : g.val d a ≠ 0 := by
          intro hd
          have hp := pairing_cols g a c
          simp [ha, hb, hc, hd, Matrix.J, Matrix.fromBlocks] at hp
        apply cancel_root H hroot 4 1 g
        apply mem_of_first_pivot H hroot
        simpa [root_mul_apply, ha] using hd
      · apply cancel_root H hroot 6 1 g
        apply mem_of_first_pivot H hroot
        simpa [root_mul_apply, ha] using hb
    · apply cancel_root H hroot 0 1 g
      apply mem_of_first_pivot H hroot
      simpa [root_mul_apply, ha] using hc
  · exact mem_of_first_pivot H hroot g ha

/-- The eight standard type-C₂ root matrix families generate `Sp₄(K)`. -/
theorem rootElements_generate :
    Subgroup.closure (Set.range (fun p : Fin 8 × K => rootElement p.1 p.2)) = ⊤ := by
  apply eq_top_of_rootElement_mem
  intro r t
  exact Subgroup.subset_closure ⟨(r, t), rfl⟩

end Representation.OneCohomology.SymplecticFour
