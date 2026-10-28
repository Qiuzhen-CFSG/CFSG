module

public import Theory.LinearAlgebra.BinaryTriangularPGroup
public import Mathlib.GroupTheory.Index

/-!
# Order divisibility from a faithful binary block action

For a representation preserving a linearly ordered block flag, taking the
simultaneous diagonal blocks is multiplicative. If the block labels increase
with the coordinates, its kernel is lower triangular over GF(2), hence a
two-group. The kernel-index formula then bounds the odd part of the source
order by that of the simultaneous diagonal image.

The concrete consumer is the literal J4 max4 matrix subgroup in
`OrderBound.lean`. Its source context is Aschbacher--Smith, printed p.511,
and the ATLAS program attributed in `SymmetricLinear.Model`.
-/

@[expose] public section

namespace Matrix
variable {n : ℕ}

def blockDiagonalPart (b : Fin n → ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2) := fun i j => if b i = b j then M i j else 0

lemma blockDiagonalPart_one (b : Fin n → ℕ) : blockDiagonalPart b 1 = 1 := by
  ext i j
  by_cases h : i = j
  · subst j; simp [blockDiagonalPart]
  · simp [blockDiagonalPart, h]

lemma blockDiagonalPart_mul (b : Fin n → ℕ)
    (M N : Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : M.BlockTriangular (OrderDual.toDual ∘ b))
    (hN : N.BlockTriangular (OrderDual.toDual ∘ b)) :
    blockDiagonalPart b (M * N) = blockDiagonalPart b M * blockDiagonalPart b N := by
  ext i j
  by_cases hij : b i = b j
  · simp only [blockDiagonalPart, hij, if_true, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : b i = b k
    · simp [hik, ← hij]
    · have hkj : b k ≠ b j := fun h => hik (hij.trans h.symm)
      simp only [hkj, if_false, mul_zero]
      rcases lt_or_gt_of_ne hik with h | h
      · rw [hM h, zero_mul]
      · rw [hN (h.trans_eq hij), mul_zero]
  · simp only [blockDiagonalPart, hij, if_false, Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : b i = b k
    · have hkj : b k ≠ b j := fun h => hij (hik.trans h)
      simp [hkj]
    · simp [hik]

end Matrix

namespace BinaryBlockOrder
variable {G : Type*} [Group G] {n : ℕ} [NeZero n]
variable (f : G →* Matrix (Fin n) (Fin n) (ZMod 2))
variable (b : Fin n → ℕ)
variable (ht : ∀ g, (f g).BlockTriangular (OrderDual.toDual ∘ b))

omit [NeZero n] in
/-- A finite generated matrix group preserves a flag when its generators do. -/
lemma triangular_of_generators [Finite G] (S : Set G)
    (hS : Subgroup.closure S = ⊤)
    (hs : ∀ g ∈ S, (f g).BlockTriangular (OrderDual.toDual ∘ b))
    (g : G) : (f g).BlockTriangular (OrderDual.toDual ∘ b) := by
  let K : Subgroup G :=
    { carrier := {x | (f x).BlockTriangular (OrderDual.toDual ∘ b)}
      one_mem' := by
        change (f 1).BlockTriangular _
        rw [map_one]
        exact Matrix.blockTriangular_one
      mul_mem' := by
        intro x y hx hy
        change (f (x * y)).BlockTriangular _
        rw [map_mul]
        exact hx.mul hy
      inv_mem' := by
        intro x hx
        have hi : x⁻¹ = x ^ (Nat.card G - 1) :=
          inv_eq_of_mul_eq_one_right (by
            rw [mul_pow_sub_one Nat.card_pos.ne', pow_card_eq_one'])
        change (f x⁻¹).BlockTriangular _
        rw [hi, map_pow]
        exact hx.pow _ }
  have hle : Subgroup.closure S ≤ K := (Subgroup.closure_le K).mpr hs
  exact hle (hS ▸ Subgroup.mem_top g)

def diagonalMatrixHom : G →* Matrix (Fin n) (Fin n) (ZMod 2) where
  toFun g := Matrix.blockDiagonalPart b (f g)
  map_one' := by rw [map_one, Matrix.blockDiagonalPart_one]
  map_mul' g h := by rw [map_mul, Matrix.blockDiagonalPart_mul b _ _ (ht g) (ht h)]

def diagonalHom : G →* (Matrix (Fin n) (Fin n) (ZMod 2))ˣ :=
  (diagonalMatrixHom f b ht).toHomUnits

lemma kernel_isPGroup (hf : Function.Injective f) (hb : Monotone b) :
    IsPGroup 2 (diagonalHom f b ht).ker := by
  apply IsPGroup.of_injective_binary_lowerTriangular
    (f.comp (diagonalHom f b ht).ker.subtype)
    (hf.comp Subtype.val_injective)
  intro g i j hij
  change f (g : G) i j = 0
  rcases (hb hij.le).lt_or_eq with hlt | heq
  · exact ht g hlt
  · have he : Matrix.blockDiagonalPart b (f (g : G)) = 1 :=
      congrArg Units.val g.property
    have hv := congrFun (congrFun he i) j
    simpa [Matrix.blockDiagonalPart, heq, Matrix.one_apply, ne_of_lt hij] using hv

lemma card_dvd_twoPower_mul [Finite G] (hf : Function.Injective f) (hb : Monotone b)
    {m : ℕ} (hc : Nat.card (diagonalHom f b ht).range ∣ m) :
    ∃ k : ℕ, Nat.card G ∣ 2 ^ k * m := by
  obtain ⟨k, hk⟩ := (kernel_isPGroup f b ht hf hb).exists_card_eq
  refine ⟨k, ?_⟩
  have he := (diagonalHom f b ht).ker.card_mul_index
  rw [Subgroup.index_ker, hk] at he
  rw [← he]
  exact Nat.mul_dvd_mul_left _ hc
end BinaryBlockOrder
