module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.Reduction

/-!
# The semilinear subgroup normalizes the root torus

The graph involution swaps the two diagonal scalars and Frobenius squares
them. Hence the literal semilinear subgroup normalizes the torus and its join
with the inner automorphisms. These identities supply the semilinear factor
in the full root-automorphism normalizer argument.

Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.3, 46.14.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
noncomputable section

theorem graph_square : graph * graph = 1 := by
  apply MulEquiv.ext
  intro q
  apply SylowModel.U.ext
  · rfl
  · rfl
  · change q.y * q.x - (q.x * q.y - q.c) = q.c
    ring

theorem graph_diagonal_swap (a : Fˣ × Fˣ) :
    graph * diagonalHom a = diagonalHom (a.2, a.1) * graph := by
  apply MulEquiv.ext
  intro q
  apply SylowModel.U.ext
  · rfl
  · rfl
  · change ((a.1 : F) * q.x) * ((a.2 : F) * q.y) -
      ((a.1 * a.2 : F) * q.c) = (a.2 * a.1 : F) * (q.x * q.y - q.c)
    ring

theorem frob_diagonal_square (a : Fˣ × Fˣ) :
    SylowModel.frob * diagonalHom a =
      diagonalHom (a.1 ^ 2, a.2 ^ 2) * SylowModel.frob := by
  apply MulEquiv.ext
  intro q
  apply SylowModel.U.ext
  · change fieldFrobenius ((a.1 : F) * q.x) = (↑(a.1 ^ 2) : F) * fieldFrobenius q.x
    simp [mul_pow]
  · change fieldFrobenius ((a.2 : F) * q.y) = (↑(a.2 ^ 2) : F) * fieldFrobenius q.y
    simp [mul_pow]
  · change fieldFrobenius ((a.1 * a.2 : F) * q.c) =
      ((↑(a.1 ^ 2) : F) * ↑(a.2 ^ 2)) * fieldFrobenius q.c
    simp [mul_pow]

private theorem involution_normalizes_torus (s : MulAut Root) (hs : s * s = 1)
    (h : ∀ a : Fˣ × Fˣ, ∃ b : Fˣ × Fˣ, s * diagonalHom a = diagonalHom b * s) :
    s ∈ normalizer (torus : Set (MulAut Root)) := by
  have hi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hc (t : MulAut Root) (ht : t ∈ torus) : s * t * s⁻¹ ∈ torus := by
    obtain ⟨a, rfl⟩ := ht
    obtain ⟨b, hb⟩ := h a
    rw [hb, mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨b, rfl⟩
  apply mem_normalizer_iff.mpr
  intro t
  refine ⟨hc t, fun ht => ?_⟩
  have hh := hc _ ht
  simp only [hi, ← mul_assoc, hs, one_mul] at hh
  simpa only [mul_assoc, hs, mul_one] using hh

theorem semilinear_le_normalizer_torus :
    semilinear ≤ normalizer (torus : Set (MulAut Root)) := by
  apply sup_le
  · apply sup_le torus.le_normalizer
    apply zpowers_le.mpr
    exact involution_normalizes_torus graph graph_square
      (fun a => ⟨(a.2, a.1), graph_diagonal_swap a⟩)
  · apply zpowers_le.mpr
    exact involution_normalizes_torus SylowModel.frob
      (by simpa only [pow_two] using SylowModel.frob_sq)
      (fun a => ⟨(a.1 ^ 2, a.2 ^ 2), frob_diagonal_square a⟩)

theorem semilinear_le_normalizer_innerTorus :
    semilinear ≤ normalizer (innerTorus : Set (MulAut Root)) := by
  have h : normalizer (torus : Set (MulAut Root)) ≤
      normalizer ((torus ⊔ inner : Subgroup (MulAut Root)) : Set (MulAut Root)) :=
    normalizer_le_normalizer_sup_normal
  simpa only [innerTorus, sup_comm torus inner] using semilinear_le_normalizer_torus.trans h

end
end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
