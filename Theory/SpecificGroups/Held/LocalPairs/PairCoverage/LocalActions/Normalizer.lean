module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Plane

/-!
# The normalizer of the diagonal four-group on the ternary plane

Conjugating the sign change on one axis transports its two eigenspaces.
A normalizing automorphism therefore permutes the coordinate axes, so it
is monomial. Conversely the diagonal group and the coordinate swap
normalize the diagonal group. A nonzero vector and its quarter-turn span
the plane, proving irreducibility of the monomial action.

This bounds the full extending image once the inner image of an actual
Held pair has been identified with the diagonal group. It does not require
actors to preserve a particular local overgroup. Source context:
Aschbacher–Smith, printed pp.509–511; GLS3 Table 5.3p.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions
open Subgroup

/-- The two coordinate generators of the plane. -/
def basisVector (i : Fin 2) : Plane :=
  Multiplicative.ofAdd (fun k => if k = i then 1 else 0)

private theorem coordinate_decomposition (x : Plane) :
    basisVector 0 ^ (x.toAdd 0).val * basisVector 1 ^ (x.toAdd 1).val = x := by
  have h : ∀ x : Plane,
      basisVector 0 ^ (x.toAdd 0).val * basisVector 1 ^ (x.toAdd 1).val = x := by
    decide +kernel
  exact h x

/-- Agreement on the two coordinate generators determines a plane automorphism. -/
theorem planeAut_ext {a b : MulAut Plane}
    (h0 : a (basisVector 0) = b (basisVector 0))
    (h1 : a (basisVector 1) = b (basisVector 1)) : a = b := by
  apply MulEquiv.ext
  intro x
  rw [← coordinate_decomposition x, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    h0, h1]

set_option synthInstance.maxSize 1000 in
private theorem eigenbasis (u : Fin 2 → (ZMod 3)ˣ) (x y : Plane)
    (hx : x ≠ 1) (hy : y ≠ 1)
    (hminus : diagonalHom u x = x⁻¹) (hplus : diagonalHom u y = y) :
    ∃ v : Fin 2 → (ZMod 3)ˣ,
      (x = diagonalHom v (basisVector 0) ∧ y = diagonalHom v (basisVector 1)) ∨
      (x = (diagonalHom v * swap) (basisVector 0) ∧
        y = (diagonalHom v * swap) (basisVector 1)) := by
  have h : ∀ (u : Fin 2 → (ZMod 3)ˣ) (x y : Plane), x ≠ 1 → y ≠ 1 →
      diagonalHom u x = x⁻¹ → diagonalHom u y = y →
      ∃ v : Fin 2 → (ZMod 3)ˣ,
        (x = diagonalHom v (basisVector 0) ∧ y = diagonalHom v (basisVector 1)) ∨
        (x = (diagonalHom v * swap) (basisVector 0) ∧
          y = (diagonalHom v * swap) (basisVector 1)) := by
    decide +kernel
  exact h u x y hx hy hminus hplus

/-- The entire automorphism normalizer consists precisely of the monomial actors. -/
theorem normalizer_diagonal_eq_monomial :
    normalizer (diagonal : Set (MulAut Plane)) = monomial := by
  apply le_antisymm
  · intro a ha
    let t := diagonalHom (fun i => if i = 0 then -1 else 1)
    have ht : t ∈ diagonal := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ := (mem_normalizer_iff.mp ha t).mp ht
    have h0 : diagonalHom u (a (basisVector 0)) = (a (basisVector 0))⁻¹ := by
      rw [hu]
      change a (t (a⁻¹ (a (basisVector 0)))) = _
      rw [MulAut.inv_apply_self]
      rw [show t (basisVector 0) = (basisVector 0)⁻¹ from by decide +kernel, map_inv]
    have h1 : diagonalHom u (a (basisVector 1)) = a (basisVector 1) := by
      rw [hu]
      change a (t (a⁻¹ (a (basisVector 1)))) = _
      rw [MulAut.inv_apply_self]
      congr 1
      decide +kernel
    have hn0 : a (basisVector 0) ≠ 1 := by
      rw [← a.map_one, ne_eq, a.injective.eq_iff]
      decide +kernel
    have hn1 : a (basisVector 1) ≠ 1 := by
      rw [← a.map_one, ne_eq, a.injective.eq_iff]
      decide +kernel
    obtain ⟨v, hv⟩ := eigenbasis u _ _ hn0 hn1 h0 h1
    rcases hv with ⟨hv0, hv1⟩ | ⟨hv0, hv1⟩
    · rw [planeAut_ext hv0 hv1]
      exact diagonal_le_monomial ⟨_, rfl⟩
    · rw [planeAut_ext hv0 hv1]
      exact monomial.mul_mem (diagonal_le_monomial ⟨_, rfl⟩)
        ((show zpowers swap ≤ monomial from le_sup_right) (mem_zpowers swap))
  · exact sup_le le_normalizer (zpowers_le.mpr swap_mem_normalizer_diagonal)

set_option synthInstance.maxSize 1000 in
private theorem rotation_spans (x : Plane) (hx : x ≠ 1) (y : Plane) :
    ∃ a b : Fin 3, x ^ a.val * rotation x ^ b.val = y := by
  have h : ∀ x y : Plane, x ≠ 1 →
      ∃ a b : Fin 3, x ^ a.val * rotation x ^ b.val = y := by
    decide +kernel
  exact h x y hx

/-- A nonzero vector and its quarter-turn generate the whole ternary plane. -/
theorem rotation_invariant_subgroup (A : Subgroup Plane)
    (hA : ∀ x ∈ A, rotation x ∈ A) : A = ⊥ ∨ A = ⊤ := by
  by_cases hb : A = ⊥
  · exact Or.inl hb
  right
  apply eq_top_iff.mpr
  obtain ⟨x, hx, hx1⟩ := (A.bot_or_exists_ne_one).resolve_left hb
  intro y _
  obtain ⟨a, b, rfl⟩ := rotation_spans x hx1 y
  exact A.mul_mem (A.pow_mem hx _) (A.pow_mem (hA x hx) _)

/-- The full monomial action has no proper nonzero invariant subgroup. -/
theorem monomial_invariant_subgroup (A : Subgroup Plane)
    (hA : ∀ a ∈ monomial, ∀ x ∈ A, a x ∈ A) : A = ⊥ ∨ A = ⊤ := by
  apply rotation_invariant_subgroup A
  apply hA rotation
  exact monomial.mul_mem (diagonal_le_monomial ⟨_, rfl⟩)
    ((show zpowers swap ≤ monomial from le_sup_right) (mem_zpowers swap))

end Held.LocalPairs.PairCoverage.LocalActions
