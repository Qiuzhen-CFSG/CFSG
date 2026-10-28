module

public import Theory.GroupTheory.PGroup.HomocyclicMatrixCongruence

/-!
# Involutory homocyclic automorphisms fixing four-torsion

For a group identified with two cyclic groups of order `2 ^ n`, with `n ≥ 3`,
an involutory automorphism fixing four-torsion commutes with every automorphism
fixing two-torsion. Every element it inverts has square one.

The coordinate calculation in `HomocyclicMatrixCongruence` proves that the
matrix of this automorphism is `I + 2^(n-1) M`. This module exposes its two
consequences in the group-theoretic form used by the normal-abelian reduction.
In particular, neither conclusion needs an ambient group or a restriction on
normal elementary abelian subgroups.

Source context: the homocyclic case of the MacWilliams–Sah bound quoted by
Janko–Thompson, Math. Z. 113 (1970), 1.1, printed p.385; see
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
The coordinate proof is self-contained in the imported module.
-/

namespace IsPGroup

/-- An involutory homocyclic automorphism fixing four-torsion centralizes all
automorphisms fixing two-torsion, and inverts only elements of square one. -/
public theorem deep_involution_of_homocyclic_fixing_four_torsion
    {D : Type*} [Group D] [Finite D] [IsMulCommutative D]
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (a : MulAut D) (ha : a ^ 2 = 1) (hfour : ∀ d : D, d ^ 4 = 1 → a d = d) :
    (∀ b : MulAut D, (∀ d : D, d ^ 2 = 1 → b d = d) → Commute b a) ∧
      (∀ d : D, a d = d⁻¹ → d ^ 2 = 1) := by
  obtain ⟨hcomm, hinv⟩ :=
    HomocyclicMatrixCongruence.deep_involution_of_equiv_prod_zmod n hn e a ha hfour
  exact ⟨fun b hb => (hcomm b hb).symm, hinv⟩

end IsPGroup
