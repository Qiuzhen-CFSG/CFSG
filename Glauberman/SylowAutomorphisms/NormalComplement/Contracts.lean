module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The odd-actor displacement subgroup

The normal-complement proof starts with an odd-order automorphism normalizing
a nonzero elementary abelian two-subgroup on which its displacement map is
surjective. This is local action data, not a normal-complement or solvability
assumption. The normalizer construction and the exclusion of these data in a
Sylow pointwise fixer are independent proof obligations.

Source: Glauberman, “On the automorphism group of a finite group having no
non-identity normal subgroups of odd order”, Math. Z. 93 (1966),
Theorem 1(b), p.158, and Lemma 3, pp.156–157; DOI 10.1007/BF01111033.
-/

public section

namespace Glauberman.SylowAutomorphisms.NormalComplement

/-- The nonzero elementary displacement subgroup used in Theorem 1(b).
The conjugation convention is `x * v * x⁻¹`, consistently with the fusion
witness and normalizer APIs. -/
structure OddDisplacement (A : Type*) [Group A] where
  actor : A
  odd_order : Odd (orderOf actor)
  subgroup : Subgroup A
  nontrivial : subgroup ≠ ⊥
  elementary : IsElementaryAbelian 2 subgroup
  normalizes : actor ∈ Subgroup.normalizer (subgroup : Set A)
  surjective_displacement : ∀ u ∈ subgroup,
    ∃ v ∈ subgroup, actor * v * actor⁻¹ * v⁻¹ = u

end Glauberman.SylowAutomorphisms.NormalComplement
