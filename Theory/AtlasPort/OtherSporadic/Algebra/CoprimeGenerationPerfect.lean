/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/CoprimeGenerationPerfect.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Perfectness from two coprime generating sets

Exponent bounds on generators pass to every abelian image. Generation by
elements of exponents two and three therefore forces the abelianization to vanish.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/CoprimeGenerationPerfect.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports.
Definitions remain exposed for downstream calculations.
-/

@[expose] public section

namespace Atlas.Algebra

/-- In an abelian image, an exponent bound on a generating set holds everywhere. -/
theorem abelian_image_exponent_of_generators {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) (S : Set G) (n : ℕ) (hS : Subgroup.closure S=⊤)
    (hn : ∀ g ∈ S, g^n=1) (g : G) : (f g)^n=1 := by
  have hs : Subgroup.closure S ≤ ((powMonoidHom n).comp f).ker := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    change (f x)^n=1
    rw [← map_pow,hn x hx,map_one]
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  exact hs hg

/-- Independent generation by elements of exponent2 and by elements of
exponent3 forces perfectness. No finiteness or particular construction is used. -/
theorem perfect_of_two_three_generating_sets {G : Type*} [Group G]
    (S T : Set G) (hS : Subgroup.closure S=⊤) (hT : Subgroup.closure T=⊤)
    (h2 : ∀ g ∈ S,g^2=1) (h3 : ∀ g ∈ T,g^3=1) : Group.IsPerfect G := by
  constructor
  apply (Subgroup.eq_top_iff' _).mpr
  intro g
  rw [← Abelianization.ker_of]
  change Abelianization.of g=1
  have hs := abelian_image_exponent_of_generators Abelianization.of S 2 hS h2 g
  have ht := abelian_image_exponent_of_generators Abelianization.of T 3 hT h3 g
  calc
    Abelianization.of g = (Abelianization.of g)^2 * Abelianization.of g := by rw [hs,one_mul]
    _ = (Abelianization.of g)^3 := (pow_succ _ 2).symm
    _ = 1 := ht

end Atlas.Algebra
