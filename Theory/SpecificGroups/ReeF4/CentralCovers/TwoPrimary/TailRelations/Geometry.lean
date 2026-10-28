module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.BlockCollection

/-!
# Concrete geometry needed to lift the Ree angular relations

There are two independent calculations in the actual Ree group. The angular
commutator inclusions imply that an earlier root block normalizes the join of
the later blocks. For distinct blocks, a fixed torus element centralizes the
first, normalizes all blocks, and has a surjective commutator map on the second.
The latter condition retains both coordinates of a nonabelian B₂ block.

These predicates specify only calculations downstairs. Neither asserts a
relation in a central extension or the existence of a section. The lifting
argument in `TailRelations` uses them to eliminate central commutator defects.

Source: GLS3, Corollary 2.4.6 and Theorem 2.4.7(f),
`refs/KGroup/GLS3/chapter2.tex`. The application to central covers is GLS3 §6.1
and Aschbacher–Smith I.1.3, printed p.407 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.CentralCovers.TwoPrimary.TailRelations
open ElementaryTwoBound Subgroup

/-- The actual join of root blocks, in any specified order. -/
def baseOrderedJoin (m : ℕ) (order : List BlockIndex) : Subgroup (Model m) :=
  order.foldr (fun i H => X m (rootIndex i) ⊔ H) ⊥

/-- The base-group consequence of the source angular-interval commutator law. -/
def BaseNormalizesTails (m : ℕ) : Prop :=
  ∀ before i after, sourceOrder = before ++ i :: after →
    X m (rootIndex i) ≤ normalizer (baseOrderedJoin m after : Set (Model m))

/-- Separating torus actors on the literal root subgroups. The commutator here
is `t * z * t⁻¹ * z⁻¹`; all elements of the second block must occur. -/
def TorusBlockSeparation (m : ℕ) : Prop :=
  ∀ i j : BlockIndex, i ≠ j → ∃ t : Model m,
    t ∈ Parabolics.fixedTorus m ∧
    (∀ k : BlockIndex, t ∈ normalizer (X m (rootIndex k) : Set (Model m))) ∧
    (∀ x : X m (rootIndex i), Commute t x.val) ∧
    ∀ y : X m (rootIndex j), ∃ z : X m (rootIndex j),
      t * z.val * t⁻¹ * z.val⁻¹ = y.val

end ReeF4.CentralCovers.TwoPrimary.TailRelations
