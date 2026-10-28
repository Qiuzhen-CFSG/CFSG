module

public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.Basic
public import Theory.SpecificGroups.OmegaSixThree.LocalStructure
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Field.ZMod

/-!
# The natural orthogonal action on ternary projective points

An isometry acts on vectors of norm minus one and respects their equivalence
modulo sign. Polarization shows that this quotient action preserves the
orthogonality graph. Restricting it along the proved inclusion of the derived
orthogonal group fixes the actual action used in F.5; no abstract permutation
representation is chosen.

Source: Aschbacher--Smith, F.5.1 and the graph preceding F.5.7, pp.300,302--303.
-/

@[expose] public section

namespace OmegaSixThree.OrthogonalityGraph

open SixTernaryCoordinates

/-- Isometries preserve norm-minus-one vectors. -/
def orthogonalVector (g : orthogonalGroup) (v : UnitVector) : UnitVector :=
  ⟨g.val v.val, (g.property v.val).trans v.property⟩

/-- Isometries act on the literal quotient of vectors by sign. -/
def orthogonalPoint (g : orthogonalGroup) : Point → Point :=
  Quotient.map (orthogonalVector g) (by
    intro v w h
    rcases h with h | h
    · exact Or.inl (congrArg g.val h)
    · exact Or.inr (by change g.val v.val = -g.val w.val; rw [h, map_neg]))

instance orthogonalMulAction : MulAction orthogonalGroup Point where
  smul := orthogonalPoint
  one_smul x := by
    induction x using Quotient.inductionOn with | h v => rfl
  mul_smul g h x := by
    induction x using Quotient.inductionOn with | h v => rfl

@[simp] theorem orthogonal_smul_point (g : orthogonalGroup)
    (v : Space) (hv : quadratic v = -1) :
    g • point v hv = point (g.val v) ((g.property v).trans hv) := rfl

/-- Preservation of the quadratic form implies preservation of its polar pairing. -/
theorem pairing_orthogonal (g : orthogonalGroup) (v w : Space) :
    pairing (g.val v) (g.val w) = pairing v w := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply mul_left_cancel₀ (by decide : (2 : ZMod 3) ≠ 0)
  rw [← polar_eq, ← map_add, g.property, g.property, g.property, polar_eq]

theorem orthogonal_preserves (g : orthogonalGroup) {x y : Point}
    (h : graph.Adj x y) : graph.Adj (g • x) (g • y) := by
  induction x using Quotient.inductionOn with | h v =>
    induction y using Quotient.inductionOn with | h w =>
      change pairing (g.val v.val) (g.val w.val) = 0
      rw [pairing_orthogonal]
      exact h

/-- The derived orthogonal group acts through its literal inclusion in the
full isometry group. -/
instance omegaMulAction : MulAction omegaPlusSixThree Point :=
  MulAction.compHom Point (Subgroup.inclusion omegaPlusSixThree_le_orthogonalGroup)

@[simp] theorem omega_smul_point (g : omegaPlusSixThree)
    (v : Space) (hv : quadratic v = -1) :
    g • point v hv = point (g.val v)
      ((omegaPlusSixThree_le_orthogonalGroup g.property v).trans hv) := rfl

theorem omega_preserves (g : omegaPlusSixThree) {x y : Point}
    (h : graph.Adj x y) : graph.Adj (g • x) (g • y) :=
  orthogonal_preserves (Subgroup.inclusion omegaPlusSixThree_le_orthogonalGroup g) h

end OmegaSixThree.OrthogonalityGraph
