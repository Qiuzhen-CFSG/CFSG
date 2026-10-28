module

public import Theory.SpecificGroups.OrthogonalFourBinary.NaturalAction
public import Theory.GroupTheory.PResidual.Defs

/-!
# Stabilizers of singular lines in the binary orthogonal four-space

The actor is the full quadratic isometry group of the existing form. Its
linear action defines actual setwise stabilizers of subgroups of the
multiplicative vector space. The line residual is the two-residual of
the stabilizer inside the full actor's two-residual.

These definitions prepare the finite calculation in the construction before
Aschbacher–Smith 15.3.68, printed p.1154 (combined manuscript, 1 March 2004).
They make no product or commutativity assertion.
-/

@[expose] public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.TerminalLines

/-- The full group of isometries of the specified quadratic form. -/
abbrev IsometryGroup := quadraticIsometrySubgroup (k := F) (V := Space) form

instance : Finite IsometryGroup :=
  Finite.of_injective (fun g : IsometryGroup => (g.val : Space → Space))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

/-- The defining action, expressed on the multiplicative vector space. -/
def vectorAction : IsometryGroup →* MulAut (Multiplicative Space) where
  toFun g := g.val.toAddEquiv.toMultiplicative
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The setwise stabilizer of the actual vector subgroup. -/
def lineStabilizer (E : Subgroup (Multiplicative Space)) : Subgroup IsometryGroup where
  carrier g := ∀ v, vectorAction g v ∈ E ↔ v ∈ E
  one_mem' := by intro v; rfl
  mul_mem' := by
    intro a b ha hb v
    exact (ha (vectorAction b v)).trans (hb v)
  inv_mem' := by
    intro a ha v
    have h := ha (vectorAction a⁻¹ v)
    simpa only [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply] using h.symm

/-- The embedded two-residual of the line stabilizer in `O²(O₄⁺(2))`. -/
noncomputable def lineResidual (E : Subgroup (Multiplicative Space)) : Subgroup IsometryGroup :=
  (pResidual 2 ↥(pResidual 2 IsometryGroup ⊓ lineStabilizer E)).map
    (pResidual 2 IsometryGroup ⊓ lineStabilizer E).subtype

end OrthogonalFourBinary.TerminalLines
