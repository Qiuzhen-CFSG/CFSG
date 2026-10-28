module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.Connected
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponents

/-!
# Borel restriction to a subtorus centralizer: geometric assembly

Borel, *Linear Algebraic Groups*, §11.15, identifies the centralizer orbit
through the Borel basepoint with a complete component of the torus-fixed locus.
The theorem below assembles the Borel conclusion from that actual closed
subvariety and its regular transitive action. It proves the literal stabilizer
identity using the ambient model and inclusion, then applies the solvable
fixed-point theorem to obtain maximality.

The fixed-component construction is still an explicit premise here. Thus this
module does not yet assert the unconditional Borel-restriction theorem. Neither
a point bijection nor the legacy arbitrary-proposition completeness record is
used. In particular, no normality of a Borel stabilizer is assumed.
-/

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction

open BorelGeometricConjugacy Variety.Geometric

attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]

/-- The intrinsic Borel conclusion from a complete fixed component with its
actual centralizer action. The geometric premises remain to be constructed
from the connected ambient group and connected centralizer in §11.15. -/
public theorem isBorel_of_transitive_closed_subvariety
    (S B : ClosedSubgroup H) (hS : IsSubtorus S)
    (hB : IsBorelSubgroup B) (hSB : S ≤ B)
    (M : CompleteModel B) (X : ClosedSubvariety M.variety)
    (A : MorphicAction S.centralizer.carrierVariety X.toGeometric)
    (x : Point X.toGeometric)
    (hx : X.inclusion x = modelBasePoint M)
    (hequiv : ∀ (g : Variety.Point S.centralizer.carrierVariety)
      (y : Point X.toGeometric),
      X.inclusion (A.toMulAction.smul g y) =
        M.action.toMulAction.smul (S.centralizer.inclusion.onPoints g) (X.inclusion y))
    (htrans : ∀ y : Point X.toGeometric,
      ∃ g : Variety.Point S.centralizer.carrierVariety, A.toMulAction.smul g x = y) :
    IsBorelSubgroup (S.centralizer.inclusion.closedSubgroupPreimage B) := by
  obtain ⟨hKc, hKs⟩ := connected_solvable S B hS hB hSB
  apply isBorel_of_complete_transitive_action _ hKc hKs A x
    (X.isComplete M.complete) htrans
  intro g
  change A.toMulAction.smul g x = x ↔ S.centralizer.inclusion.onPoints g ∈ B.toSubgroup
  rw [← modelBasePoint_stabilizer M]
  have hinj : Function.Injective (fun y : Point X.toGeometric => X.inclusion y) := by
    intro y z hyz
    apply Subtype.ext
    apply (CategoryTheory.cancel_mono X.inclusion.hom).mp
    exact congrArg Subtype.val hyz
  rw [← hinj.eq_iff, hequiv, hx]
  rfl

/-- Apply the maximality argument to the literal fixed component. Its regular
centralizer action and transitivity are the remaining source premises. -/
public theorem isBorel_of_fixedComponent_transitive
    (S B : ClosedSubgroup H) (hS : IsSubtorus S)
    (hB : IsBorelSubgroup B) (hSB : S ≤ B)
    (M : CompleteModel B)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (A : MorphicAction S.centralizer.carrierVariety (fixedComponent M S Z).toGeometric)
    (x : Point (fixedComponent M S Z).toGeometric)
    (hx : (fixedComponent M S Z).inclusion x = modelBasePoint M)
    (hequiv : ∀ (g : Variety.Point S.centralizer.carrierVariety)
      (y : Point (fixedComponent M S Z).toGeometric),
      (fixedComponent M S Z).inclusion (A.toMulAction.smul g y) =
        M.action.toMulAction.smul (S.centralizer.inclusion.onPoints g)
          ((fixedComponent M S Z).inclusion y))
    (htrans : ∀ y : Point (fixedComponent M S Z).toGeometric,
      ∃ g : Variety.Point S.centralizer.carrierVariety, A.toMulAction.smul g x = y) :
    IsBorelSubgroup (S.centralizer.inclusion.closedSubgroupPreimage B) :=
  isBorel_of_transitive_closed_subvariety S B hS hB hSB M
    (fixedComponent M S Z) A x hx hequiv htrans

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
