module

public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.CompleteOrbit
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.CompleteModel

/-!
# Actual orbits with parabolic stabilizer

A point fixed by a Borel subgroup has closed orbit. The complete source is the
proved geometric model of the original G/B, and the orbit is the actual orbit
of the supplied action. In a complete projective ambient variety this produces
the complete parabolic orbit used in Borel, §§13.6–13.7.
-/

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

open SemisimpleCenterContainment.RadicalGeometry.BorelRestriction

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X : Geometric k}

public theorem orbit_isClosed_of_borel_fixed (A : MorphicAction G X)
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (x : Point X) (hfix : ∀ g ∈ B.toSubgroup, A.toMulAction.smul g x = x) :
    IsClosed (Set.range (A.orbitMorphismAt x).hom) := by
  obtain ⟨M⟩ := nonempty_completeModel B hB
  exact M.action.orbit_closed_of_complete_transitive_stabilizer A hG M.complete
    (modelBasePoint M) (modelBasePoint_transitive M) x
    (fun g hg => hfix g ((modelBasePoint_stabilizer M g).mp hg))

public theorem orbit_isComplete_of_borel_fixed (A : MorphicAction G X)
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hX : IsComplete X) (x : Point X)
    (hfix : ∀ g ∈ B.toSubgroup, A.toMulAction.smul g x = x) :
    IsComplete (A.orbitSubvariety x).toGeometric :=
  A.orbitSubvariety_isComplete hX x (A.orbit_isClosed_of_borel_fixed hG B hB x hfix)

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
