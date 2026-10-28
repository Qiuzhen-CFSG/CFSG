module

public import Theory.AlgebraicGroup.Bor1.SolvableFixedPointInduction
public import Theory.AlgebraicGroup.Bor1.CompleteNormalOrbitFixedPoint

/-!
# The solvable fixed-point theorem

Borel, *Linear Algebraic Groups*, §10.4
(`refs/KGroup/Bor1/Chapter3.tex`, lines 851–859).
Dimension induction reduces to an action with trivial commutator action.
A smooth closed orbit then has normal stabilizer, and the normal-orbit
lemma forces it to consist of a single point.

Completeness is universal closedness of the actual structure morphism. The
normal-orbit lemma uses the genuine affine stabilizer quotient and proves its
irreducibility before transferring completeness from the smooth closed orbit.
-/

open AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A connected solvable algebraic group acting morphically on a nonempty
complete variety has a fixed point. The variety may be disconnected. -/
public theorem exists_fixedPoint_of_isConnected_isSolvable_isComplete
    {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
    {X : Geometric k} (A : MorphicAction G X)
    (hG : Variety.IsConnected G) (hsol : Group.IsSolvable (Variety.Point G))
    (hX : IsComplete X) (hne : Nonempty (Point X)) :
    ∃ x : Point X, ∀ g : Variety.Point G, A.toMulAction.smul g x = x := by
  apply exists_fixedPoint_of_commutator_trivial_case ?_ A hG hsol hX hne
  intro H _ Y B hH hY hYne hcomm
  obtain ⟨y₀⟩ := hYne
  let : Nonempty Y.toScheme := ⟨y₀.1 (IsLocalRing.closedPoint k)⟩
  obtain ⟨y, -, hy⟩ := B.exists_smooth_closed_orbit
  have hN : (B.pointStabilizer y).toSubgroup.Normal := by
    apply Subgroup.Normal.of_commutator_le
    intro c hc
    exact (B.mem_pointStabilizer y c).mpr (hcomm c hc y)
  exact ⟨y, B.fixed_of_isClosed_orbit_of_normal_stabilizer hH hY y hy hN⟩

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
