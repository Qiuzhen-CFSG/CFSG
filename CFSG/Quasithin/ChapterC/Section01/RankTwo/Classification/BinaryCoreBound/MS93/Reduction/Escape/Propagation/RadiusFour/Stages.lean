module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.OrbitIdentities

/-!
# The remaining radius-four arguments on printed p.889

Centrality and the actual conjugators, displacements and intersections have
been proved in Centrality and OrbitIdentities. The first remaining branch
proves commutation with the second conjugate, the local join, and nonmovement
of the first conjugate. The second branch may take those conclusions as
explicit inputs while proving the noncontainment and intersection bounds.

These records are proof targets, not additional hypotheses of MS93 (4.3.8).
The RadiusFour assembly remains conditional until their producers are supplied.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.8), printed p.889, ending
before the final contradiction for (4.3).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The first three paragraphs on p.889, for the actual constructed orbits. -/
structure ForwardFacts (geometry : Geometry R) : Prop where
  commutation : ∀ (p : Counterexample geometry) (d t₃ t₅ : Vertex R),
    Before p.a p.a' d 4 → Before p.a p.a' t₃ 3 → Before p.a p.a' t₅ 5 →
    ∀ w : CentralOrbitWitnesses p d t₃ t₅, ⁅VBall R p.a 4, Z R w.lam⁆ = ⊥
  nonmoving : ∀ (p : Counterexample geometry) (d t₃ t₅ : Vertex R),
    Before p.a p.a' d 4 → Before p.a p.a' t₃ 3 → Before p.a p.a' t₅ 5 →
    ∀ w : CentralOrbitWitnesses p d t₃ t₅, w.mu ∉ movingNeighbors geometry d
  radius_join : ∀ (p : Counterexample geometry) (d : Vertex R),
    Before p.a p.a' d 4 → ∀ t, Before p.a' p.a t 1 →
      VBall R d 4 ⊔ Q R p.a = Q R t

/-- The normal-radius contradiction and final intersection bound on p.889. -/
structure KernelBounds (geometry : Geometry R) : Prop where
  not_le : ∀ (p : Counterexample geometry) (d : Vertex R),
    Before p.a p.a' d 4 → ¬ VBall R p.a 4 ≤ Q R d
  intersection_le : ∀ (p : Counterexample geometry) (d : Vertex R),
    Before p.a p.a' d 4 → VBall R p.a 4 ⊓ Q R d ≤ Q R p.c

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour
