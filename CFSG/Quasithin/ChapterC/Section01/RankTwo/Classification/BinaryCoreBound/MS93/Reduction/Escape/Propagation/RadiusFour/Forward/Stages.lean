module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Geometry

/-!
# Local algebra stages of the forward radius-four argument

The geometric extraction and reversal are proved in Geometry and Reduction.
Reversal supplies movement at the sixth predecessor and the trivial central
intersection. Products proves the local product noncontainment and join.

These records are intermediate proof targets, not additional hypotheses of the
source theorem. Forward.forwardFacts constructs both from the preceding stages.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.8), first three paragraphs
of printed p.889. The final contradiction for (4.3) is outside this interface.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The two local-algebra inputs to the reversed-configuration contradiction. -/
structure ReversalFacts (geometry : Geometry R) : Prop where
  radius_disjoint : ∀ p : Counterexample geometry,
    radiusCommutator p.a p.a' ⊓ localCenter p.a = ⊥
  selected_moving : ∀ (p : Counterexample geometry) (d t₃ t₅ s : Vertex R),
    Before p.a p.a' d 4 → Before p.a p.a' t₃ 3 → Before p.a p.a' t₅ 5 →
    Before p.a p.a' s 6 → ∀ w : CentralOrbitWitnesses p d t₃ t₅,
    ∀ (x : Vertex R) (hx : color R x = false),
      CriticalPair R x w.lam (geometry.exists_critical x hx) →
      (cosetGraph R).dist x p.a = 4 →
      (cosetGraph R).dist p.a w.lam + 4 = geometry.b R →
        w.lam ∈ movingNeighbors geometry s

/-- The commutation proved from ReversalFacts, available as an explicit input
to the independent local-product argument. -/
def CommutationFacts (geometry : Geometry R) : Prop :=
  ∀ (p : Counterexample geometry) (d t₃ t₅ : Vertex R),
    Before p.a p.a' d 4 → Before p.a p.a' t₃ 3 → Before p.a p.a' t₅ 5 →
    ∀ w : CentralOrbitWitnesses p d t₃ t₅, ⁅VBall R p.a 4, Z R w.lam⁆ = ⊥

/-- The local-product outputs preceding the final nonmoving deduction.
Noncontainment follows in the source from the stronger assertion about Vcirc;
the radius join retains the literal first path edge. -/
structure ProductFacts (geometry : Geometry R) : Prop where
  first_not_le : ∀ (p : Counterexample geometry) (d t₃ t₅ : Vertex R),
    Before p.a p.a' d 4 → Before p.a p.a' t₃ 3 → Before p.a p.a' t₅ 5 →
    ∀ w : CentralOrbitWitnesses p d t₃ t₅, ¬ V R w.mu ≤ Q R p.a
  radius_join : ∀ (p : Counterexample geometry) (d : Vertex R),
    Before p.a p.a' d 4 → ∀ t, Before p.a' p.a t 1 →
      VBall R d 4 ⊔ Q R p.a = Q R t

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward
