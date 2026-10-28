module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Source

/-!
# Remaining proof stages of the contrary-configuration propagation

These records are targets for the three remaining arguments, not additional
source hypotheses. Their producers may take the preceding stages explicitly,
so the proofs can be developed independently. The propagation assembly must
construct all three records before it supplies Escape.PropagationFacts.

The edge indices (4.3.3) are proved separately in Propagation.Edges. The
centrality at the vertex four before the endpoint follows from BackwardFacts
in Propagation.Consequences. The remaining fields below retain the literal
normality, reverse moving-neighbor condition, radius groups and conjugators.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.4)--(4.3.8), pp.886--889.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The equality, uniqueness and strict distance assertions (4.3.4)--(4.3.5). -/
structure RigidityFacts (geometry : Geometry R) : Prop where
  equal_Z : ∀ p : Counterexample geometry, ∀ t, Before p.a' p.a t 1 →
    ∀ d e, Adjacent R d t → Adjacent R e t →
      ¬ U R d ⊓ Z R e ≤ localCenter e → Z R d = Z R e
  moving_Z_unique : ∀ p : Counterexample geometry, ∀ t, Before p.a' p.a t 1 →
    ∃ d, Adjacent R d t ∧ d ∈ movingNeighbors geometry p.a ∧
      ∀ e, Adjacent R e t → e ∈ movingNeighbors geometry p.a → Z R e = Z R d
  six_lt : ∀ _p : Counterexample geometry, 6 < geometry.b R

/-- The backward bound and the four local propagation clauses (4.3.6)--(4.3.7). -/
structure BackwardFacts (geometry : Geometry R) : Prop where
  backward_bound : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    ¬ radiusCommutator p.a p.a' ≤ localCenter d →
      d ∈ movingNeighbors geometry p.c ∧
      ∀ t, Adjacent R p.a t →
        (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a →
          backwardSpan geometry p.a t ≤ Q R d
  product_normal : ∀ p : Counterexample geometry, ∀ d,
    (cosetGraph R).dist p.a d = 2 → p.a ∈ movingNeighbors geometry d →
      V R d ⊔ V R p.a ≤ stabilizer R p.a ∧
      ((V R d ⊔ V R p.a).subgroupOf (stabilizer R p.a)).Normal ∧
      ⁅V R d, Ltilde R p.a⁆ ≤ Vcirc R p.a
  moving_symmetric : ∀ p : Counterexample geometry, ∀ d,
    d ∈ movingNeighbors geometry p.a ↔ p.a ∈ movingNeighbors geometry d
  far_not_moving : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    p.c ∉ movingNeighbors geometry d
  moving_radius_bound : ∀ p : Counterexample geometry,
    ∀ d ∈ movingNeighbors geometry p.a, V R d ≤ Q R p.c

/-- The centrality, actual orbit choices and literal conclusions used from
(4.3.8). Centrality at the vertex four before the endpoint is derived separately. -/
structure RadiusFourFacts (geometry : Geometry R) : Prop where
  radius_central_at_two : ∀ p : Counterexample geometry,
    radiusCommutator p.a p.a' ≤ localCenter p.c
  witnesses : ∀ p : Counterexample geometry, ∀ d t₃ t₅,
    Before p.a p.a' d 4 → Before p.a p.a' t₃ 3 → Before p.a p.a' t₅ 5 →
      Nonempty (PropagationWitnesses p d t₃ t₅)
  radius_four : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    (¬ VBall R p.a 4 ≤ Q R d) ∧ VBall R p.a 4 ⊓ Q R d ≤ Q R p.c ∧
      ∀ t, Before p.a' p.a t 1 → VBall R d 4 ⊔ Q R p.a = Q R t

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation
