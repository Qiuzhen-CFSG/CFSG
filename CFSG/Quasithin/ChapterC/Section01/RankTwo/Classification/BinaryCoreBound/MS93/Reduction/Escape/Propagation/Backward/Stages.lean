module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Stages

/-!
# Remaining mathematical contracts within the backward argument

These are proof targets, with no constructor from the source data here.
The (4.3.7)(i) proof may take the (4.3.6) bound explicitly; the symmetry and
far-propagation proof may take (i) explicitly. The Backward assembly owner
must construct and discharge all three stages before supplying BackwardFacts.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.6)--(4.3.7),
printed pp.886--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Source (4.3.6), including its essential reverse-moving span. -/
structure BoundFacts (geometry : Geometry R) : Prop where
  bound : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    ¬ radiusCommutator p.a p.a' ≤ localCenter d →
      d ∈ movingNeighbors geometry p.c ∧
      ∀ t, Adjacent R p.a t →
        (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a →
          backwardSpan geometry p.a t ≤ Q R d

/-- Source (4.3.7)(i): relative normality and the residual commutator bound. -/
structure ProductFacts (geometry : Geometry R) : Prop where
  products : ∀ p : Counterexample geometry, ∀ d,
    (cosetGraph R).dist p.a d = 2 → p.a ∈ movingNeighbors geometry d →
      V R d ⊔ V R p.a ≤ stabilizer R p.a ∧
      ((V R d ⊔ V R p.a).subgroupOf (stabilizer R p.a)).Normal ∧
      ⁅V R d, Ltilde R p.a⁆ ≤ Vcirc R p.a

/-- Source (4.3.7)(ii)--(iii), retaining all three assertions. -/
structure MovingFacts (geometry : Geometry R) : Prop where
  symmetric : ∀ p : Counterexample geometry, ∀ d,
    d ∈ movingNeighbors geometry p.a ↔ p.a ∈ movingNeighbors geometry d
  far_not_moving : ∀ p : Counterexample geometry, ∀ d, Before p.a p.a' d 4 →
    p.c ∉ movingNeighbors geometry d
  radius_bound : ∀ p : Counterexample geometry,
    ∀ d ∈ movingNeighbors geometry p.a, V R d ≤ Q R p.c

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
