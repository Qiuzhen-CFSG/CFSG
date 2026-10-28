module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Source

/-!
# The remaining representation and geometry stages of (4.3.1)

The first stage still has to prove R₀ ≠ R; Bounds.lean converts it into all
numerical assertions of (i)--(ii), and Edges.lean supplies the edge equality.
The two output records here separate the full natural-section construction
and moving generation from the distance and commutator conclusions.

These records have no unconditional constructors. In particular SectionFacts
retains all fields of the actual SingleNaturalSection, including quotient
normalities, the triple commutator and equivariant fixed/moving splitting.
The H order bound follows from TailFacts.radius_moving_card by a proved
transport argument, so it need not be a separate remaining hypothesis.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(iii)--(vii), pp.882--883.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

/-- The full representation and generation outputs (4.3.1)(iii)--(iv).
The natural section keeps the actual quotient action and fixed/moving splitting. -/
structure SectionFacts (p : Counterexample geometry) where
  natural_section : NaturalSectionAt p.a (V R p.a) (Z R p.a)
  moving_generation : ∀ d ∈ movingNeighbors geometry p.a,
    Vcirc R p.a ≤ NormalizerTransfer.conjugatesIn (Z R d) (stabilizer R p.a)

/-- The remaining outputs (4.3.1)(v)--(vii), after the natural section.
These are targets for the last stage, not consequences supplied by a constructor here. -/
structure TailFacts (p : Counterexample geometry) : Prop where
  six_le : 6 ≤ geometry.b R
  radius_moving_card : 4 ≤ Nat.card (⁅V R p.a, Vcirc R p.c⁆ : Subgroup (FreeAmalgam R))
  edge_commutator : ∀ t, Before p.a' p.a t 1 →
    ∀ d, Adjacent R d t → d ∈ movingNeighbors geometry p.a →
      ⁅Z R d, Q R p.a⁆ = edgeDisplacement d t

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
