module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Quotient

/-!
# The two mathematical stages of the first pairing

Step (2) proves that the moving natural section of V/Z has the orientation
opposite to U. The denominator of this section is Z[V,Q]; it must not be
replaced by U before proving step (3). `MovingOrientationAt` retains the
entire natural-section structure and actual contragredient coordinates
relative to U under one quotient marking.

Step (3) identifies the intrinsic section Vcirc/U and proves the edge and
moving-neighbor assertions. `StepThreeAt` records its local outputs. Neither
record is assumed in the source theorem: their producers remain obligations
of the first-pairing assembly. The two producers can be developed independently
by letting the latter explicitly take the former's conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2)--(3), pp.883--884;
the meaning of the moving section is specified on p.881.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Opposite orientation before the radical denominator has been identified.
This is a conclusion of step (2), not a new source hypothesis. -/
structure MovingOrientationAt (a : Vertex R) where
  projection : stabilizer R a →* SL
  naturalU : RankOnePairing.NaturalFactor projection ⊤
    ((U R a).subgroupOf (stabilizer R a)) ⊥
  natural_section : SingleNaturalSection projection
    ((Q R a).subgroupOf (stabilizer R a))
    (pResidual 2 (stabilizer R a))
    ((V R a).subgroupOf (stabilizer R a))
    ((Z R a).subgroupOf (stabilizer R a))
  dual : RankOnePairing.DualFactor projection ⊤
    (movingPreimage ((Q R a).subgroupOf (stabilizer R a))
      ((V R a).subgroupOf (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)))
    (radicalPreimage ((Q R a).subgroupOf (stabilizer R a))
      ((V R a).subgroupOf (stabilizer R a)) ((Z R a).subgroupOf (stabilizer R a)))
    ((U R a).subgroupOf (stabilizer R a)) naturalU

/-- The local section and edge outputs of step (3). H=U and the order of
Vcirc are derived from these coordinates by Consequences.lean. -/
structure StepThreeAt (geometry : Geometry R) (a : Vertex R) : Prop where
  opposite : Nonempty (OppositeSectionAt a)
  edge_eq : ∀ t d, Adjacent R a t → Adjacent R d t →
    d ∈ movingNeighbors geometry a → edgeDisplacement d t = edgeDisplacement a t
  moving_symmetric : ∀ d, d ∈ movingNeighbors geometry a → a ∈ movingNeighbors geometry d

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
