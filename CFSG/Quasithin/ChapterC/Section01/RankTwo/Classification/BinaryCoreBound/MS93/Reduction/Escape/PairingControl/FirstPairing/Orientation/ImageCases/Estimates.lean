module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.NaturalQuotient

/-!
# Estimate interfaces for the two first-pairing image cases

The large-image estimate retains the original geodesic and the moving-neighbor
condition needed to apply step (1) at alpha+2. The small-image estimate retains
the actual intersection V_c ∩ Q_alpha and the image of its commutator modulo
D_c. The latter lower bound is not the already proved order bound for the
intersection quotient: a representation argument must connect them.

These are outputs of the producers exposed by `LargeImage` and `SmallImage`.
`ImageCases.image_cases` constructs both from the earlier source inputs and
the two pairing bounds, then derives the contradiction in each case.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), p.884.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : MS93.Geometry R}

/-- The path displacement estimate in the image-order-greater-than-two case.
The moving condition must be proved, so step (1) can be used at alpha+2. -/
structure LargeImageEstimate (p : Counterexample geometry) (path : FrontPath p) : Prop where
  moving : p.a ∈ movingNeighbors geometry path.second
  edge_le_fixed : edgeDisplacement p.a path.first ≤ fixedCore R path.second

/-- The two remaining representation estimates in the image-order-two case.
The image lower bound concerns the literal commutator, not just the actor. -/
structure SmallImageEstimate (p : Counterexample geometry) where
  d : Vertex R
  moving : d ∈ movingNeighbors geometry p.a
  image_lower : 4 ≤ (fixedCore R p.c).relIndex
    (⁅Z R d, V R p.c ⊓ Q R p.a⁆ : Subgroup (FreeAmalgam R))
  commutator_le_fixed : ⁅V R p.a, V R p.c ⊓ Q R p.a⁆ ≤ fixedCore R p.a

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
