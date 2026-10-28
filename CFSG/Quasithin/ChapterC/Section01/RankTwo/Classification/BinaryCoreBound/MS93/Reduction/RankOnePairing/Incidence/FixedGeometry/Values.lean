module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.Pencils

/-!+# The local value spaces for the fixed case of MS93 (1.7)

This intermediate geometric obligation concerns only the commutator values
in the specified natural three-space Z. In addition to the local bounds,
it asks for the other two lines through actual elements of the neighboring
normalizer. It does not assume anything about the image of X in its local
rank-one factor. The binary quotient argument in `FixedGeometry` constructs
that image and the two decompositions required by `FixedPencil`.

The constructor for this obligation must retain the arbitrary marking on Z.
Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), printed p.847.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry
open Subgroup
universe u
variable {M : Type u} [Group M]

/-- Only the geometry of the value spaces; the seed generator and the local
spanning statements are derived separately from the actual rank-one quotient. -/
structure ValueGeometry (e : Extension (M := M)) (i : Bool) (Z W X : Subgroup M)
    [Z.Normal] : Prop where
  seed_bound : ⁅X, W⁆ ≤ localFixed e Z i
  local_bound : ⁅localGenerated (localParabolic e (!i)) X, W⁆ ≤ localFixed e Z (!i)
  local_proper : ¬ Z ≤ localFixed e Z (!i)
  seed_fixed : localFixed e Z i ≤ centralizer (localResidual (localParabolic e i) : Set M)
  seed_card : Nat.card (localFixed e Z i) ≤ 2
  value_neighbors : ∃ a b : M, a ∈ localParabolic e (!i) ∧ b ∈ localParabolic e (!i) ∧
    localFixed e Z i ⊓ conjugate a (localFixed e Z i) = ⊥ ∧
    localFixed e Z i ⊓ conjugate b (localFixed e Z i) = ⊥ ∧
    conjugate a (localFixed e Z i) ⊓ conjugate b (localFixed e Z i) = ⊥

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry
