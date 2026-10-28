module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.SourceData

/-!
# Separate outputs of the p.907 auxiliary calculation

The moving quotient and the subsequent X calculation are separate proof
obligations. `CoreCalculation` records only the latter conclusions, with
actual natural coordinates and the three full-actor identities. It has no
constructor from the source assumptions here. The structure assembly owner
must construct both this record and the independently defined `MovingFactor`.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), p.907.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The X calculation and cross-layer identities after recognizing the moving
quotient. This is an output contract, not an additional source hypothesis. -/
structure CoreCalculation (source : LocalSource L R) (i : Bool) (d : M) where
  natural : XFactor source i d
  first_triple : ∀ g : M, flagIncident source i g d →
    ⁅⁅X source i d, localFlagKernel source i g⁆, localFlagActor source i g⁆ ≤ Z R (alpha R)
  second_commutator : ⁅secondFlagLayer source i d, localFlagActor source (!i) d⁆ ≤ X source i d
  second_decomposition : ∀ g : M, flagIncident source i g d →
    secondFlagLayer source i d =
      commutatorPreimage (firstFlagLayer (R := R) g) (localFlagKernel source (!i) d)
        (Z R (alpha R)) ⊔ X source i d


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
