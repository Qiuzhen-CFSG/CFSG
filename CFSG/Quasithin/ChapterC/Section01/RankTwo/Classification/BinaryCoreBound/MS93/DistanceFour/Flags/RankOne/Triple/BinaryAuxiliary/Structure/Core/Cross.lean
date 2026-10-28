module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.First
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Comparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Cross.Second

/-!
# Cross-commutator deductions for the binary auxiliary core

The source midpoint comparison and the two full-actor cross bounds are
assembled here. The first bound is transported to every incident first actor,
and the second bound is returned to the selected second flag.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-! The two p.907 cross bounds, assembled from the genuine midpoint comparison. -/

theorem coreCrossCommutators
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (moving : MovingFactor source i p.delta0) (x : XFactor source i p.delta0) :
    (∀ g : M, flagIncident source i g p.delta0 →
      ⁅⁅X source i p.delta0, localFlagKernel source i g⁆,
        localFlagActor source i g⁆ ≤ Z R (alpha R)) ∧
      ⁅secondFlagLayer source i p.delta0, localFlagActor source (!i) p.delta0⁆ ≤
        X source i p.delta0 := by
  obtain ⟨c⟩ := middleComparison source geometry common hb early i hkernel natural p moving x
  have hlarge : 2 < geometry.b R := by omega
  exact ⟨(first_triple_of_comparison source geometry hlarge early i hkernel p x c) p.delta0,
    second_commutator_of_middle_comparison source geometry common hb early i hkernel natural
      p moving x c⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
