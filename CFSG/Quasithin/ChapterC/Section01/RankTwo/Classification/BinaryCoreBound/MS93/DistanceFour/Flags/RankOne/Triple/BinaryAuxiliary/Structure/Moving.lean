module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Comparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Recognition

/-!
# Quotient and comparison infrastructure for the p.907 moving factor

The imported modules construct the actual finite binary auxiliary quotient
and full conjugation action. They prove the denominator factorization and
index cancellation used to bound its displacement, leaving the reverse
geometric commutator comparison explicit. `SmallDisplacementData` is the
interface to the remaining conditional binary recognition argument.

Actual marked factors transport back through any ambient automorphism and
between all original local flags. Neither transport nor the quotient
construction asserts existence of the source natural moving factor; its
final construction must discharge the geometric and recognition inputs.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Pull back the actual coordinates and exact actor kernel from a transported
local geometry. For `MiddleTransport`, the inverse is the inverse of its
already right-action-oriented conjugation. -/
theorem movingFactor_of_map (source : LocalSource L R) (i : Bool) (d : M)
    (e : MulAut (FreeAmalgam R))
    (n : MarkedFactor ((localFlagActor source (!i) d).map e.toMonoidHom)
      ((⁅Y source i d, localFlagActor source (!i) d⁆ ⊔ secondFlagLayer source i d).map
        e.toMonoidHom)
      ((secondFlagLayer source i d).map e.toMonoidHom)
      ((localFlagKernel source (!i) d).map e.toMonoidHom)) :
    Nonempty (MovingFactor source i d) := by
  have hn := markedFactorMap e.symm n
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact e.symm_apply_apply x
  simpa only [Subgroup.map_map, he, Subgroup.map_id] using Nonempty.intro hn

/-- A moving factor at any one original flag supplies it at the selected delta0. -/
theorem movingFactor_at_iff [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d e : M) :
    Nonempty (MovingFactor source i d) ↔ Nonempty (MovingFactor source i e) := by
  constructor
  · rintro ⟨n⟩
    simpa only [inv_mul_cancel_right] using
      movingFactor_conjugate source geometry hlarge i (e*d⁻¹) d n
  · rintro ⟨n⟩
    simpa only [inv_mul_cancel_right] using
      movingFactor_conjugate source geometry hlarge i (d*e⁻¹) e n

/-- The source estimates and binary recognition construct the actual moving
factor at the selected `delta0` flag. -/
theorem movingFactor [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i) :
    Nonempty (MovingFactor source i p.delta0) := by
  have hlarge : 2 < geometry.b R := by omega
  obtain ⟨c⟩ := Moving.middleComparisonData source geometry common hb early i hkernel natural p
  let t := middleTransport p
  have estimates := Moving.smallDisplacementData_of_middleComparison source geometry common
    early i p t c
  obtain ⟨n⟩ := Moving.movingFactor_of_smallDisplacement source geometry common early i c.flag
    ((secondFlagLayer source i p.delta0).map t.conjugation.symm.toMonoidHom) estimates
  exact (movingFactor_at_iff source geometry hlarge i c.flag p.delta0).mp ⟨n⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
