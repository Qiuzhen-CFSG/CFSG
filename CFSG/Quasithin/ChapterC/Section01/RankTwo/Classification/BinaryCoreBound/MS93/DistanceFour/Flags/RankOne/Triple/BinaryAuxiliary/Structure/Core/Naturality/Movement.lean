module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Pencil

/-!
# The nonzero displacement calculation on MS93 p.907

The literal action on Y/Z_alpha and its incident pencil turn hypothetical
centralization of D by the local core into centralization of [Y,core] by
the full actor. This contradicts the original preparatory triple. The
proved residual equivalence then gives movement of X/Z_alpha by the
genuine residual. Both constructions are supplied here, with no additional
action or displacement premise and without using the separate size bound.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The nonzero D/core displacement on p.907, from the original source
configuration and the constructed action on the literal Y/Z_alpha. -/
theorem D_core_commutator_not_le
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (_hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (_natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (_moving : MovingFactor source i p.delta0) :
    ¬ ⁅D source i p.delta0, localFlagKernel source (!i) p.delta0⁆ ≤
      Z R (alpha R) := by
  obtain ⟨b⟩ := coreMovement_sourceAction source geometry common early i hkernel p.delta0
  exact b.D_core_commutator_not_le_of_calculation geometry p
    (CoreMovement.pencil_core_displacement_fixed b.representation b.layer b.pencil)

/-- The nonzero core displacement is moved by the actual local residual;
nontriviality of X/Z_alpha alone is not used as a replacement. -/
theorem X_residual_commutator_not_le
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (moving : MovingFactor source i p.delta0) :
    ¬ ⁅X source i p.delta0, localFlagResidual source (!i) p.delta0⁆ ≤
      Z R (alpha R) := by
  exact (X_residual_commutator_not_le_iff_D_core_commutator_not_le
    source geometry common early i p.delta0).mpr
      (D_core_commutator_not_le source geometry common hb early i hkernel natural p moving)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
