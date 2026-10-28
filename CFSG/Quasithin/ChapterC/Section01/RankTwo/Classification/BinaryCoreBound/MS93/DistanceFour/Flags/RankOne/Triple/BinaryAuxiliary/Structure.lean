module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Targets
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.SourceData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Midpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core

/-!
# Assembly of the binary auxiliary structure on MS93 p.907

The midpoint construction supplies the actual transporter and Sylow
arrangement. The commutator comparison constructs the natural moving
quotient at the selected flag, and the core calculation supplies the natural
X quotient and all three cross-layer identities. Literal conjugation then
transports the complete structure, including both exact actor kernels and
the coordinate action equations, to every requested flag.

`localStructure` discharges both calculation premises from the source
inputs. The earlier natural section and corrected preparatory configuration
remain explicit inputs supplied by the enclosing flag argument.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), p.907.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Assemble the two calculations at a single flag and transport the complete
structure to any flag. Both calculation premises must still be discharged. -/
theorem localStructure_of_calculations [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool) (d₀ : M)
    (moving : MovingFactor source i d₀) (core : CoreCalculation source i d₀) (d : M) :
    Nonempty (LocalStructure source i d) := by
  apply (localStructure_at_iff source geometry hlarge i d₀ d).mp
  exact ⟨⟨moving.val, moving.property, core.natural.val, core.natural.property,
    core.first_triple, core.second_commutator, core.second_decomposition⟩⟩

/-- The binary auxiliary structure of MS93 (4.6.8), p.907, at each incident
second flag. Both natural factors and every cross-layer identity are
constructed from the corrected source configuration. -/
theorem localStructure [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (natural : FlagNaturalSection source i)
    (p : SourceFlagPreparatoryData source geometry i)
    (d : M) (_hd : flagIncident source i 1 d) :
    Nonempty (LocalStructure source i d) := by
  obtain ⟨moving⟩ := movingFactor source geometry common hb early i hkernel natural p
  obtain ⟨core⟩ := coreCalculation source geometry common hb early i hkernel natural p moving
  exact localStructure_of_calculations source geometry (by omega) i p.delta0 moving core d

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
