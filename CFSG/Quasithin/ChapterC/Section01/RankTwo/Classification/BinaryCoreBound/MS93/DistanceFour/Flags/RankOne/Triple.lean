module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Terminal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Targets
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Escape

/-!
# The marked flag argument for MS93 (4.6.8)

`select_flag_kernel` proves the source parabolic selection using the actual
quotient, flag and amalgam embedding. `pairingExtension` identifies the
Section 1 local normalizers and distinguishes the two residual actors.
`Natural` and `Preparatory` construct the natural section and the corrected
source configuration on pp.905--906. `BinaryAuxiliary` defines the literal
Y, D and X layers, proves their local normalization and quotient meaning,
and derives the three-neighbor commutator bound. D uses the full untilded
actor, as on p.907.

`BinaryAuxiliary.localStructure` constructs the natural moving and X quotients,
their exact actor kernels and the cross-layer identities on p.907.
`BinaryAuxiliary.auxiliaryEscapes` uses that structure to prove both escapes on p.908.
The terminal displacement argument then makes the midpoint edge commutator
central, contradicting the configuration obtained from a noncentral triple.
`flagControl` discharges every intermediate premise and proves the marked
core selection and central triple bound from the original local inputs.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.905--908.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The marked parabolic selection and MS93 (4.6.8) in the binary case.
The triple uses the source-ordered tilded residual, and its target is the
embedded intrinsic center of the original vertex stabilizer. -/
theorem flagControl [Finite M] (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) : FlagControl source := by
  apply flagControl_of_binary_auxiliary_escapes source geometry common hb early
  intro i hkernel natural p
  exact BinaryAuxiliary.auxiliaryEscapes source geometry common hb early i hkernel natural p
    (BinaryAuxiliary.localStructure source geometry common hb early i hkernel natural p)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
