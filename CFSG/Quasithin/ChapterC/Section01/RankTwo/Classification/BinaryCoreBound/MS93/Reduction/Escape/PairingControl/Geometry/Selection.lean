module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six

/-!
# The selected critical path in MS93 (4.3.2)(4)--(5)

The neighbor-generation argument constructs a critical configuration with
the required relative centralizer equality and an actual third predecessor.
The contrary fixed-core bound transports to the selected start. On that
same configuration, the two six-step branches exclude b = 6; the contained
branch uses the genuine (1.7)(ii) pairing with its natural-factor premise
discharged. The initial bound b >= 6 then gives b > 6.

`exists_centralizerChoice` discharges both stage premises of the earlier
conditional assembly. Only the specified earlier source inputs remain.
The conditional APIs are preserved through public imports.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(4)--(5), pp.884--885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Original MS93 (4.3.2)(4)--(5): construct the centralizer-selected critical
path and prove b > 6, with both selection and exclusion stages discharged. -/
theorem exists_centralizerChoice (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ q : Counterexample geometry, 6 < geometry.b R ∧ Nonempty (CentralizerChoice q) :=
  exists_centralizerChoice_of_selection source hb modules initial facts p bad
    (Centralizer.exists_centralizerChoice source hb modules transfer initial facts p bad)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
