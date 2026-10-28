module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation

/-!
# MS93 (4.3.2)(4): centralizer selection

The local neighbor-generation identity supplies a neighboring V-layer that
escapes the kernel at the start. The geometric assembly constructs its new
critical endpoint, retaining the start and trapped second predecessor. It
also retains the actual third predecessor and proves that the centralizer of
the new radius commutator inside that vertex's kernel is exactly Q_c.

`exists_centralizerChoice` discharges the generation premise using only the
earlier source inputs. In particular, the selection does not require b > 6.
Endpoint movement is proved before applying the radius/displacement identity.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.2)(4) and the preceding display, printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Source (4), preserving the start and trapped second predecessor while
constructing the changed critical endpoint and its relative centralizer. -/
theorem exists_centralizerChoice_preserving
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ q : Counterexample geometry, q.a = p.a ∧ q.c = p.c ∧
      Nonempty (CentralizerChoice q) := by
  obtain ⟨t, ht⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  exact exists_centralizerChoice_of_span source hb initial facts p ht
    (Generation.local_neighbor_generation source hb modules transfer initial facts p bad ht)

/-- The centralizer-selected critical configuration of MS93 (4.3.2)(4),
from the earlier source inputs and without a b > 6 hypothesis. -/
theorem exists_centralizerChoice
    (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ q : Counterexample geometry, Nonempty (CentralizerChoice q) := by
  obtain ⟨q, _, _, choice⟩ :=
    exists_centralizerChoice_preserving source hb modules transfer initial facts p bad
  exact ⟨q, choice⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer
