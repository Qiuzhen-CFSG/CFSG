module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.SelectedSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Terminal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.SelectedSource

/-!
# The complete local-control argument MS93 (4.3.2)

Assume the full-radius commutator is not contained in its fixed core. The
first pairing supplies the opposite factors and step-(3) identities. Choose
the source centralizer path and use the complete six-step exclusion to obtain
b > 6. The local products then construct a terminal seed on this same path.
Keep the contrary assumption and centralizer choice with that seed; the
selected-source terminal pairing gives the faithful-action contradiction.

This proves the fixed-core containment. The existing order-four calculation
then gives the remaining two exact edge identities in LocalControl. All
intermediate pairing and geometric premises are discharged here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2), printed pp.883--886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.SourceProof

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R}

/-- The source geometric stage keeps its bad configuration, terminal seed and
centralizer choice together, including the literal selected critical path. -/
theorem exists_selected_terminal (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ∃ q : Counterexample geometry,
      (¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a) ∧
      Nonempty (TerminalSeed q × Geometry.CentralizerChoice q) := by
  obtain ⟨q, hlarge, ⟨chosen⟩⟩ :=
    Geometry.Selection.exists_centralizerChoice_of_selection source hb modules initial facts p bad
      (Geometry.Selection.Centralizer.exists_centralizerChoice source hb modules transfer
        initial facts p bad)
  have hbad := Geometry.bad_at hb p.color_a bad q.a q.color_a
  obtain ⟨s, hs, hn, hout⟩ := Geometry.LocalProducts.local_products source hb modules transfer
    initial facts q hbad hlarge chosen
  exact ⟨q, hbad, ⟨Geometry.terminalSeed_of_forward_normal q hlarge hs hn hout, chosen⟩⟩

/-- Original source (4.3.2), with only its earlier local-source, module,
normalization and initial-facts inputs. All pairing stages are discharged. -/
theorem localControl_of_source (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) : LocalControl p := by
  obtain ⟨hp⟩ := initial p
  apply localControl_of_commutator_le source hb modules hp
  by_contra bad
  have facts := FirstPairing.first_pairing_facts source hb modules transfer initial p bad
  obtain ⟨q, hbad, ⟨seed, chosen⟩⟩ :=
    exists_selected_terminal source hb modules transfer initial facts p bad
  exact TerminalPairing.SelectedSource.false_of_selected_source source hb modules transfer
    initial facts q hbad seed chosen


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.SourceProof
