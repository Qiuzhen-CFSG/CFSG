module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.TerminalPairing.CoreAlgebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.EdgeSeed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Native.Intersection

/-!+# The terminal contradiction from selected native incidence

The geometric seed construction is uniform in incident vertices: it needs
native incidence, but no assumption that the critical distance is six.
At the actual terminal edge it supplies the marked seed, native containment
and commutator bound. The local pairing theorem then gives the terminal
commutator chain, whose faithful action contradicts the terminal seed.

This reduces the remaining selected-path argument to native incidence at
the predecessor, equivalently containment of its fixed preimage in an
adjacent radius group. Neither incidence nor that containment is asserted
here without a premise. The terminal seed retains its genuine distance
bound greater than six.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), final application of (1.7)(ii) in (4.3.2), printed p.886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing.SelectedIncidence
open Geometry.Selection.Centralizer.Generation

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : MS93.Geometry R}

/-- Native incidence supplies the complete pairing at the prescribed terminal
edge, including the actual common quotient marking and subtype transport. -/
theorem terminal_chain_of_native_incidence (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (seed : TerminalSeed p) (incidence : NativeIncidence p.c) :
    ⁅Vcirc R p.a, Vcirc R p.c⁆ ≤ ⁅Z R p.a, Vcirc R p.c⁆ ∧
      ⁅Z R p.a, Vcirc R p.c⁆ ≤ Z R p.a := by
  obtain ⟨edge⟩ := Geometry.Selection.Six.EdgeSeed.nonempty_at_edge_of_incidence
    source hb modules initial facts p bad p.before_color seed.adjacent incidence
  obtain ⟨pairing⟩ := EdgeSeedAt.pairing_of_local_facts source geometry hb facts edge
  exact terminal_pairing_chain_of_pairing source p seed edge pairing

/-- The actual terminal faithfulness consumer discharges the chain once native
incidence on the selected path is supplied. -/
theorem false_of_native_incidence (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (seed : TerminalSeed p) (incidence : NativeIncidence p.c) : False := by
  obtain ⟨h₁, h₂⟩ := terminal_chain_of_native_incidence source hb modules initial facts p bad seed incidence
  obtain ⟨hp⟩ := initial p
  exact terminal_contradiction source hp seed (h₁.trans h₂)

/-- An equivalent sufficient target is containment of the full fixed preimage
in the literal terminal neighbor. The containment remains a source obligation. -/
theorem false_of_fixed_le_terminal_neighbor (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (seed : TerminalSeed p)
    (hfixed : B R p.c (geometry.Z_normal p.c) ≤ V R seed.t) : False := by
  apply false_of_native_incidence source hb modules initial facts p bad seed
  exact ⟨seed.t, seed.adjacent,
    (native_intersection_iff_fixed_le_neighbor source hb modules initial facts p
      p.before_color seed.adjacent).mpr hfixed⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.TerminalPairing.SelectedIncidence
