module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Span
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Terminal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Transport

/-!
# Assembly of the geometric middle of MS93 (4.3.2)

The checked deductions control the actual normalizer span after (6) and
turn the forward normal product into the terminal edge centralization.
Changing the critical configuration also transports the bad fixed-core
bound. The two remaining source stages are explicit in the conditional
assembly: the centralizer choice with b > 6, and the local-product and
endpoint noncontainment argument following (6).

This module does not yet prove the source-only exists_terminal_seed theorem.
Its remaining stage premises must be discharged before that theorem can be
used by the (4.3.2) assembly owner.

Source: MS93 (1993), (4.3.2)(4)--(6) and the subsequent paragraph, pp.884--886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : MS93.Geometry R}

/-- Conditional geometric assembly. Both source-stage premises remain to be
proved; neither the terminal edge centralization nor a terminal seed is an input. -/
theorem exists_terminal_seed_of_geometric_stages (hb : 2 < geometry.b R)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (selection : ∃ q : Counterexample geometry,
      6 < geometry.b R ∧ Nonempty (Geometry.CentralizerChoice q))
    (products : ∀ q : Counterexample geometry,
      ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a →
      6 < geometry.b R → Geometry.CentralizerChoice q →
      ∃ s, Before q.a' q.a s 2 ∧
        ((Vcirc R q.a ⊔ Vcirc R s).subgroupOf (stabilizer R s)).Normal ∧
        ¬ Vcirc R q.c ≤ Q R q.a) :
    ∃ q : Counterexample geometry, Nonempty (TerminalSeed q) := by
  obtain ⟨q, hlarge, ⟨chosen⟩⟩ := selection
  have hbad := Geometry.bad_at hb p.color_a bad q.a q.color_a
  obtain ⟨s, hs, hn, hout⟩ := products q hbad hlarge chosen
  exact ⟨q, ⟨Geometry.terminalSeed_of_forward_normal q hlarge hs hn hout⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
