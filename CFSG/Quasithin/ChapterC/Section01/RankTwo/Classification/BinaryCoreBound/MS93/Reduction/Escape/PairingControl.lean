module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FaithfulSection

/-!
# Assembly of the local-control contradiction MS93 (4.3.2)

The initial reduction and terminal faithfulness argument are proved here.
`localControl_of_pairing_stages` assembles three still-explicit intermediate
inputs: the first pairing's opposite local sections, the geometric terminal
seed, and the final dual pairing's commutator bound. None is an assumption
of the source theorem. Their constructors must be proved before this
assembly gives the requested LocalSource-only local-control theorem.

The last bound makes the endpoint-side moving group act trivially on the
natural start section. Its faithful quotient marking puts that group in
the start two-core, contrary to the terminal seed. This establishes the
fixed-core bound, and the order-four argument in Basic gives the exact
edge identities for H.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2), printed pp.883--886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The final contradiction uses the actual natural factor of V/Z; its
commutator premise is the output still required of the last dual pairing. -/
theorem terminal_contradiction (source : LocalSource L R)
    {p : Counterexample geometry} (initial : InitialFacts p) (seed : TerminalSeed p)
    (hc : ⁅Vcirc R p.a, Vcirc R p.c⁆ ≤ Z R p.a) : False :=
  seed.actor_not_le (actor_le_Q source p.color_a initial.natural_section
    (Vcirc R p.c) seed.actor_local hc)

/-- Conditional assembly, retaining all three unproved source stages as
explicit premises. This is not yet the source-only theorem (4.3.2). -/
theorem localControl_of_pairing_stages (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ p : Counterexample geometry, Nonempty (InitialFacts p))
    (first : ∀ p : Counterexample geometry,
      ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a → ContraryLocalFacts geometry)
    (geometric : ∀ p : Counterexample geometry,
      ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a →
      ContraryLocalFacts geometry →
      ∃ q : Counterexample geometry, Nonempty (TerminalSeed q))
    (pairing : ∀ p : Counterexample geometry, ContraryLocalFacts geometry →
      TerminalSeed p → ⁅Vcirc R p.a, Vcirc R p.c⁆ ≤ Z R p.a)
    (p : Counterexample geometry) : LocalControl p := by
  obtain ⟨hinit⟩ := initial p
  apply localControl_of_commutator_le source hb modules hinit
  by_contra hbad
  have facts := first p hbad
  obtain ⟨q, ⟨seed⟩⟩ := geometric p hbad facts
  obtain ⟨hq⟩ := initial q
  exact terminal_contradiction source hq seed (pairing q facts seed)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
