module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Terminal.Normality

/-!
# The final contradiction in original MS93 (4.3)

The actual third orbit witness, uniform centrality at six, positive
radius-six kernel bound, and noncommutation select a reversed contrary
critical pair. Its critical commutator lies in the original R₀ and the
original starting local center, whose intersection is trivial.

All terminal inputs are constructed here from the preceding source stages.
The public Escape boundary constructs those preceding stages in turn.
Source: Meierfrankenfeld--Stellmacher (1993), printed pp.889–890.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal
open Subgroup Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- The complete final contradiction on printed pp.889–890. The earlier
source stages remain explicit, and every terminal premise is proved here. -/
theorem counterexample_false (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry) : False := by
  have hlarge := eight_le propagation p
  obtain ⟨d, hd⟩ := p.exists_before (show 4 ≤ geometry.b R by omega)
  obtain ⟨t₃, h₃⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  obtain ⟨t₅, h₅⟩ := p.exists_before (show 5 ≤ geometry.b R by omega)
  obtain ⟨s, hs⟩ := p.exists_before (show 6 ≤ geometry.b R by omega)
  obtain ⟨t₇, h₇⟩ := p.exists_before (show 7 ≤ geometry.b R by omega)
  obtain ⟨w⟩ := third_orbit_witnesses source hb modules initial control edge propagation
    p hd h₃ h₅ hs h₇
  exact contradiction_of_third_noncommutation source hb modules initial control edge propagation p h₇ w
    (third_noncommutation source hb modules initial control propagation p hd h₃ h₅ hs w)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal
