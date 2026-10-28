module

public import CFSG.Quasithin.ChapterG.Section03.Recognition
public import CFSG.Quasithin.ChapterG.Section03.Decomposition
public import CFSG.Quasithin.ChapterG.Section03.LocalRank

/-!
# The G.3 source-use specialization with trivial two-core

Full-action recognition supplies the two inputs needed by the internal orbit
decomposition and local rank arguments. Thus all three conclusions of G.3.1
hold when the actual faithful acting group has trivial intrinsic two-core.
This extra hypothesis is explicit: this is not the unrestricted printed lemma.
Consumers must prove it for their full action image before applying this result.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004, G.3.1,
printed pp.337--338 (PDF pp.348--349).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section03

open BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- All G.3.1 conclusions, with the additional trivial-two-core input on the
actual faithful acting group. Recognition and both conditional helpers are
discharged here. No irreducibility or semisimplicity input is required. -/
theorem source_conclusions_of_twoCore_eq_bot
    {G : Subgroup (BinaryLinear.GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hcore : pCore 2 G = ⊥) :
    FullAction G Δ ∧ Decomposition G Δ ∧ LocalStructure G Δ := by
  have hf := fullAction_of_hypotheses_of_twoCore_eq_bot h hcore
  have hd := decomposition_of_fullAction G Δ h hf
  exact ⟨hf, hd, localStructure_of_decomposition h hf hd⟩

end CFSG.Quasithin.ChapterG.Section03
