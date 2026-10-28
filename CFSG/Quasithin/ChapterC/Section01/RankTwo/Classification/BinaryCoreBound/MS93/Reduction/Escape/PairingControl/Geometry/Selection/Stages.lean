module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Transport

/-!
# Combining the two path-selection stages

The contrary fixed-core bound transports to the selected critical start.
The initial facts give b >= 6, so the exclusion of equality yields b > 6
on that same configuration. This conditional helper lies below both the
six-step exclusion and the completed selection assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(4)--(5), pp.884--885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : MS93.Geometry R}

/-- Assemble the two independent source stages, retaining and transporting
the changed configuration rather than asserting a WLOG identification. -/
theorem exists_centralizerChoice_of_stages (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (selection : ∃ q : Counterexample geometry, Nonempty (CentralizerChoice q))
    (exclude : ∀ q : Counterexample geometry,
      ¬ ⁅V R q.a, Q R q.a⁆ ≤ fixedCore R q.a → CentralizerChoice q → geometry.b R ≠ 6) :
    ∃ q : Counterexample geometry, 6 < geometry.b R ∧ Nonempty (CentralizerChoice q) := by
  obtain ⟨q, ⟨choice⟩⟩ := selection
  have hbad := bad_at hb p.color_a bad q.a q.color_a
  have hne := exclude q hbad choice
  obtain ⟨hq⟩ := initial q
  have hle := hq.six_le
  exact ⟨q, by omega, ⟨choice⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection
