module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.SourcePolarRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SourcePolarFacts

/-!
# The original C₃ recognition theorem I.5.1(2)

The original D1–D5 subgroup system supplies the marked point residues.
The global coset geometry has 63 points, a faithful action, and singular
and nonsingular one-or-all triples. Binary row reconstruction identifies
its point set with the nonzero vectors of a six-dimensional symplectic
space. The original point core gives the full symplectic image.

Source: Aschbacher–Smith I.5.1(2), with the proof in I.5.3–15, printed
pp.419–424. No global finiteness or recognition premise is required.
-/

public noncomputable section
namespace Quasithin.I5.C3Recognition
open Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G]

def equivSp6 (S : DSystem .C3 G) : G ≃* Sp (ZMod 2) :=
  equivSp6_of_local_polar_facts S S.source_local_polar_facts

theorem theorem_I_5_1_2 (S : DSystem .C3 G) : Nonempty (G ≃* Sp (ZMod 2)) :=
  ⟨equivSp6 S⟩

theorem center_eq_bot (S : DSystem .C3 G) : Subgroup.center G = ⊥ := by
  let e := equivSp6 S
  apply le_bot_iff.mp
  intro a ha
  have he : e a ∈ Subgroup.center (Sp (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨c, rfl⟩ := e.surjective b
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp ha c)
  rw [EvenProjective.center_eq_bot, Subgroup.mem_bot] at he
  exact Subgroup.mem_bot.mpr (e.injective (he.trans (map_one e).symm))

theorem card_eq (S : DSystem .C3 G) : Nat.card G = 1451520 := by
  rw [Nat.card_congr (equivSp6 S).toEquiv]
  exact card_sp_of_card_two (by simp)

end Quasithin.I5.C3Recognition
