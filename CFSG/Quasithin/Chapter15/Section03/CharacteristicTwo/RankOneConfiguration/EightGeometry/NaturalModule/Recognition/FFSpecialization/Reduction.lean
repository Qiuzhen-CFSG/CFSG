module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Marking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Repeated
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Orthogonal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.NaturalDualExclusion

/-!
# Geometric reduction of all unmarked degree-eight module cases

The moving line excludes both a natural module plus its dual and any number
of repeated natural summands. The classifier may choose its own component
isomorphism: `exists_remarking` transports the middle flag into those same
coordinates, preserving the actual parabolic and moving line. The surviving
orthogonal quotient gives the required equivariant surjection and its exact
component-fixed kernel in the original S₈ marking.

This is a conditional reduction of classification output. It does not assume
that `UnmarkedCases` is a source theorem; deriving that output from the full
B.5.1 alternatives, B.4.2, and the relevant central-cover facts remains a
separate classification obligation.

Source: Aschbacher–Smith, B.5.1(1) and the proof of 15.3.32(1), combined
manuscript (1 March 2004), printed pp.99–103 and 1132.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
open Chapter2.ComponentRefinement.LieType.Binary

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) K V} {L P S Y : Subgroup K}

/-- Repeated natural summands are excluded even when their component model was
chosen independently of the original parabolic marking. -/
theorem RepeatedNatural.not_movingLine_unmarked {r : ℕ} (h : RepeatedNatural ρ L r)
    (mark : Models.MiddleNodeMarking L P)
    (line : Models.MovingLine ρ P S Y) (hY : Y ≤ P) : False := by
  obtain ⟨F, hF, hP⟩ := exists_remarking mark h.model
  exact h.not_movingLine ⟨h.model, F, hF, hP⟩ rfl line hY

/-- The same transported marking excludes independently chosen natural-plus-dual
coordinates. The actual parabolic and the moving line are unchanged. -/
theorem not_naturalDual_unmarked (model : L ≃* PSL 4)
    (mark : Models.MiddleNodeMarking L P)
    (line : Models.MovingLine ρ P S Y) (hY : Y ≤ P) :
    ¬ Nonempty (Models.NaturalDual ρ L model) := by
  obtain ⟨F, hF, hP⟩ := exists_remarking mark model
  exact NaturalDualExclusion.not_nonempty_naturalDual ⟨model, F, hF, hP⟩ line hY

/-- All unmarked cases reduce to the orthogonal cover in the original S₈
marking. This consumes classification output; it does not supply that output. -/
theorem orthogonalCover_of_unmarked (h : UnmarkedCases ρ L)
    (e : K ≃* Equiv.Perm (Fin 8))
    (he : L.map e.toMonoidHom = alternatingGroup (Fin 8))
    (hfull : Representation.Coinvariants.ker (ρ.comp L.subtype) = ⊤)
    (mark : Models.MiddleNodeMarking L P)
    (line : Models.MovingLine ρ P S Y) (hY : Y ≤ P) :
    Nonempty (Models.OrthogonalCover ρ L e) := by
  rcases h with h | h | h
  · obtain ⟨h⟩ := h
    exact ⟨h.markedCover e he hfull⟩
  · obtain ⟨model, h⟩ := h
    exact (not_naturalDual_unmarked model mark line hY h).elim
  · obtain ⟨r, _, _, ⟨h⟩⟩ := h
    exact (h.not_movingLine_unmarked mark line hY).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
end
