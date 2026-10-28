module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.FixedComparisons
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center
public import Theory.SpecificGroups.BinaryLinear.SylowCenters

/-!
# Excluding the equal-order fixed actor in terminal §13.6

The actual central quotient PSL₃(4) has Sylow two-subgroups with center of
order four. Every Sylow two-subgroup of SL₄(2) has center of order at most
two. Transport through an alleged group equivalence contradicts these
proved bounds, even though both ambient groups have order 20160.

The projective Sylow calculation uses the faithful upper-unitriangular
embedding into PSL₃(4); it does not replace this quotient by SL₃(4).
All other fixed actors have already been excluded by order comparison.
Together these results eliminate every `FixedCompetitor` for each of the
three exceptional terminal components.

This uses the Sylow-center strategy of ATLAS
`Comparisons/Exceptional/Order20160Nonisomorphism.lean`, with the existing
CFSG Sylow calculations. Source application: Aschbacher–Smith, B.4.2/B.4.5,
printed pp.86–87, and terminal §13.6, printed p.935 (PDF p.952), combined
manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications

/-- Sylow two-center orders distinguish the literal equal-order models. -/
theorem l3Four_not_equiv_linearFourTwo :
    ¬ Nonempty (Components.L3Four ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  rintro ⟨e⟩
  let S : Sylow 2 Components.L3Four := Classical.choice inferInstance
  have hfour : Nat.card (center S) = 4 :=
    Matrix.PSL3.LinearThree.card_center_sylow Components.F4 (n := 2)
      (by decide) (GaloisField.card 2 2 (by decide)) S
  have htwo := BinaryLinear.sl_sylow_center_card_le_two (by decide : 2 ≤ 4)
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  rw [← BinaryLinear.sylow_center_card_congr e S, hfour] at htwo
  omega

/-- None of the terminal components PSL₃(4), M₂₃, or J₂ is a fixed B.4 actor.
This discharges the fixed-group branch of the terminal small-ratio sieve. -/
theorem not_fixedCompetitor_of_exceptional {L : Type*} [Group L]
    (hm : ExceptionalModel L) : ¬ FixedCompetitor L := by
  intro hf
  exact l3Four_not_equiv_linearFourTwo (order20160_collision_of_exceptional_fixed hm hf)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
