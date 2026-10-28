module

public import Theory.SpecificGroups.AlternatingSix.SylowFixedOddCore
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# The A₆ and central three-cover cases of the E.6.19 inspection

A faithful acting group containing Inn(L), with an order-two subgroup fixing
an actual Sylow two-subgroup pointwise, has trivial odd core in that actor's
centralizer when L is A₆ or its perfect central three-cover. The intrinsic A₆
calculation uses its natural S₆ automorphisms, the fixed groups D₈ and S₄,
and the outer quotient of order four.

For the cover we transport the action through the actual central quotient
isomorphism. Perfectness preserves faithfulness and the inner-action and
Sylow-fixing hypotheses. The acting group H and its subgroup E stay unchanged,
so the conclusion concerns the original centralizer in H.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and E.6.19, printed p.252 (PDF p.263).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
open Chapter1.Section02.LocalModels
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
variable {L : Subgroup G} {φ : H →* MulAut L} {E : Subgroup H}

/-- The A₆ case retains an actual isomorphism with the six-point alternating group. -/
theorem alternating_six_oddCore_eq_bot
    (d : Theory.GroupAction.SylowFixedInvolution φ E) (hL : IsAlternating L 6) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  obtain ⟨e⟩ := hL
  exact AlternatingSix.ShadowLocal.sylowFixedInvolution_centralizer_oddCore_eq_bot
    _ E (d.equiv e)

/-- The perfect central three-cover has the same centralizer conclusion on H. -/
theorem alternating_six_cover_oddCore_eq_bot
    (d : Theory.GroupAction.SylowFixedInvolution φ E) (hL : IsAlternatingCover L 6) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  let _ : IsQuasisimple L := hL.1
  obtain ⟨e⟩ := hL.2.2
  exact AlternatingSix.ShadowLocal.sylowFixedInvolution_centralizer_oddCore_eq_bot
    _ E (d.centralQuotient e)

/-- Neither six-point model can realize the odd-core obstruction in E.6.19. -/
theorem alternating_six_or_cover_oddCore_eq_bot
    (d : Theory.GroupAction.SylowFixedInvolution φ E)
    (hL : IsAlternating L 6 ∨ IsAlternatingCover L 6) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  rcases hL with hL | hL
  · exact alternating_six_oddCore_eq_bot d hL
  · exact alternating_six_cover_oddCore_eq_bot d hL

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
