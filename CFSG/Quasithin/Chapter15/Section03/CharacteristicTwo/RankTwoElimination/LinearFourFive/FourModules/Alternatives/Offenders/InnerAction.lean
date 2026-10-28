module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Offenders.Quotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.LocalSetup

/-!
# Using the prepared inner Sylow action

Inner conjugation by R, together with inner conjugation by L itself,
gives inner conjugation by LR. The preparation module's actual S-action
restricts to this R-action when R ≤ S. The comparison is checked on the
literal quotient representatives, so it assumes no action-image marking.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), first
paragraph of 15.3.24, printed p.1129.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Offenders
variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)

/-- Innerness on the supplement extends to the generated overgroup. -/
theorem inner_on_join (hn : d.R ≤ normalizer (L : Set G))
    (hi : ∀ r : d.R, pCoreJoinAction 2 hn (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L)) :
    ∀ g : (L ⊔ d.R : Subgroup G), pCoreJoinAction 2 hn g ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  let H := L ⊔ d.R
  let N := (MulAut.innerSubgroup (L ⧸ pCore 2 L)).comap (pCoreJoinAction 2 hn)
  have hL : L ≤ N.map H.subtype := by
    intro l hl
    refine ⟨inclusion le_sup_left ⟨l, hl⟩, ?_, rfl⟩
    change pCoreJoinAction 2 hn (inclusion le_sup_left ⟨l, hl⟩) ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L)
    rw [pCoreJoinAction_on_component]
    exact ⟨_, rfl⟩
  have hR : d.R ≤ N.map H.subtype := by
    intro r hr
    exact ⟨inclusion le_sup_right ⟨r, hr⟩, hi ⟨r, hr⟩, rfl⟩
  intro g
  obtain ⟨x, hx, he⟩ := (sup_le hL hR) g.property
  have he' : x = g := Subtype.ext he
  exact he' ▸ hx

/-- The exact preparation conclusion supplies the inner LR-action used for offenders. -/
theorem inner_on_join_of_sylow
    (hn : d.R ≤ normalizer (L : Set G))
    (hS : d.S ≤ normalizer (L : Set G)) (hRS : d.R ≤ d.S)
    (hi : Preparation.IsInnerOnComponent d L hS) :
    ∀ g : (L ⊔ d.R : Subgroup G), pCoreJoinAction 2 hn g ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  apply inner_on_join d L hn
  intro r
  have he : pCoreJoinAction 2 hn (inclusion le_sup_right r) =
      Preparation.sylowCoreAction d L hS (inclusion hRS r) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
    rw [pCoreJoinAction_mk, Preparation.sylowCoreAction_apply]
    rfl
  rw [he]
  exact hi _

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Offenders

end
