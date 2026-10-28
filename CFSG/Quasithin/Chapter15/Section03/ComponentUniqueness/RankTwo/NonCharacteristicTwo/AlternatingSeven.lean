module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.AlternatingSeven.SourceInputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.AlternatingSeven.BlockStructure

/-!
# Excluding the alternating-seven alternative in 15.3.42

An actual A₇ model carries Y₊ and a Sylow two-subgroup of L to a solvable
Sylow overgroup in A₇. Compatible partition placement identifies Y₊ with
A₄ × C₃. Its center has order three and is characteristic in Y₊, and hence
normal in the original M ∩ I, contradicting F*(M ∩ I) = O₂(M ∩ I).

The triple cover is excluded separately by its center of order three. Thus
the complete literal alternative 1.1.5(3d), including the specified action,
is impossible. Only relative normality of L inside I is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.42,
printed p.1138, and 1.1.5(3d), printed pp.501--502.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven
variable {G : Type*} [Group G] [Finite G]
variable {I L M Yplus S : Subgroup G} [(L.subgroupOf I).Normal]

/-- The source product is derived from the actual A₇ embedding and the
preceding local conclusions. No placement or product is an extra premise. -/
theorem yplus_structure (h : ComponentSetup I L M Yplus S)
    (e : L ≃* alternatingGroup (Fin 7)) :
    Nonempty (Yplus ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 3))) := by
  obtain ⟨P, hn, hp, hrank, hsolv⟩ := model_input h e
  let := hsolv
  obtain ⟨f⟩ := model_equiv_a4_c3 (modelY (Yplus := Yplus) e) P hn hp hrank
  exact ⟨(modelYEquiv h e).trans f⟩

/-- The actual A₇ branch is incompatible with the earlier source conclusions. -/
theorem alternating_seven_impossible (h : ComponentSetup I L M Yplus S)
    (e : L ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨f⟩ := yplus_structure h e
  exact impossible_of_yplus_center_card h (center_card_of_equiv_a4_c3 f)

/-- Both the simple model and its nonsplit triple cover are excluded. In
particular this applies to the cycle structure 2³ in source case (d). -/
theorem alternating_action_seven_impossible (h : ComponentSetup I L M Yplus S)
    (α : MulAut L) (σ : Equiv.Perm (Fin 7))
    (ha : Candidates.ComponentStructure.AlternatingAction α 7 σ) : False := by
  obtain ⟨e⟩ := alternatingAction_has_simple_model h α σ ha
  exact alternating_seven_impossible h e

/-- Direct adapter for the catalogue on the component as a subgroup of I.
The central quotient in the cover alternative is retained in that type. -/
theorem relative_alternating_action_seven_impossible (h : ComponentSetup I L M Yplus S)
    (α : MulAut (L.subgroupOf I)) (σ : Equiv.Perm (Fin 7))
    (ha : Candidates.ComponentStructure.AlternatingAction α 7 σ) : False := by
  let f := subgroupOfEquivOfLe h.component_le
  rcases ha with ⟨e, _⟩ | ⟨_, ⟨e⟩, _⟩
  · exact alternating_seven_impossible h (f.symm.trans e)
  · exact no_three_center_of_center_eq h.center_eq ((centerCongr f).symm.trans e)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven
