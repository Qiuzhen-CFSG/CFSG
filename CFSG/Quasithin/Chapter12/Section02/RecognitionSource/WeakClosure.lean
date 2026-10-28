module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.GlobalTI
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic

/-!
# The weak-closure centralization step in 12.2.17

Global TI and normalization by T make every conjugate of the original V
inside T commute with V, by the elementary two-group case of I.6.2.
Their literal weak closure W₀(T,V) therefore centralizes V. The natural-row
application supplies global TI from the actual action and no escape.

This proves the centralization step. The equality C_T(V)=O₂(LT) and the
subsequent normalizer bound remain part of the source local analysis.
Source: Aschbacher--Smith, 12.2.17, printed p.800.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterE
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

theorem chosen_conjugates_in_sylow_centralize
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hTI : IsTISubgroup V)
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  let := D.elementary
  have hn := ((structural G T L h).2.2 V D).1
  have hi : (normalizer (V : Set G)).relIndex (T : Subgroup G) < Nat.card V := by
    rw [relIndex_eq_one.mpr hn]
    exact (Subgroup.one_lt_card_iff_ne_bot V).mpr D.ne_bot
  exact hTI.conjugate_le_centralizer_of_index V (T : Subgroup G)
    T.isPGroup' D.le_sylow hi g hg

theorem chosen_weakClosure_zero_centralizes
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hTI : IsTISubgroup V) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      0 < globalW V (T : Subgroup G) := by
  have hall := chosen_conjugates_in_sylow_centralize h D structural hTI
  constructor
  · apply le_inf (indexedWeakClosure_le V (T : Subgroup G) 0)
    rw [weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    obtain ⟨g, rfl, hg⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
    exact hall g hg
  · apply bot_lt_iff_ne_bot.mpr
    intro he
    obtain ⟨g, hg, hn⟩ := (globalW_eq_zero_iff V (T : Subgroup G)).mp he
    exact hn (hall g hg)

/-- The source natural row has the original W₀-centralization conclusion
without a TI callback. -/
theorem natural_weakClosure_zero_centralizes
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V) {d : ℕ}
    (hnatural : Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d)) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      0 < globalW V (T : Subgroup G) :=
  chosen_weakClosure_zero_centralizes h D structural
    (globalTI_of_natural h D structural hnone hnatural)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
