module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalClassificationOpening
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalClassificationRows

/-!
# The group and chosen-module clauses of the local 12.3.2 classification

The original residual is a generating component. The maximal case has
A₅ quotient by its own two-core and the orthogonal chosen central action;
every proper overcomponent has literal central quotient A₇. The earlier
A₇ exclusion, restricted to the same G and T, therefore gives maximal
faithfulness of O²(H). No whole omega-span decomposition follows merely
from the classification of its chosen Irr⁺ sections.

The source A₇ exclusion and the whole moved-module conclusion remain
explicit obligations of the original 12.3.2 assembly. In the actual D
application, the A₇ producer additionally retains Hypothesis1311 T.
Source: Aschbacher–Smith, 12.2.7 and 12.3.2, printed pp.797–798,807.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02 Section02.RecognitionSource ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L H : Subgroup G}

/-- The nonsolvable local residual has either its own maximal A₅ structure
or a proper A₇ overcomponent, with the exact central quotient convention. -/
theorem local_residual_five_or_seven
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    (Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) ∧
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) ∧
      ∀ (W : Subgroup G) (E : ChosenModule T (localResidual H) W),
        letI := E.actionCentralizer_normal
        Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 5))) ∨
    ∃ Y : Subgroup G, localResidual H < Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y ∧
      Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)) ∧
      ∀ (W : Subgroup G) (E : ChosenModule T Y W),
        (T : Subgroup G) ≤ normalizer (W : Set G) ∧
        (Module.finrank (ZMod 2) E.space = 4 ∨ Module.finrank (ZMod 2) E.space = 6) := by
  obtain ⟨C,Y,hKY,hY⟩ := local_residual_overcomponent h structural modules hZ hH hs
  have hp := local_hstar_minimalParabolic (structural L h).1 hH hs
  by_cases he : localResidual H = Y
  · have hK : Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) := he.symm ▸ hY
    have hp' (J : Subgroup G) (heJ : J = H) (hTJ : (T : Subgroup G) ≤ J) :
        ChapterB.IsMinimalParabolicOver (T.subtype hTJ) ⊤ := by
      subst J
      exact hp
    have hpk := hp' _ (localResidual_supplement hH.1.1.2) le_sup_right
    have each (W : Subgroup G) (E : ChosenModule T (localResidual H) W) :=
      E.five_of_minimalParabolic hK ((structural _ hK).2.2 W E).1 hpk (modules _ W hK E)
    obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural _ hK).2.1
    exact Or.inl ⟨hK,(each W E).1,fun W E => (each W E).2⟩
  · have hlt := lt_of_le_of_ne hKY he
    obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
    exact Or.inr ⟨Y,hlt,hY,
      (C.proper_seven_source_of_parabolic structural modules hH hp hlt hY E).1,
      fun W E => (C.proper_seven_source_of_parabolic structural modules hH hp hlt hY E).2⟩

/-- The group and chosen-action clauses of 12.3.2, conditional only on the
literal earlier A₇ exclusion at this same G,T. This does not assert the
one-or-two model on the entire moved omega-span. -/
theorem local_residual_maximal_five_of_seven_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hZ : centralizer (sylowCenterSeed T : Set G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7))) :
    Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) ∧
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) ∧
      ∀ (W : Subgroup G) (E : ChosenModule T (localResidual H) W),
        letI := E.actionCentralizer_normal
        Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 5)) := by
  rcases local_residual_five_or_seven h structural modules hZ hH hs with hf | ⟨Y,_,hY,he,_⟩
  · exact hf
  · exact (seven Y hY he).elim

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
