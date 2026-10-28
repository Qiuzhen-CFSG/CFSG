module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Models
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.Source
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ModelFacts.Carriers
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ModelFacts.LinearOuter
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ModelFacts.Actions

/-!+# Structural model facts for the terminal constituent reduction

The complete component conclusion identifies the actual residual image
L in X = H/O₂(H) with PSL₃(4), M₂₃, or J₂, and identifies L with F*(X).
Each carrier has trivial center and an explicit involution. Their actual
outer orders divide twelve, one, and two respectively. Conjugation on L
therefore embeds every elementary binary subgroup of X disjoint from L
in an outer group whose order divides twelve; such a subgroup has rank
at most two.

`residual_structural_facts_of_source` supplies exactly the group hypotheses
of the faithful-section and constituent reductions, and the involution
used in the B.4 degree obstruction. Quasisimplicity is inherited from the
source C-component through `Models`; it is not an extra model premise.
This module supplies structural inputs to the terminal strict-bound
assembly, rather than asserting that representation-theoretic conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 13.6.27
and the terminal paragraph of §13.6, printed pp.934–935 / PDF pp.951–952.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound

namespace ModelFacts

/-- A uniform divisibility bound for the actual outer groups of the three
terminal models, transported along their genuine multiplicative equivalences. -/
theorem exceptional_outer_card_dvd {L : Type*} [Group L] (h : ExceptionalModel L) :
    Nat.card (MulAut.Outer L) ∣ 12 := by
  unfold ExceptionalModel at h
  rcases h with h | h | h <;> let e := Classical.choice h
  · rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact l3Four_outer_card_dvd
  · rw [Nat.card_congr (MulAut.outerCongr e).toEquiv, m23_outer_card]
    exact one_dvd _
  · rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact j2_outer_card_dvd.trans (by decide)

end ModelFacts

open Section08 ModelFacts
variable {G : Type*} [Group G] [Finite G]

/-- The center hypothesis in the faithful star-section construction follows
from the complete component conclusion, on its literal residual image. -/
theorem residual_center_of_source (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S) :
    center (Source.starImage H (terminalResidual H)) = ⊥ :=
  exceptional_center (residual_model_of_source H S hs).2

/-- An involution in the actual residual image, supplying the degree
obstruction used to exclude the B.4 exceptional module alternatives. -/
theorem residual_involution_of_source (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S) :
    ∃ t : Source.starImage H (terminalResidual H), orderOf t = 2 :=
  exceptional_involution (residual_model_of_source H S hs).2

/-- Every elementary binary actor disjoint from the terminal component has
rank at most two. The actor is a subgroup of the literal star quotient. -/
theorem disjoint_residual_rank_le_two_of_source (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S) (A : Subgroup (Source.Hstar H))
    (hA : IsElementaryTwo A) (hd : Disjoint A (Source.starImage H (terminalResidual H))) :
    rank A ≤ 2 := by
  obtain ⟨hfit, hmodel⟩ := residual_model_of_source H S hs
  exact rank_le_two_of_injective_outer H hfit (exceptional_center hmodel)
    (exceptional_outer_card_dvd hmodel) A hA hd

/-- Source-specialized kernels: conjugation is faithful and the outer
action kills exactly the residual image, with no undischarged center premise. -/
theorem residual_action_kernels_of_source (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S) :
    (residualConjugation H).ker = ⊥ ∧
      (residualOuterAction H).ker = Source.starImage H (terminalResidual H) := by
  have hf := (residual_model_of_source H S hs).1
  have hz := residual_center_of_source H S hs
  exact ⟨residualConjugation_kernel H hf hz, residualOuterAction_kernel H hf hz⟩

/-- Conjugation gives a faithful action of the actual quotient X/L on Out(L). -/
theorem residual_outer_quotient_injective_of_source (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S) :
    Function.Injective (MulAut.outerAction (Source.starImage H (terminalResidual H))) :=
  MulAut.outerAction_injective _
    (residual_centralizer H (residual_model_of_source H S hs).1
      (residual_center_of_source H S hs))

/-- The complete group input for Sections and the terminal constituent
reduction, with its center, involution, and actor-rank premises discharged. -/
theorem residual_structural_facts_of_source (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S) :
    generalizedFitting (Source.Hstar H) = Source.starImage H (terminalResidual H) ∧
      IsQuasisimple (Source.starImage H (terminalResidual H)) ∧
      center (Source.starImage H (terminalResidual H)) = ⊥ ∧
      (∃ t : Source.starImage H (terminalResidual H), orderOf t = 2) ∧
      ∀ A : Subgroup (Source.Hstar H), IsElementaryTwo A →
        Disjoint A (Source.starImage H (terminalResidual H)) → rank A ≤ 2 :=
  ⟨(residual_model_of_source H S hs).1, residual_quasisimple_of_source H S hs,
    residual_center_of_source H S hs, residual_involution_of_source H S hs,
    fun A hA hd => disjoint_residual_rank_le_two_of_source H S hs A hA hd⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound
