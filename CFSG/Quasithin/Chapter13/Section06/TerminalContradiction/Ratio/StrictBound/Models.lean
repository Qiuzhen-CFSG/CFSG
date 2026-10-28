module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.Source
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Definitions
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The actual residual models in the terminal ratio argument

The component in 13.6.27 is identified by its intrinsic two-core quotient.
The following paragraph uses instead its image in H/O₂(H), after resetting
K to H∞. The C-component quotient equivalence identifies these groups.
We transport the given model markings through that equivalence and the
literal residual image; PSL₃(4) is not replaced by SL₃(4).

`ExceptionalModel` records just the three resulting group isomorphisms.
It is not the full 13.6.27 hypothesis: the source `Components.Conclusion`
also retains generation, the prime-to-three residual alternatives, and
the actual nontrivial diagram action. Those clauses remain available to
the final strict-bound assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
13.6.27 and the terminal paragraph of §13.6, printed pp.934–935.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound

/-- Actual group equivalences, extracted from the complete source alternatives.
This predicate alone does not encode their diagram or generation clauses. -/
def ExceptionalModel (L : Type*) [Group L] : Prop :=
  Nonempty (L ≃* Components.L3Four) ∨
    Nonempty (L ≃* Sporadic.Mathieu.M23) ∨
    Nonempty (L ≃* Sporadic.LeechRelated.J2.Carrier)

open Section08
variable {G : Type*} [Group G] [Finite G]

private theorem quasisimple_of_fitting_cComponent
    {X : Type*} [Group X] [Finite X]
    (h : (generalizedFitting X).IsCComponent) : IsQuasisimple (generalizedFitting X) := by
  classical
  by_cases hex : ∃ D : Subgroup X, IsComponent X D
  · obtain ⟨D, hD⟩ := hex
    let := hD.2
    have hn : D ≠ ⊥ := hD.isCComponent.ne_bot
    have hd := component_le_generalizedFitting X D hD
    have he : D = generalizedFitting X := le_antisymm hd
      (h.minimal D hd hn inferInstance hD.1)
    exact he ▸ hD.2
  · have he : componentLayer X = ⊥ := by
      apply le_bot_iff.mp
      apply sSup_le
      intro D hD
      exact (hex ⟨D, hD⟩).elim
    have hf : generalizedFitting X = fittingSubgroup X := by
      simp only [generalizedFitting, he, sup_bot_eq]
    have hs : Group.IsSolvable (generalizedFitting X) := hf.symm ▸ inferInstance
    exact (h.not_isSolvable hs).elim

/-- The source component quotient and the residual image are compared by
an actual equivalence; the generalized-Fitting identity uses that same image.
This is transport of an explicit 13.6.27 output, not a proof of 13.6.27. -/
theorem residual_model_of_source (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S) :
    generalizedFitting (Source.Hstar H) = Source.starImage H (terminalResidual H) ∧
      ExceptionalModel (Source.starImage H (terminalResidual H)) := by
  obtain ⟨K, hK, halt, _, hfit, hres⟩ := hs
  have heq : Source.starImage H (terminalResidual H) = Components.componentImage K := by
    rw [Source.starImage, terminalResidual_subgroupOf, hres]
    rfl
  refine ⟨hfit.trans heq.symm, ?_⟩
  let e : (K ⧸ pCore 2 K) ≃* Source.starImage H (terminalResidual H) :=
    (cComponentTwoCoreQuotientEquiv hK).trans (MulEquiv.subgroupCongr heq.symm)
  rcases halt with ⟨_, hJ | hM⟩ | ⟨f, _, _, _⟩
  · exact Or.inr (Or.inr ⟨e.symm.trans (Classical.choice hJ)⟩)
  · exact Or.inr (Or.inl ⟨e.symm.trans (Classical.choice hM)⟩)
  · exact Or.inl ⟨e.symm.trans f⟩

/-- Quasisimplicity follows from the source component and F* identity.
No independent simplicity certification of any sporadic carrier is needed:
a nonsolvable C-component equal to F* contains an ordinary component,
and minimality forces equality with it. -/
theorem residual_quasisimple_of_source (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S) :
    IsQuasisimple (Source.starImage H (terminalResidual H)) := by
  have hfit := (residual_model_of_source H S hs).1
  have hc : (Source.starImage H (terminalResidual H)).IsCComponent := by
    obtain ⟨K, hK, _, _, _, hres⟩ := hs
    rw [Source.starImage, terminalResidual_subgroupOf, hres]
    let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
    exact hK.map_quotient (pCore 2 H)
  exact hfit ▸ quasisimple_of_fitting_cComponent (hfit.symm ▸ hc)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound
