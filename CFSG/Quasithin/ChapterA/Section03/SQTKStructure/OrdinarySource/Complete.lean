module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.OddCoverAssembly
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Complete

/-!
# A.3.6 with the complete actual covering catalogue

Every ordinary-component covering calculation is now proved, including the
Ree, Held and J₄ cases. The raw ordinary-component theorem only needs its
actual Theorem C model. The full SQTK assembly retains exactly the genuine
earlier universal Theorems A and C; it adds no cover or classification premise.

Source: Aschbacher–Smith A.3.6, printed pp.43–45.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure
open Chapter1.Section02
universe u

theorem OrdinarySource.remainingOddCoverInputs : OrdinarySource.RemainingOddCoverInputs.{u} := by
  apply OrdinarySource.remainingOddCoverInputs_of_ree
  intro L _ _ _ m hm h
  obtain ⟨d, ⟨e⟩⟩ := h
  exact ReeF4.CentralCovers.OddPrimary.localBlock_center_isPGroup m hm d e

/-- The complete raw ordinary-component source case, suitable for proper-section induction. -/
theorem OrdinarySource.ordinary_conclusion_of_model
    {X : Type u} [Group X] [Finite X] (hcore : pCore 2 X = ⊥)
    (L : Subgroup X) (hL : IsComponent X L)
    (hmodel : LocalModels.TheoremCModel (L ⧸ center L)) : A36Conclusion L :=
  OrdinarySource.ordinary_conclusion OrdinarySource.remainingOddCoverInputs hcore L hL hmodel

theorem a36Input_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X) : A36Input.{u} KnownSimple.IsKnownSimple :=
  a36Input_of_theoremsAC_and_odd_covers hA hC OrdinarySource.remainingOddCoverInputs

/-- The literal B.5.2 quotient consumer, with all covering inputs discharged. -/
theorem quasisimple_twoCore_quotient_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X)
    {H : Type u} [Group H] [Finite H] (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {C : Subgroup H} (hc : C.IsCComponent) [Group.IsNilpotent (solvableRadical C)] :
    IsQuasisimple (C ⧸ pCore 2 C) :=
  quasisimple_twoCore_quotient_of_sources hA hC OrdinarySource.remainingOddCoverInputs hH hc

end CFSG.Quasithin.ChapterA.SQTKStructure
