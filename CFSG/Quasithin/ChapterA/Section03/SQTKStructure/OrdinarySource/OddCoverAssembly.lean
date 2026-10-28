module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Structure
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Held

/-!
# Discharging the sporadic covering inputs of A.3.6

The actual Held and J₄ odd-primary covering calculations supply their
entries in the ordinary-component assembly. Only the analogous Ree bound
remains. Together with genuine Theorems A and C, that bound gives all of
A.3.6, including the independently proved noncentral-Fitting branch.

Source: Aschbacher–Smith A.3.6 and I.1.3, printed pp.43–45, 407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure
open Chapter1.Section02
universe u

/-- The legacy covering-input record with both sporadic entries discharged. -/
theorem OrdinarySource.remainingOddCoverInputs_of_ree
    (hree : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L]
      (m : ℕ), 1 ≤ m → LocalModels.IsReeF4At (L ⧸ center L) m →
        IsPGroup 2 (center L)) : OrdinarySource.RemainingOddCoverInputs.{u} where
  ree := hree
  held := fun _L _ _ _ h => Held.OddPrimary.source_center_isPGroup h
  janko_four := fun _L _ _ _ h => Janko4.OddPrimary.source_center_isPGroup h

/-- The full A.3.6 source input from genuine earlier A/C and the remaining
Ree odd-primary bound. No sporadic covering premise remains. -/
theorem a36Input_of_theoremsAC_and_ree
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hree : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L]
      (m : ℕ), 1 ≤ m → LocalModels.IsReeF4At (L ⧸ center L) m →
        IsPGroup 2 (center L)) : A36Input.{u} KnownSimple.IsKnownSimple :=
  a36Input_of_theoremsAC_and_odd_covers hA hC
    (OrdinarySource.remainingOddCoverInputs_of_ree hree)

end CFSG.Quasithin.ChapterA.SQTKStructure
