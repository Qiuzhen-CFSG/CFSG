module

public import CFSG.Quasithin.MainForward.Chapter2Complete
public import CFSG.Quasithin.Chapter14.Section08.SourceCases

/-!
# The forward Main Theorem through the actual local quotient branches

The complete Chapter 2 theorem discharges the unique-overgroup case. For a
nonempty faithful local family, the Chapter 14 dispatcher constructs the
counterexample, applies the five-row quotient catalogue and constructs the
L₃(2) flag. Its A₅ branch may use the full Main-Theorem model output rather
than the narrower standalone D output. The empty-family input remains E.

The earlier source implications remain explicit, so this is a conditional
assembly. Source: Aschbacher--Smith, 14.8.1--2, pp.1078--1079, and the Main
Theorem proof, p.1166.
-/

public section
namespace CFSG.Quasithin.MainForward

open Subgroup Theory.GroupTheory ClassificationModels
open Chapter14.Section08.SourceCases

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The Main-Theorem reduction only needs the full model list in the nonempty
branch. Theorem 2.1.1 is supplied by its completed source proof. -/
theorem forward_of_nonempty_models_and_theoremE
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hnonempty : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      (faithfulLocalComponents T).Nonempty → IsQTKEModel G)
    (hE : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      faithfulLocalComponents T = ∅ → IsTheoremEModel G) : IsQTKEModel G := by
  have h211 (T : Sylow 2 G)
      (hu : ∃! M : Subgroup G, IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M) :
      IsTheorem211Model G := by
    obtain ⟨M, ⟨hM, hTM⟩, hunique⟩ := hu
    exact Chapter2.theorem_2_1_1 h T M hM hTM
      (fun N hN hTN => hunique N ⟨hN, hTN⟩)
  rcases forward_to_theoremD h h211 hE with hm | ⟨T, hmany, hne⟩
  · exact hm.toQTKEModel
  · exact hnonempty T hmany hne

/-- Apply the actual five-row dispatcher in the nonempty-family branch.
Every missing earlier source theorem remains visible as an input. -/
theorem forward_of_local_source_branches
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (caseOne : Chapter14.Section03.CaseOneSource.Earlier1332CaseOne.{u})
    (catalogue : Catalogue G) (unitary : UnitaryExclusion G)
    (six : SixRecognition G) (nonabelian : NonabelianRecognition G)
    (abelian : AbelianRecognition G) (five : FiveRecognition G)
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hE : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      faithfulLocalComponents T = ∅ → IsTheoremEModel G) : IsQTKEModel G := by
  apply forward_of_nonempty_models_and_theoremE h ?_ hE
  intro T hmany hne
  exact qtkeModel_of_source_branches structural caseOne catalogue unitary six
    nonabelian abelian five h T hmany hne

end CFSG.Quasithin.MainForward
