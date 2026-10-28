module

public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.LinearThreeAt

/-!
# The final five-row dispatcher with structure at the original G,T

The maximal-counterexample construction and the five-quotient catalogue are
unchanged. In the L₃(2) row, the local Chapter12 adapter chooses the actual Irr⁺
module, marks its literal quotient action, constructs its invariant flag and
splits its conjugate span. Only structure and naturality at the original G,T
are used. The caller can therefore supply both after obtaining |M(T)| > 1.

The strict D conclusion still requires the two specific A₅ models. The
separate full-model conclusion accepts the existing A₅ terminal output. All
source inputs remain explicit, and the universal public endpoints are retained
in `SourceCases`. Source: Aschbacher--Smith, 14.8.1--2, pp.1078--1079.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases.At

open Subgroup Theory.GroupTheory ClassificationModels
open Chapter1.Section02.LocalModels
open Chapter12.Section02
open Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
variable (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (caseOne : Earlier1332CaseOneAt T)
  (catalogue : Catalogue G) (unitary : UnitaryExclusion G)
  (six : SixRecognition G) (nonabelian : NonabelianRecognition G)
  (abelian : AbelianRecognition G)

include structural caseOne catalogue unitary six nonabelian abelian

/-- Select the original maximal counterexample and exhaust its five quotient
rows, using the local module/flag construction in the linear-three row. -/
theorem theoremDModel_or_five_counterexample
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) :
    IsTheoremDModel G ∨ ∃ L : Subgroup G,
      Maximal (Counterexample T) L ∧ IsAlternating (L ⧸ pCore 2 L) 5 := by
  classical
  by_cases hD : IsTheoremDModel G
  · exact Or.inl hD
  obtain ⟨L, hmax⟩ :=
    LieTypeBranch.exists_maximal_counterexample_of_not_theoremDModel h T hne hD
  have d := hmax.1
  have hm : MidSizeModel (L ⧸ pCore 2 L) :=
    (catalogue T L hmany d L d.local_component).2
  rcases hm with h5 | h3 | h6 | hc6 | hu
  · exact Or.inr ⟨L, hmax, h5⟩
  · exact Or.inl (SourceAssembly.At.theoremDModel_of_linearThree
      structural caseOne nonabelian abelian d h3 hmany)
  · rcases six T L hmany hmax (Or.inl h6) with hs | hu
    · exact (d.no_symplectic_six hs).elim
    · exact (d.no_unitary_four hu).elim
  · rcases six T L hmany hmax (Or.inr hc6) with hs | hu
    · exact (d.no_symplectic_six hs).elim
    · exact (d.no_unitary_four hu).elim
  · exact (unitary T L hmany d hu).elim

/-- The original narrower D output, conditional on the precise source 13.6.1
pair of A₅ models. No full-model conclusion is narrowed implicitly. -/
theorem theoremDModel_of_source_branches
    (five : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Maximal (Counterexample T) L →
      IsAlternating (L ⧸ pCore 2 L) 5 →
        ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) : IsTheoremDModel G := by
  rcases theoremDModel_or_five_counterexample structural caseOne catalogue unitary
    six nonabelian abelian h hmany hne with hD | ⟨L, hmax, h5⟩
  · exact hD
  · rcases five T L hmany hmax h5 with hu | hl
    · exact .exceptional (.unitary_binary hu)
    · exact .exceptional (.linear_three hl)

/-- The full-model output needed by MainForward, using the actual A₅ source
endpoint and structure at this same Sylow subgroup only. -/
theorem qtkeModel_of_source_branches (five : FiveRecognition G)
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : (MainForward.faithfulLocalComponents T).Nonempty) : IsQTKEModel G := by
  rcases theoremDModel_or_five_counterexample structural caseOne catalogue unitary
    six nonabelian abelian h hmany hne with hD | ⟨L, hmax, h5⟩
  · exact hD.toQTKEModel
  · exact five T L hmany hmax h5

end CFSG.Quasithin.Chapter14.Section08.SourceCases.At
