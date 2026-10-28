module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesDefs

/-!
# The chosen-seed trichotomy feeds ambient-local structural assembly

The first source alternative identifies the full normalizer orbit with V;
the second identifies the Sylow orbit with V and has trivial fixed space.
After the marked doubled branch is excluded, these orbit equalities imply
the precise normalizer containments used by Structural1222At. Independent
normalization still supplies existence of a chosen module.

The 3.2.5 producer, the 7.0.1/12.1.11 exclusion, and normalization all retain
the actual multiple-overgroup premise. This is their conditional assembly.
Source: Aschbacher--Smith, 12.2.2, printed p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Connect the literal producer trichotomy and its independently owned
doubled-branch exclusion to all clauses of the local structural theorem. -/
theorem structural1222At_of_source325_of_not_doubled_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (normalization : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      SourceNormalization1222At KnownSimple.IsKnownSimple T)
    (alternatives : ∀ (L V : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.Source325Alternatives)
    (exclude : ∀ (L V : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → ¬ D.MarkedDoubled) :
    Structural1222At KnownSimple.IsKnownSimple T := by
  apply structural1222At_of_source_branches (normalization hmany)
  intro L V h D
  rcases alternatives L V hmany h D with ⟨_, hU⟩ | ⟨hW, hc, _⟩ | hd
  · exact Or.inl (hU ▸ le_normalizer_componentOrbit V (normalizer (L : Set G)))
  · exact Or.inr ⟨hW ▸ le_normalizer_componentOrbit V (T : Subgroup G), hc⟩
  · exact (exclude L V hmany h D hd).elim

end CFSG.Quasithin.Chapter12.Section02
