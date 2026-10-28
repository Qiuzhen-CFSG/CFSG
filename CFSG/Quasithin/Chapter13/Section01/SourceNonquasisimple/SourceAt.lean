module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Assembly
public import CFSG.Quasithin.Chapter13.Section01.SourceQuasisimple.ClassificationAt

/-!
# Source 13.1.7 and the literal 13.3.2 application at G,T

The five-model refinement constructs the exact earlier quasisimple rigidity
and classification inputs. The assembled nonquasisimple argument then excludes
every member of L⁺(G,T), not only maximal members. Finally the maximal-overgroup
argument identifies every faithful member with its maximal overgroup and gives
its Sylow normalization and unchanged five-model quotient.

Only the pointwise structural and module theorems of 12.2.2 and the
larger-linear exclusion of 12.9.1 remain explicit. Their existing producers
are qt-d-1222-source, qt-d-1222-modules, qt-d-1222-normalization and
qt-d-1291-source; qt-d-1317-source retains final discharge. The original
Hypothesis1311/Hypothesis1331 and multiple-overgroup guard are preserved.
Source: Aschbacher--Smith, 13.1.2, 13.1.7 and 13.3.2(1--2),
printed pp.866,868--876,884--885.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter12.Section02 SourceNonquasisimple SourceQuasisimple
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- Source 13.1.7 in the guarded branch, with every Chapter13 local premise
discharged. The remaining premises are precisely the named Chapter12 inputs. -/
theorem Hypothesis1311.nonquasisimpleFaithful_eq_empty_of_source_inputs_at
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (larger : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (XiQuotient I) n 2) :
    nonquasisimpleFaithful T = ∅ := by
  obtain ⟨hrig,hclass⟩ := quasisimple_sources_of_inputs_at h hmany structural modules larger
  exact nonquasisimpleFaithful_eq_empty_of_quasisimple_sources h hmany hrig hclass

/-- Every actual faithful member has quasisimple quotient by its own
two-core, including the originally selected nonmaximal member. -/
theorem Hypothesis1311.faithful_quasisimple_of_source_inputs_at
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (larger : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (XiQuotient I) n 2)
    {L : Subgroup G} (hL : L ∈ MainForward.faithfulLocalComponents T) :
    IsQuasisimple (XiQuotient L) := by
  by_contra hn
  have hm : L ∈ nonquasisimpleFaithful T := ⟨hL,hn⟩
  rw [h.nonquasisimpleFaithful_eq_empty_of_source_inputs_at hmany structural modules larger] at hm
  exact hm

/-- The actual 13.3.2(1--2) contract for every member of the faithful family,
with maximal quasisimplicity and the five-model catalogue both constructed. -/
theorem Hypothesis1311.source1332OneTwo_of_source_inputs_at
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (larger : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (XiQuotient I) n 2) :
    Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T := by
  apply SourceAssembly.At.source1332OneTwo_of_maximal_models h _ _ structural
  · intro I hf
    exact h.faithful_quasisimple_of_source_inputs_at hmany structural modules larger
      ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T I).mpr ⟨hf.1.1,hf.2⟩)
  · intro I hi
    exact FiveQuotients.midSize
      (fiveQuotients_of_source_inputs_at h hmany structural modules larger hi)

end CFSG.Quasithin.Chapter13.Section01

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Eliminate the literal nonquasisimple branch of Hypothesis 13.3.1.
No replacement of its distinguished subgroup or Sylow subgroup is made. -/
theorem Hypothesis1331.quasisimple_of_source_inputs_at
    (h : Hypothesis1331 T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (larger : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (XiQuotient I) n 2) :
    IsQuasisimple (XiQuotient L) :=
  h.hypothesis1311.faithful_quasisimple_of_source_inputs_at
    hmany structural modules larger h.local_component

/-- Supply the full family normality/catalogue input at the original
13.3.1 consumer, retaining only the earlier Chapter12 source obligations. -/
theorem Hypothesis1331.source1332OneTwo_of_source_inputs_at
    (h : Hypothesis1331 T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (larger : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (XiQuotient I) n 2) :
    Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T :=
  h.hypothesis1311.source1332OneTwo_of_source_inputs_at hmany structural modules larger

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
