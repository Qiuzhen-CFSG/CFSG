module
public import CFSG.Quasithin.Chapter12.Section09.SourceAt.NaturalBranch
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourceReduction.Completion
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.CompleteAt
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.LargerLinearInput

/-!
# The larger-linear source at the original ambient group and Sylow

The proved degree-five reduction supplies the original chosen module's full
natural marking. Its exclusion then supplies the preference condition for
degree four. Only the original degree-four natural reduction remains explicit;
the earlier structural and module results concern the same G,T. Recognition,
point-span abelianity, fusion and the terminal contradiction are constructed.

Source: Aschbacher--Smith 12.5.1,12.9.1 and 13.1.2(3), printed pp.816--822,
857--866, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section09 Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {I : Subgroup G} {n : ℕ}

/-- The original degree-five row is excluded using the proved 12.5.1 source. -/
theorem largerLinear_five_excluded_of_local_source
    (h : Hypothesis1311 T)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hi : Hypothesis1223 KnownSimple.IsKnownSimple T I) :
    ¬ ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 5 2 := by
  intro hq
  obtain ⟨⟨W,⟨D⟩⟩⟩ := (structural I hi).2.1
  have natural := Chapter12.Section05.NaturalSource.naturalModule_from_source
    hi D structural modules hq
  obtain ⟨hs⟩ := largerLinear_higherRank_of_natural h hi D (Or.inr rfl) hq natural
  exact SourceAt.natural_branch_contradiction_from_source hs (Or.inr rfl)
    (by intro he; omega) structural modules
    (RecognitionSource.theorem12213_of_modules_of_many_at structural modules hmany)

/-- Both larger rows are excluded once the genuine initial degree-four
naturality source is supplied at the same G,T. No universal earlier record,
degree-five reduction or terminal callback is required. -/
theorem largerLinear_excluded_of_local_source
    (h : Hypothesis1311 T)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (four : ∀ L V : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2 →
        NaturalModule D 4)
    (hi : Hypothesis1223 KnownSimple.IsKnownSimple T I) (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (I ⧸ pCore 2 I) n 2 := by
  have no_five := fun (J : Subgroup G) (hj : Hypothesis1223 KnownSimple.IsKnownSimple T J) =>
    largerLinear_five_excluded_of_local_source h structural modules hmany hj
  rcases hn with rfl | rfl
  · intro hq
    obtain ⟨⟨W,⟨D⟩⟩⟩ := (structural I hi).2.1
    obtain ⟨hs⟩ := largerLinear_higherRank_of_natural h hi D (Or.inl rfl) hq
      (four I W hi D hq)
    exact SourceAt.natural_branch_contradiction_from_source hs (Or.inl rfl)
      (fun _ => no_five) structural modules
      (RecognitionSource.theorem12213_of_modules_of_many_at structural modules hmany)
  · exact no_five I hi

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
