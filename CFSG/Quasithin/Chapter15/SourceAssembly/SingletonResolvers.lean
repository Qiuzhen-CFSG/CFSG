module

public import CFSG.Quasithin.Chapter15.SourceAssembly.MSClassifications

/-!
# Final E assembly from the separate MS fields and singleton resolvers

The C.1.32 and C.1.34 producers supply the two fields of the same earlier
classification record. In the singleton-centralizer branch, apply the
pointwise 15.1.3 theorem only after retaining its actual singleton hypothesis.
The centralizing continuation may use the rank-two resolver for this same Mc.
The existing MS endpoint then supplies both characteristic-two exclusions
and the final centralizer case split.

This is a conditional assembly: neither MS field nor either branch resolver
is proved here. Their source proofs remain necessary for unconditional E.

Source: Aschbacher--Smith C.1.32/34, 15.1.3 and 15.4.25 (Theorem E),
printed pp.135--137, 1086 and 1165.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15
open Section03 ChapterA.Section05To06
open CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Assemble E from its four independent source inputs, preserving every
C.1.34 quotient/module layer and restricting the resolvers to the actual
singleton centralizer. The centralizing producer may depend on the rank-two
producer, without requiring either resolver for arbitrary Mc. -/
theorem source_theoremE_of_MS_fields_and_singleton_resolvers
    (rankTwo : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple L R → RankTwoAlternatives L R)
    (linearThree : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple L R → ∀ (n : ℕ), 1 ≤ n →
      ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) →
      ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
        ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F,
          MSModuleAlternatives L R S n F e)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hrank : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
        Section01.RankTwoResolver T Mc)
    (hcentral : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
        Section01.RankTwoResolver T Mc → Section01.CentralizingResolver T Mc) :
    ClassificationModels.IsTheoremEModel G := by
  let earlier : EarlierMSClassifications KnownSimple.IsKnownSimple :=
    { rankTwo := rankTwo, linearThree := linearThree }
  apply source_theoremE_of_MS_classifications earlier hG T hmany hempty
  intro Mc hu
  have hr : Section01.RankTwoResolver T Mc := hrank Mc hu
  exact Section01.source_lemma_15_1_3_of_branch_resolvers hG T hempty hu hmany
    hr (hcentral Mc hu hr)

end CFSG.Quasithin.Chapter15
