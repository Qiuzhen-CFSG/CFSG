module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison.Marking
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison.StarRow

/-!
# Assembly of the contained-component comparison in original 14.6.15

The literal image of K₁ retains its two-core quotient, and B normalizes
that image. A natural block and its core-quotient Sylow normalizer give a
compatible natural module and standard Borel marking, so the proved
natural-Borel contradiction applies.

The source row selection and original-block reconstruction remain explicit
premises here. This file does not assert the unconditional comparison.

Source: Aschbacher--Smith 14.6.15, printed p.1035, using C.2.7(3), pp.145--147.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : EscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- Apply the genuine row geometry to the original normalizer and intersection. -/
theorem contained_row_geometry (h : d.K1 ≤ j.J)
    (row : NaturalStarRow j.J (Mc.pCoreIn 2)) :
    Chapter1.IsSylowIn 2
      (starImage j.J (Mc.pCoreIn 2) (Stellmacher.elementaryAbelianMaxJ (Mc.pCoreIn 2)))
      (starImage j.J (Mc.pCoreIn 2) j.J) ∧
      IsRankOneBorel (starImage j.J (Mc.pCoreIn 2) j.J)
        (starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))) ∧
      Chapter1.IsSylowIn 2 (Mc.pCoreIn 2) (j.J ⊔ Mc.pCoreIn 2) ∧
      ((∃ n, ChapterC.IsL2EvenBlock j.J n) ∨ ChapterC.IsAlternatingBlock j.J 5) :=
  row.geometry (contained_input s d j h)

/-- The selected image quotient and reconstructed block give all three
required comparison outputs, with the original K₁ quotient restored. -/
theorem comparison_of_core_block_borel (h : d.K1 ≤ j.J)
    (hcyclic : Nonempty
      ((coreImage j.J d.K1 ⧸ pCore 2 (coreImage j.J d.K1)) ≃* Multiplicative (ZMod 5)))
    {n : ℕ} (hblock : ChapterC.IsL2EvenBlock j.J n)
    (hborel : ∃ S : Sylow 2 (j.J ⧸ pCore 2 j.J),
      coreImage j.J (borelIntersection s d j) = normalizer (S : Set (j.J ⧸ pCore 2 j.J))) :
    ∃ b : NaturalBorelModel j.J (borelIntersection s d j),
      Nonempty ((d.K1 ⧸ pCore 2 d.K1) ≃* Multiplicative (ZMod 5)) ∧
        ChapterC.IsL2EvenBlock j.J b.field.degree := by
  obtain ⟨b,hdegree⟩ := exists_naturalBorelModel_of_block hblock
    (component_core_le_intersection s d j h) hborel
  obtain ⟨e⟩ := hcyclic
  exact ⟨b,⟨(coreImageQuotientEquiv h).symm.trans e⟩,hdegree.symm ▸ hblock⟩

/-- The original terminal consumer applies once the block reconstruction
and its literal core-quotient Borel are supplied. -/
theorem false_of_core_block_borel (h : d.K1 ≤ j.J)
    {n : ℕ} (hblock : ChapterC.IsL2EvenBlock j.J n)
    (hborel : ∃ S : Sylow 2 (j.J ⧸ pCore 2 j.J),
      coreImage j.J (borelIntersection s d j) = normalizer (S : Set (j.J ⧸ pCore 2 j.J))) :
    False := by
  obtain ⟨b,_⟩ := exists_naturalBorelModel_of_block hblock
    (component_core_le_intersection s d j h) hborel
  exact false_of_natural_borel s d j h b

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
