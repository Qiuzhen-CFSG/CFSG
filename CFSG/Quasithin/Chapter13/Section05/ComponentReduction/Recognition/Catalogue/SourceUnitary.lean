module
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.MarkedUnitary
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceChiefMarked

/-!
# The natural unitary chief row is impossible on the original source image

The original component supplies the faithful irreducible chief action and its
nonidentity involution of binary displacement at most two. For the natural
SU₃(2ⁿ) row, n ≥ 2, this displacement is smaller than both the coefficient
degree and half the module dimension. The proved scalar-restriction theorem
therefore excludes the row on the literal chief image. No marked actor or
small-displacement hypothesis is added to the source input.

Source: Aschbacher–Smith 13.5.21, printed pp.923–924, condition (iii), and
Table B.4.5, printed p.87. The other action alternatives are unchanged.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Section08.Source Configuration
universe u

/-- The full natural unitary action on the actual generalized Fitting subgroup. -/
@[expose] def UnitaryChiefAction {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W)
    (F : BinaryField) (J : HermitianForm 3 F.Carrier) : Prop :=
  Nonempty (ActionEquiv (ρ.comp (generalizedFitting E).subtype) (unitaryThree F J))

variable {G : Type u} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The source constructs the marked actor on this very chief image before
applying the natural unitary exclusion. -/
theorem source_chief_not_unitary (s : Selected D K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hirr : IsIrreducible (chiefRepresentation D K h U N))
    (F : BinaryField) (n : ℕ) (hlarge : 2 ≤ n) (hdegree : F.degree = 2 * n)
    (J : HermitianForm 3 F.Carrier) :
    ¬ UnitaryChiefAction (imageRepresentation (chiefRepresentation D K h U N)) F J := by
  have hyp := source_chief_hypotheses_all D K h s hG hH hi hu hcard U N hn hirr
  obtain ⟨t, ht, hr, _⟩ := source_chief_marked_all D K h s hG hH hi hu hcard U N hn hirr
  exact ChapterB.SmallRatioClassification.marked_b4_unitary_source hyp F n hlarge hdegree J t ht hr

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
