module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceRankOne
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceAlternatingFive
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.MarkedSourceCatalogue

/-!
# The original full chief catalogue with its proved source exclusions

Each literal noncentral irreducible chief image is classified by the complete
B.4 action theorem. The original configuration excludes A₅, A₇, the natural
linear-two and linear-three rows, larger-field Sp₄, Suzuki and the orthogonal
larger-field row. This record retains the unfiltered catalogue together with
actual contradictions, for the remaining source row analysis.
Source: Aschbacher–Smith13.5.21, p.924.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Section08.Source ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration

/-- The full action alternatives together with the proved source row exclusions. -/
structure ChiefSieve {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W) : Prop where
  catalogue : FullCatalogueAction ρ
  not_five : ¬ Nonempty (generalizedFitting E ≃* alternatingGroup (Fin 5))
  not_seven : ¬ Nonempty (generalizedFitting E ≃* alternatingGroup (Fin 7))
  not_linearTwo : ∀ F, ¬ LinearTwoChiefAction ρ F
  not_linearThree : ∀ F, ¬ LinearThreeChiefAction ρ F
  not_symplectic : ∀ F, 1 < F.degree → ¬ SymplecticChiefAction ρ F
  not_suzuki : ∀ k, 0 < k → ¬ SuzukiChiefAction ρ k
  not_orthogonal : ∀ Kfield F :
      Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField,
    F.degree = 2*Kfield.degree → ¬ Nonempty
      (generalizedFitting E ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier)

variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
  (s : Selected D K) [(componentCentralizer s h).Normal]

/-- Complete catalogue and seven genuine exclusions on the literal chief image. -/
theorem source_chief_sieve
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hirr : IsIrreducible (chiefRepresentation D K h U N))
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY) :
    ChiefSieve (imageRepresentation (chiefRepresentation D K h U N)) where
  catalogue := source_chief_fullCatalogue D K h s hG hH hi hu hcard U N hn hirr
  not_five := source_chief_not_five s h hG hH hi hu hcard U N hn hirr Y hY c
  not_seven := source_chief_not_seven D K h s hG hH hi hu hcard U N hn hirr Y hY c
  not_linearTwo := source_chief_not_linearTwo s h hG hH hi hu hcard U N hn hirr Y hY c
  not_linearThree := source_chief_not_linearThree D K h s hG hH hi hu hcard U N hn hirr Y hY c
  not_symplectic := source_chief_not_symplectic D K h s hG hH hi hu hcard U N hn hirr Y hY c
  not_suzuki := source_chief_not_suzuki D K h s hG hH hi hu hcard U N hn hirr Y hY c
  not_orthogonal := source_chief_not_orthogonal D K h s hG hH hi hu hcard U N hn hirr Y hY c
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
