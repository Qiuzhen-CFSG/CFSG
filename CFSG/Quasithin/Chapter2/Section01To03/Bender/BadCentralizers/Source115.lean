module

public import CFSG.Quasithin.Chapter1.SourceInputs
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.OrdinaryBalance.Source

/-!
# The actual earlier 1.1.5 input to the Bender argument

The ambient core and involution arguments construct every marked input for
ordinary components. The full universal A/B/C implication supplies the
Theorem C quotient model, and the full local quasisimple classifier supplies
its original action. This produces precisely `ComponentSource115`, then
feeds the existing empty-delta Bender application with proved ordinary balance.

The local marked classifier is proved. Only `qt-a02-abc-assembly` remains
explicit in the complete source applications below.
Source: Aschbacher–Smith 1.1.5 and Proposition 2.2.2, pp.501–503, 519–520.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open CFSG.Quasithin.ChapterA.Section02
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2.BenderFusion
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Supply the actual universal ambient component-action input, with all
local hypotheses constructed from the original 1.1.5 configuration. -/
theorem BadCentralizers.componentSource115_of_local_classification
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC KnownSimple.IsKnownSimple X)
    (hclass : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L]
      (α : MulAut L) (P : Sylow 2 L), MarkedInvolution α P →
        IsTheoremCModel (L ⧸ center L) → ModelAction115 L α) :
    BadCentralizers.ComponentSource115 G := by
  intro H S M z h D hD
  exact (Chapter1.lemma_1_1_5_three_of_local_classification hG hABC hclass H S M z h D hD).2.2

/-- Apply the constructed source input to the original empty-delta Bender
consumer, keeping the full KnownSimple catalogue and actual maximal subgroup. -/
theorem source_local_control_with_centralizers_of_delta_empty_and_local_classification
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC KnownSimple.IsKnownSimple X)
    (hclass : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L]
      (α : MulAut L) (P : Sylow 2 L), MarkedInvolution α P →
        IsTheoremCModel (L ⧸ center L) → ModelAction115 L α)
    (T : Sylow 2 G) (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅) :
    ∃ w : LocalControlWitness T M,
      ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M :=
  source_local_control_with_centralizers_of_delta_empty_and_source115 hG T M hM hTM hunique hdelta
    (BadCentralizers.componentSource115_of_local_classification hG hABC hclass)
/-- The complete component-action source input, using the proved marked classifier. -/
theorem BadCentralizers.componentSource115
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC KnownSimple.IsKnownSimple X) :
    BadCentralizers.ComponentSource115 G := by
  intro H S M z h D hD
  exact (Chapter1.lemma_1_1_5_three_source hG hABC H S M z h D hD).2.2

/-- The original empty-delta Bender application with the full marked
classification discharged. -/
theorem source_local_control_with_centralizers_of_delta_empty_and_theoremsABC
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC KnownSimple.IsKnownSimple X)
    (T : Sylow 2 G) (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅) :
    ∃ w : LocalControlWitness T M,
      ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M :=
  source_local_control_with_centralizers_of_delta_empty_and_source115 hG T M hM hTM hunique hdelta
    (BadCentralizers.componentSource115 hG hABC)

end CFSG.Quasithin.Chapter2.BenderFusion
