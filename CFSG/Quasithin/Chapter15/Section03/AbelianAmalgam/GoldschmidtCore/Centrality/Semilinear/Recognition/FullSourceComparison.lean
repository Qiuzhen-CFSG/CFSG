module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.DihedralComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.SquareFieldComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceAlternatives

/-!
# Semilinear recognition from the full corrected source alternatives

The original rows and ambient dihedral branch use their existing comparison.
The genuine square-field extension is excluded by its actual component order
and the B-side action. Applying the universal inputs retains the original
local pair and actual offender representation throughout.
Source: Aschbacher–Smith F.6.18 and 15.3.68, pp.309–310,1154–1155.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]

theorem source_classification_comparison
    {G₁ G₂ : Subgroup D} {S : Sylow 2 D}
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥)
    (hf : FSource.SourceAlternative G₁ G₂ S)
    (hb : SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)) :
    offenderSubgroup ρ = ⊤ ∧ Nonempty (D ≃* SL(3,ZMod 2)) := by
  rcases hf with ha | hrw
  · exact adequate_classification_comparison ρ hr hne hcore ha hb
  · exact (square_field_classification_impossible hrw.some ρ hr hne hcore hb).elim

theorem recognition_of_source_classifications {K : GroupClass.{u}}
    (sourceF : FSource.SourceClassificationInput K)
    (sourceB : GeneralClassificationInput.{u,v} K)
    (G₁ G₂ : Subgroup D) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (cover : ThreePrimeSQTKQuotient K D)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hyp : FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype))
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥) :
    (∃ S : Sylow 2 D, G₁ ⊓ G₂ = (S : Subgroup D) ∧
      (FSource.SourceAlternative G₁ G₂ S ∨ FSource.SourceAlternative G₂ G₁ S)) ∧
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
    offenderSubgroup ρ = ⊤ ∧ Nonempty (D ≃* SL(3,ZMod 2)) := by
  obtain ⟨S, hS, hf⟩ := sourceF D G₁ G₂ triple cover
  have hb := sourceB _ _ _ hyp
  refine ⟨⟨S, hS, hf⟩, hb, ?_⟩
  rcases hf with hf | hf <;> exact source_classification_comparison ρ hr hne hcore hf hb

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
