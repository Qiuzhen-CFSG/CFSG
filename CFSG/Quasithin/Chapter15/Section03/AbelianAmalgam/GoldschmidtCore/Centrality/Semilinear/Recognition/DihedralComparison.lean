module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.DihedralPSL2

/-!
# Semilinear recognition from the adequate F.6.18 source interface

The rank-one comparison uses the ambient dihedral PSL₂ component and the
original Sylow. It needs no assertion that the two local factors are S₄.
The original triple, quotient witness and full B-side action are retained.
Source: Aschbacher–Smith, F.6.18, printed pp.309–310, and 15.3.68,
printed pp.1154–1155.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] [Finite D]

/-- The adequate alternatives give the same actual SL₃(2) recognition. -/
theorem adequate_classification_comparison
    {G₁ G₂ : Subgroup D} {S : Sylow 2 D}
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥)
    (hf : FSource.AdequateAlternative G₁ G₂ S)
    (hb : SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype)) :
    offenderSubgroup ρ = ⊤ ∧ Nonempty (D ≃* SL(3,ZMod 2)) := by
  rcases hf with hf | hr
  · exact full_classification_comparison ρ hr hne hcore hf hb
  · obtain ⟨r⟩ := hr
    obtain ⟨es⟩ := r.sylow
    exact dihedral_classification_comparison S es ρ hr hne hcore r.quasisimple r.component hb

/-- Apply the adequate F source and the full B source to the original actors.
Both literal local labels and their common Sylow remain in the output. -/
theorem recognition_of_adequate_classifications {K : GroupClass.{u}}
    (sourceF : FSource.AdequateClassificationInput K)
    (sourceB : GeneralClassificationInput.{u,v} K)
    (G₁ G₂ : Subgroup D) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (cover : ThreePrimeSQTKQuotient K D)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hyp : FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype))
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥) :
    (∃ S : Sylow 2 D, G₁ ⊓ G₂ = (S : Subgroup D) ∧
      (FSource.AdequateAlternative G₁ G₂ S ∨ FSource.AdequateAlternative G₂ G₁ S)) ∧
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
    offenderSubgroup ρ = ⊤ ∧ Nonempty (D ≃* SL(3,ZMod 2)) := by
  obtain ⟨S, hS, hf⟩ := sourceF D G₁ G₂ triple cover
  have hb := sourceB _ _ _ hyp
  refine ⟨⟨S, hS, hf⟩, hb, ?_⟩
  rcases hf with hf | hf <;> exact adequate_classification_comparison ρ hr hne hcore hf hb

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
