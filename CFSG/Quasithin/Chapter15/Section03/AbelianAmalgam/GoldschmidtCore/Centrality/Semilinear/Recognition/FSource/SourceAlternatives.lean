module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SquareField

/-!
# Source alternatives retaining the actual rank-one extension actions

The original numbered alternatives and the ambient dihedral PSL₂ branch are
retained. The square-field branch additionally retains either defining-prime
congruence and the actual Frobenius action. The original local labels and common
Sylow remain arguments throughout. These are interfaces for source assembly;
the universal input below is conditional until all source families are proved.
Source: Aschbacher–Smith F.6.18, printed pp.309–310.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {D : Type u} [Group D] [Finite D]

def SourceAlternative (G₁ G₂ : Subgroup D) (S : Sylow 2 D) : Prop :=
  AdequateAlternative G₁ G₂ S ∨ Nonempty (SquareFieldExtensionRow S)

def SourceClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D),
    ChapterF.IsGoldschmidtTriple G₁ G₂ → ThreePrimeSQTKQuotient K D →
    ∃ S : Sylow 2 D, G₁ ⊓ G₂ = (S : Subgroup D) ∧
      (SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S)

theorem AdequateClassificationInput.source {K : GroupClass.{u}}
    (h : AdequateClassificationInput K) : SourceClassificationInput K := by
  intro D _ _ G₁ G₂ ht hq
  obtain ⟨S,hS,hm⟩ := h D G₁ G₂ ht hq
  exact ⟨S,hS,hm.elim (fun hm => Or.inl (Or.inl hm)) (fun hm => Or.inr (Or.inl hm))⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
