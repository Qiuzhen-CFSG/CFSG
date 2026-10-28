module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource

/-!
# The ambient dihedral PSL₂ branch of F.6.18

The actual PSL₂ field, degree, congruence, generalized Fitting subgroup and
common Sylow are sufficient for the Chapter 14 and 15 comparisons. The local
Goldschmidt generators are retained by the surrounding triple, without an
additional assertion that both are S₄. The original thirteen-row interface
remains available unchanged.

The enlarged source input below is still a conditional universal interface.
Its producer must prove the ambient models from the SQTK quotient and the
original Goldschmidt triple. It is not itself a classification theorem.
Source: Aschbacher–Smith, F.6.18 and its dihedral case, printed pp.309–310.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {D : Type u} [Group D] [Finite D]

/-- The actual ambient PSL₂ model and the original dihedral Sylow. -/
structure DihedralPSL2Row (S : Sylow 2 D) where
  field : FieldParameter.{u}
  degree : field.degree ≤ 2
  congruence : Nat.card field.Carrier % 16 = 7 ∨ Nat.card field.Carrier % 16 = 9
  model : D ≃* PSL(2,field.Carrier)
  component : generalizedFitting D = ⊤
  quasisimple : IsQuasisimple (generalizedFitting D)
  sylow : Nonempty (S ≃* DihedralGroup 4)

/-- Source alternatives adequate for the ambient comparisons; the original
local labels remain in every legacy alternative and in the supplied triple. -/
def AdequateAlternative (G₁ G₂ : Subgroup D) (S : Sylow 2 D) : Prop :=
  Alternative G₁ G₂ S ∨ Nonempty (DihedralPSL2Row S)

/-- Universal adequate source input, requiring both genuine source hypotheses. -/
def AdequateClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D),
    ChapterF.IsGoldschmidtTriple G₁ G₂ → ThreePrimeSQTKQuotient K D →
    ∃ S : Sylow 2 D, G₁ ⊓ G₂ = (S : Subgroup D) ∧
      (AdequateAlternative G₁ G₂ S ∨ AdequateAlternative G₂ G₁ S)

/-- Every original full classifier supplies the adequate interface. -/
theorem ClassificationInput.adequate {K : GroupClass.{u}}
    (h : ClassificationInput K) : AdequateClassificationInput K := by
  intro D _ _ G₁ G₂ ht hq
  obtain ⟨S, hS, hm⟩ := h D G₁ G₂ ht hq
  exact ⟨S, hS, hm.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
