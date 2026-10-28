module

public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication
public import CFSG.Quasithin.ChapterA.Section01.SectionRank.CyclicCentralizers

/-!
# Discharging the section-centralizer input in F.6.16

The complete A.1.31(1) theorem supplies the universal cross-universe
surjective interface used by the actual SQTK cover. The resulting F.6.16
companions retain only the original Goldschmidt rigidity input, whose source
proof and final assembly have separate owners. All literal model and marked
action conclusions are preserved.

Source: Aschbacher–Smith, A.1.31(1), pp.27–28, and F.6.16, pp.308–309.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
universe u v

/-- The proved A.1.31(1) input, with rank on the source of the surjection. -/
theorem sectionCentralizerInput : SectionCentralizerInput.{u,v} := by
  intro A _ _ D _ _ p _ hp hrank f hf hF S hS hne
  exact Theory.GroupTheory.cyclic_primeCore_centralizer_of_surjective_rank_le_two
    hp hrank f hf hF S hS hne

variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}
variable {Ghat : Type u} [Group Ghat] [Finite Ghat] {K : GroupClass.{u}}

/-- F.6.16 with its complete section-centralizer premise discharged. -/
theorem source_lemma_F_6_16_of_rigidity
    (rigidity : GoldschmidtRigidityInput.{u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hn : ¬ IsCyclic (pCore 3 G)) :
    IsPGroup 3 (pResidual 2 G) ∧
      ((Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* Multiplicative (ZMod 2)) ∧
        (pCore 2 G₁).map G₁.subtype = ⊥ ∧ (pCore 2 G₂).map G₂.subtype = ⊥) ∨
      Nonempty (G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      Nonempty (G ≃* MarkedCubicRecognition.HeisenbergExtension)) :=
  source_lemma_F_6_16_of_inputs rigidity sectionCentralizerInput hhat e h hn

/-- The same discharge preserves both marked lines and the compatible action. -/
theorem source_marked_models_of_rigidity
    (rigidity : GoldschmidtRigidityInput.{u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hn : ¬ IsCyclic (pCore 3 G))
    (hnot : ¬ Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* Multiplicative (ZMod 2))) :
    Nonempty (MarkedRecognition.MarkedModel G₁ G₂ MarkedCubicRecognition.Nine
      MarkedCubicRecognition.nineAction
      (MonoidHom.inl MarkedCubicRecognition.C3 MarkedCubicRecognition.C3).range
      (MonoidHom.inr MarkedCubicRecognition.C3 MarkedCubicRecognition.C3).range) ∨
    Nonempty (MarkedRecognition.MarkedModel G₁ G₂ (HeisenbergPrime 3)
      MarkedCubicRecognition.heisenbergAction
      MarkedCubicRecognition.leftAxis.range MarkedCubicRecognition.rightAxis.range) :=
  source_marked_models_of_inputs rigidity sectionCentralizerInput hhat e h hn hnot

end CFSG.Quasithin.ChapterF.Noncyclic
