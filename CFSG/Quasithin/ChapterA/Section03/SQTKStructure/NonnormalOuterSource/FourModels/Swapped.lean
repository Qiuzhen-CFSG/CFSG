module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Classification

/-!
# Literal swapped-component consumer of the original four-model source

The supplied quasisimple L/O₂(L) identifies the actual image of L inside
H/O₂(H) as an ordinary component. Its nonnormality follows from the original
T-action. The source theorem gives index two and the four actual models;
the existing factor, Borel and outer-action calculations then give precisely
the complete swapped conclusion of Proposition 1.3.4(1). Only the genuine
universal earlier Theorems A and C remain, with the full known-simple class.

Source: Aschbacher–Smith A.3.8(3), pp.45–46, and 1.3.4, pp.509–510.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
universe u
variable {G : Type u} [Group G] [Finite G] {p : ℕ} {T X P H L : Subgroup G}

/-- The original swapped input supplies an ordinary component in its literal
two-core quotient, so the exact source model theorem applies. -/
theorem nonnormal_model_of_theoremsAC
    (hA : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple D)
    (hC : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple D)
    (h : SwappedInput KnownSimple.IsKnownSimple p T X P H L) :
    (normalizer (L.subgroupOf H : Set H)).index = 2 ∧
      Section02.NonnormalCComponentModel (XiQuotient L) := by
  let := pCore_isNilpotent (p := 2) (G := H)
  let B := (L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  have hB : B.IsCComponent := h.component.2.map_quotient _
  let eL := subgroupOfEquivOfLe h.component.1
  let eQ := QuotientGroup.congr (pCore 2 (L.subgroupOf H)) (pCore 2 L) eL
    (pCore_map_iso 2 eL)
  let e : XiQuotient L ≃* B := eQ.symm.trans (cComponentTwoCoreQuotientEquiv h.component.2)
  let : IsQuasisimple (XiQuotient L) := h.quasisimple
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hordinary : IsComponent (XiQuotient H) B := ⟨hB.subnormal,inferInstance⟩
  have hn : ¬ B.Normal := by
    intro hnormal
    have hh := cComponent_normal_of_quotient_normal h.component.2 (pCore 2 H) hnormal
    exact h.not_invariant ((le_sup_right.trans h.overgroup).trans
      ((normal_subgroupOf_iff_le_normalizer h.component.1).mp hh))
  obtain ⟨hi,hm⟩ := ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_index_and_model
    hA hC (overgroup_quotient_sqtk h) (pCore_quotient_pCore_eq_bot 2) B hordinary hn
  exact ⟨(cComponent_normalizer_index_quotient h.component.2 (pCore 2 H)).symm.trans hi,
    hm.of_mulEquiv e⟩

/-- The complete existing swapped Sylow conclusion from original inputs
and genuine earlier A/C; no A.3.8 or model-selection premise remains. -/
theorem embedding_of_theoremsAC
    (hA : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple D)
    (hC : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple D)
    (h : SwappedSylowInput KnownSimple.IsKnownSimple p T X P H L) :
    Nonempty (P ≃* Plane p) ∧ SwappedFactors T P L ∧ SwappedModel p (XiQuotient L) := by
  obtain ⟨hi,hm⟩ := nonnormal_model_of_theoremsAC hA hC h.toSwappedInput
  have hs := SwappedFactorsProof.quotient_simple h.toSwappedInput hm
  obtain ⟨e⟩ := SwappedFactorsProof.quotient_product
    ChapterA.Section03.CComponentCommutation.universal_A_3_7 h.toSwappedInput hi hs
  obtain ⟨hp,hf⟩ := SwappedFactorsProof.factors_of_index_simple
    ChapterA.Section03.CComponentCommutation.universal_A_3_7 h.toSwappedInput hi hs e
  exact ⟨hp,hf,model_of_product h hs e hm⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
