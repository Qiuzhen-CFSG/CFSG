module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationImage

/-!
# Original Cartan normalization in the nonzero-core branch

The completed containing-component catalogue reduces normalization to
one noncentral Fitting branch. The actual-image recognition theorem
identifies the smaller residual with SL₂(p); the prime-linear Cartan
normalization theorem and perfect lift finish that branch. The original
Cartan therefore normalizes O²(H), and the old-residual two-core equality
follows under the original nonzero-core hypotheses.

The tensor assembly qt-d-tensor-exclusion owns the separate line theorem
and the final tensor exclusion. The line-based applications here consume
its literal normalization conclusion and have no recognition callback.

Source: Aschbacher--Smith, Proposition 9.3.1 and Lemma 9.3.2, printed
pp.732--733 of the combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The nonzero-core branch of original Proposition 9.3.1: the original
Cartan normalizes the old residual, with image recognition discharged. -/
theorem nonzero_core_cartan_normalizes
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) :=
  m.nonzero_core_cartan_normalizes_of_oddCore_images
    (fun _ hJU hJ hnJ hn => m.cartan_normalizer_residual_prime_model hJU hJ hnJ hn)
    hH hlarge A B hAB hA9 hAe hB3 hBK hBC hcore

/-- Once the original residual normalizes the tensor line, the Cartan
normalizes that residual. The line premise is supplied by the independent
line-centralization branch of the tensor assembly. -/
theorem cartan_normalizes_of_line
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hKN : (pResidual 2 H).map H.subtype ≤ normalizer (m.tensorLine : Set G)) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) :=
  m.nonzero_core_cartan_normalizes hH hlarge A B hAB hA9 hAe hB3 hBK hBC
    (m.cartan_core_ne_bot_of_old_residual_normalizes_line hH A hAB hKN)

/-- The old-residual equality of original Lemma 9.3.2, with Cartan
normalization proved from the nonzero-core source hypotheses. -/
theorem source_cartan_twoCore_of_nonzero_core
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    (A ⊔ (T : Subgroup G)).pCoreIn 2 =
      ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype) ⊔ (H ⊔ A).pCoreIn 2 := by
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  exact source_old_residual_cartan_twoCore D hH eK A B hAB
    (hBC ▸ inf_le_left) hBK hB3
    (m.nonzero_core_cartan_normalizes hH hlarge A B hAB hA9 hAe hB3 hBK hBC hcore)

/-- The same literal two-core equality after the independent tensor-line
normalization theorem supplies the nonzero core. -/
theorem source_cartan_twoCore_of_line
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hKN : (pResidual 2 H).map H.subtype ≤ normalizer (m.tensorLine : Set G)) :
    (A ⊔ (T : Subgroup G)).pCoreIn 2 =
      ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype) ⊔ (H ⊔ A).pCoreIn 2 :=
  m.source_cartan_twoCore_of_nonzero_core hH hlarge A B hAB hA9 hAe hB3 hBK hBC
    (m.cartan_core_ne_bot_of_old_residual_normalizes_line hH A hAB hKN)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
