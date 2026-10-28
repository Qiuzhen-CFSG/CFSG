module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AlternatingSevenMaximal.Rows
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.EmbeddingNormality
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# A₇ local images in the original two-core quotient

The genuine model-valued 1.2.4 theorem puts a Sylow-invariant local component
in a normal containing component. The A₇ maximality theorem identifies their
images in the actual quotient by O₂. The source application uses the literal
span L=⟨K^{X∩N(O₂(KT))}⟩, deriving its Sylow normalization from the core
normalizer and the quotient SQTK hypotheses from the original QTKE data.

Local-component membership and the A₇ model of the image in X/O₂(X) remain
explicit. A model for L/O₂(L), or for its auxiliary action image, is not
substituted for that hypothesis: their core kernels require a separate
source comparison.
Source: Aschbacher–Smith C.5.12–13, printed pp.162–163; 1.2.4.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.AlternatingSevenMaximal
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

/-- An actual Sylow-invariant local component with A₇ image has normal
image in the original two-core quotient. Only genuine A.3.12 is retained. -/
theorem local_image_normal {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (T : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents T → A312Conclusion B)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ Chapter1.L G S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hmodel : IsAlternating (B.map (QuotientGroup.mk' (pCore 2 G))) 7) :
    (B.map (QuotientGroup.mk' (pCore 2 G))).Normal := by
  obtain ⟨D,hD,hBD,_,hrows,hn⟩ := lemma_1_2_4_of_A_3_12 hA312 hQ S hB
  have he := eq_of_embedding _ _ (map_mono hBD) hmodel hrows
  let : D.Normal := hn hSB
  rw [he]
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

/-- The literal source span in the larger group X. Its model premise is
on its actual image in X/O₂(X), not on an auxiliary quotient. -/
theorem source_image_normal {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hlocal : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      conjugateSpanBy K N ∈ Chapter1.LIn X T)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      IsAlternating (((conjugateSpanBy K N).subgroupOf X).map
        (QuotientGroup.mk' (pCore 2 X))) 7) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    (((conjugateSpanBy K N).subgroupOf X).map
      (QuotientGroup.mk' (pCore 2 X))).Normal := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  have hLX : L ≤ X := hlocal.1
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hTL : T ≤ normalizer (L : Set G) :=
    (le_sup_right.trans hAN).trans (le_normalizer_conjugateSpanBy K N)
  have hTs : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hmem : L.subgroupOf X ∈ Chapter1.L X (S : Subgroup X) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTX hLX).mp hlocal
  have hXH : X ∈ Chapter1.H G := by
    intro he
    have hXbot : X = ⊥ := by
      apply bot_unique
      have hh : X ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ X.pCoreIn 2 := hX
      rw [he] at hh
      intro x hx
      apply hh
      refine ⟨hx, ?_⟩
      intro y hy
      have hy : y = 1 := hy
      simp only [hy, one_mul, mul_one]
    have hLbot : L = ⊥ := bot_unique (hLX.trans hXbot.le)
    have hsolv : Group.IsSolvable L := by rw [hLbot]; infer_instance
    exact Chapter1.mem_L_not_isSolvable hlocal.2 hsolv
  apply local_image_normal hA312 (uniqueness_local_quotient_sqtk hG hXH) S hmem _ hmodel
  rw [← subgroupOf_normalizer_eq hLX]
  intro s hs
  exact hTL (hS ▸ mem_map_of_mem X.subtype hs)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.AlternatingSevenMaximal
