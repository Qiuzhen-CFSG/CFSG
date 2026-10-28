module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.LocalFamily

/-!
# The genuine containing-component embedding in X

The original auxiliary span belongs to L(X,T), and T normalizes it. Applying
the model-valued 1.2.4 theorem in X therefore produces its unique containing
C-component, proves that component normal in X, and gives the actual pair
embedding in X/O₂(X). Both quotient maps in the conclusion are literal.
No model or core-kernel identification for the smaller image is assumed.
Source: Aschbacher–Smith C.5.12–13, printed pp.162–163; 1.2.4.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original reduced source data supplies the unique normal containing
C-component in X and the genuine A.3.12 embedding of their two-core images. -/
theorem source_larger_embedding {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    ∃ D : Subgroup X, D.IsCComponent ∧ L.subgroupOf X ≤ D ∧
      (∀ E : Subgroup X, E.IsCComponent → L.subgroupOf X ≤ E → E = D) ∧
      D.Normal ∧
      A312Embedding ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))
        (D.map (QuotientGroup.mk' (pCore 2 X))) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  obtain ⟨hlocal,hTL⟩ := source_larger_local_family hG hA312 K T X hK h3 hTK hAX hX S hS
  have hLX : L ≤ X := hlocal.1
  have hTX : T ≤ X := le_sup_right.trans hAX
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
      simp only [hy,one_mul,mul_one]
    have hLbot : L = ⊥ := bot_unique (hLX.trans hXbot.le)
    have hsolv : Group.IsSolvable L := by rw [hLbot]; infer_instance
    exact Chapter1.mem_L_not_isSolvable hlocal.2 hsolv
  obtain ⟨D,hD,hLD,hu,hemb,hn⟩ := lemma_1_2_4_of_A_3_12 hA312
    (uniqueness_local_quotient_sqtk hG hXH) S hmem
  refine ⟨D,hD,hLD,hu,hn ?_,hemb⟩
  rw [← subgroupOf_normalizer_eq hLX]
  intro s hs
  exact hTL (hS ▸ mem_map_of_mem X.subtype hs)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
