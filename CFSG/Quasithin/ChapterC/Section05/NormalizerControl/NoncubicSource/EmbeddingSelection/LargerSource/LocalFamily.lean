module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingOrbit

/-!
# The auxiliary span in the larger local family

The actual A.3.12 source application makes L=⟨K^{X₁}⟩ a C-component
of X₁=X∩N(O₂(KT)). Its nontrivial two-core and the original full Sylow
allow the local-component restriction theorem to place L in L(X,T).
The original Sylow normalizes L because it lies in X₁. This proves local
applicability in X without comparing the two different quotient kernels.
Source: Aschbacher–Smith C.5.12–13, printed pp.162–163; 1.2.4.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Genuine reduced source data places the original auxiliary span in
the larger group’s local family and supplies its Sylow normalization. -/
theorem source_larger_local_family {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    L ∈ Chapter1.LIn X T ∧ T ≤ normalizer (L : Set G) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hKN : K ≤ N := le_sup_left.trans hAN
  have hLN : L ≤ N := conjugateSpanBy_le_self hKN
  have hfamily := noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS
  obtain ⟨Q,hQ⟩ := hfamily.2.2
  have hcore : A.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) ((pCoreIn_le 2 A).trans hAN) inf_le_right
  have hNH : N ∈ Chapter1.H G := by
    intro he
    exact hfamily.1.2.2.2 (bot_unique (hcore.trans he.le))
  have hcomp := (noncubic_source_embedding_of_A312 hG hA312 K T X hK h3 hTK hAX hX S hS).1
  exact ⟨⟨hLN.trans inf_le_left,Chapter1.mem_L_of_cComponent hNH ⟨Q,hQ⟩ hLN hcomp⟩,
    (le_sup_right.trans hAN).trans (le_normalizer_conjugateSpanBy K N)⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
