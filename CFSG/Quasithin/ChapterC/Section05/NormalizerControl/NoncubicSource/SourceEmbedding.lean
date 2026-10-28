module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Embedding
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
/-!
# The original QTKE hypotheses supply the noncubic embedding application

The auxiliary normalizer contains the nontrivial normal two-core of KT.
It therefore belongs to the original two-local family, and QTKE inheritance
supplies its literal two-core quotient's SQTK hypotheses. Only the universal
earlier A.3.12 and A.3.8 theorems remain in the embedding application.
Source: Aschbacher–Smith C.5.13 and 1.2.4, printed pp.162 and504.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
/-- The source embedding for the original auxiliary conjugate span, with
the local SQTK assertion derived from the simple QTKE ambient group. -/
theorem noncubic_source_embedding {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (hA38 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ B : Subgroup H, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set H)).index = 2 ∧ NonnormalCComponentModel B)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    (L.subgroupOf N).IsCComponent ∧
      A312Embedding ((K.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)))
        ((L.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hlocal := (noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX P hP).1
  have hcore : A.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) ((pCoreIn_le 2 A).trans hAN) inf_le_right
  have hNH : N ∈ Chapter1.H G := by
    intro he
    exact hlocal.2.2.2 (bot_unique (hcore.trans he.le))
  exact noncubic_auxiliary_embedding hA312 hA38 K T X hK h3 hTK hAX hX P hP
    (uniqueness_local_quotient_sqtk hG hNH)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
