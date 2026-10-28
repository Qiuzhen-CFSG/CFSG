module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.CubicSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.ReducedSpan
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.Chapter1.Section01Inheritance
/-!
# The actual auxiliary two-core

Reducedness of the normal four-group makes the auxiliary two-core centralize it.
The original Sylow centralizer identity then identifies that core with O₂(KT).
Source: Aschbacher–Smith C.5.13, printed p.162.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
/-- Once the actual auxiliary normalizer preserves U, its two-core is
exactly the original P₁=O₂(KT). -/
theorem alternating_three_auxiliary_core
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hAX : K ⊔ T ≤ X)
    (PX : Sylow 2 X) (hPX : (PX : Subgroup X).map X.subtype = T)
    (hNU : X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G) ≤ normalizer (U K : Set G)) :
    (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)).pCoreIn 2 = (K ⊔ T).pCoreIn 2 := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hKN : K ≤ N := le_sup_left.trans hAN
  have hUN : U K ≤ N := (map_subtype_le _).trans hKN
  have hTN : T ≤ N := le_sup_right.trans hAN
  obtain ⟨S,hS⟩ := Chapter1.IsSylowIn.restrict (show Chapter1.IsSylowIn 2 T X from ⟨PX,hPX⟩)
    hTN (show N ≤ X from inf_le_left)
  let : IsElementaryAbelian 2 (U K) := h.elementary
  have hspan : conjugateSpanBy (U K) N = U K :=
    le_antisymm (conjugateSpanBy_le le_rfl hNU) (le_conjugateSpanBy _ _)
  have hred := alternating_three_full_span_reduced h ha hT hTK N hKN S hS
    (hspan.le.trans (le_centralizer (U K)))
  rw [hspan] at hred
  have hcore := (CounterexampleCharacteristic.ReducedMarking.reduced_baumann_core K T
    h.short hT hTK ⟨P,hP⟩).2.2.2.2.2
  apply le_antisymm
  · have hNT : N.pCoreIn 2 ≤ T := hS ▸ pCoreIn_le_sylow N S
    have hNC : N.pCoreIn 2 ≤ centralizer (U K : Set G) := by
      rintro _ ⟨n,hn,rfl⟩ u hu
      exact (congrArg N.subtype (hred.le_centralizer_pCore (show (⟨u,hUN hu⟩ : N) ∈ (U K).subgroupOf N from hu) n hn)).symm
    exact (le_inf hNT hNC).trans_eq hcore
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A)
      ((pCoreIn_le 2 A).trans hAN) inf_le_right
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
