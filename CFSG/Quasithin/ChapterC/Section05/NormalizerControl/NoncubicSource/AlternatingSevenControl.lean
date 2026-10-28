module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.MovedCore
public import Theory.SpecificGroups.AlternatingSevenQuotientControl
/-!
# The A₇ auxiliary-image branch of C.5.13

The literal auxiliary group is N=X∩N_G(O₂(KT)), and its module is the
original omega-center span V. The original Sylow subgroup restricts to N.
If the actual image of L=⟨Kᴺ⟩ in N/C_N(V) is A₇, the automorphism-image
normalizer bound implies N_N(T)≤N_G([V,K])=N_G(U(K)).

The earlier row selection supplies exactly that group isomorphism. No
short-group, irreducibility, or block-recognition conclusion about L is
assumed. The central layer of the original module is retained throughout.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
/-- The genuine source Sylow and commutator identities discharge the A₇ normalizer branch. -/
theorem noncubic_control_of_alternatingSeven_image (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let V := conjugateSpanBy (omegaOneCenterAmbient T) N
      let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
      let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
      Nonempty (DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N) ≃*
        alternatingGroup (Fin 7))) :
    (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U K : Set G) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  let L := DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N)
  let : L.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hAN : K ⊔ T ≤ N := le_inf hAX ((K ⊔ T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G))))
  have hKN : K ≤ N := le_sup_left.trans hAN
  have hTN : T ≤ N := le_sup_right.trans hAN
  obtain ⟨Q,hQ⟩ := Chapter1.IsSylowIn.restrict
    (show Chapter1.IsSylowIn 2 T X from ⟨S,hS⟩) hTN inf_le_left
  have hQS : (Q : Subgroup N) = T.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [hQ,map_subgroupOf_eq_of_le hTN]
  have hQK : (Q : Subgroup N) ≤ normalizer (K.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hKN,hQS]
    intro t ht
    exact hTK ht
  obtain ⟨e⟩ := hmodel
  have hn := normalizer_commutator_le_of_alternatingSeven_image (V.subgroupOf N)
    (K.subgroupOf N) Q hQK L (map_mono le_normalClosure) e
  have hm : ⁅V.subgroupOf N,K.subgroupOf N⁆.map N.subtype = U K := by
    rw [map_commutator,map_subgroupOf_eq_of_le hs.2.1,map_subgroupOf_eq_of_le hKN]
    exact hs.2.2.2.2.2.2.2
  rintro g ⟨hgN,hgT⟩
  have hg : (⟨g,hgN⟩ : N) ∈ normalizer (Q : Set N) := by
    change (⟨g,hgN⟩ : N) ∈ normalizer ((Q : Subgroup N) : Set N)
    rw [hQS,← subgroupOf_normalizer_eq hTN]
    exact hgT
  have hh := ⁅V.subgroupOf N,K.subgroupOf N⁆.le_normalizer_map N.subtype
    (mem_map_of_mem N.subtype (hn hg))
  rwa [hm] at hh
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
