module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Span
/-!
# The literal block image in the auxiliary action quotient

Because U≤V, an element of K centralizing V lies in C_K(U)=O₂(K).
The reverse inclusion follows from O₂(K)≤P₁≤C(V). Thus the actual image
of K in X₁/C_X₁(V₁) is its original two-core quotient, with the full central
cover of U retained throughout.
Source: Aschbacher–Smith C.5.13, printed p.162.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
/-- The first isomorphism theorem for the actual block action on V. -/
theorem block_action_quotient_equiv (K N V : Subgroup G)
    (hK : IsShort K) (hKN : K ≤ N) (hVN : V ≤ N)
    (hNV : N ≤ normalizer (V : Set G)) (hUV : U K ≤ V)
    (hcore : K.pCoreIn 2 ≤ centralizer (V : Set G)) :
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
    Nonempty ((K ⧸ pCore 2 K) ≃*
      (K.subgroupOf N).map (QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)))) := by
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  let f := q.comp (inclusion hKN)
  have hk : f.ker = pCore 2 K := by
    ext k
    constructor
    · intro hk
      have hc : inclusion hKN k ∈ centralizer (V.subgroupOf N : Set N) :=
        (QuotientGroup.eq_one_iff _).mp hk
      apply hK.centralizer_blockU.le
      intro u hu
      apply Subtype.ext
      exact congrArg N.subtype (hc ⟨u,hVN (hUV (mem_map_of_mem K.subtype hu))⟩
        (hUV (mem_map_of_mem K.subtype hu)))
    · intro hk
      apply (QuotientGroup.eq_one_iff _).mpr
      intro v hv
      exact Subtype.ext (hcore (mem_map_of_mem K.subtype hk) v hv)
  have hr : f.range = (K.subgroupOf N).map q := by
    rw [MonoidHom.range_comp,inclusion_range]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hr)⟩
/-- On the literal C.5.13 omega-center span, the block image is exactly
its original quotient. The natural and alternating source applications
discharge the noncentral fixed-point premise on their original modules. -/
theorem source_omega_block_quotient (K T X : Subgroup G)
    (hK : IsShort K) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (hfixed : ¬ U K ⊓ omegaOneCenterAmbient T ≤ centralizer (K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hspan := source_omega_span_of_noncentral_fixed K T X hK hT hTK P hP hA hAX hfixed
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hspan.2.1).mpr hspan.2.2.1
    Nonempty ((K ⧸ pCore 2 K) ≃*
      (K.subgroupOf N).map (QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N)))) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hs := source_omega_span_of_noncentral_fixed K T X hK hT hTK P hP hA hAX hfixed
  have hcore : K.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes (show K ≤ A from le_sup_left) (sup_le K.le_normalizer hTK)).trans
      (normalizer_core_omega_span A X T P hP hA hAX).2.2.1
  exact block_action_quotient_equiv K N V hK (le_sup_left.trans hAN) hs.2.1 hs.2.2.1 hs.2.2.2.1 hcore
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
