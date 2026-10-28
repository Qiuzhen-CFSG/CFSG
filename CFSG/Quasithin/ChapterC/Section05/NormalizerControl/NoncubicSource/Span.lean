module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OmegaSeed
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Core
public import Theory.GroupTheory.SylowFixedSpanReduced
public import Theory.GroupTheory.ReducedNormal.Defs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
/-!
# The noncubic auxiliary omega-center span in C.5.13

The literal span is elementary inside P₁, and P₁ centralizes it. A
noncentral full-Sylow fixed seed generates U, retaining its central
covering layer. This identifies its Sylow centralizer with P₁. Its
Sylow-fixed generators also prove genuine two-reducedness.

For A₅ the noncentral seed is proved from the actual module. For natural
covers it is precisely the earlier I.2.3(2) simultaneous fixed-point input.
Source: Aschbacher–Smith C.5.13, printed p.162.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
/-- The exact span and centralizer preliminaries from the genuine fixed seed. -/
theorem source_omega_span_of_noncentral_fixed (K T X : Subgroup G)
    (hK : IsShort K) (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (hfixed : ¬ U K ⊓ omegaOneCenterAmbient T ≤ centralizer (K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    IsElementaryAbelian 2 V ∧ V ≤ N ∧ N ≤ normalizer (V : Set G) ∧
      U K ≤ V ∧ V ≤ T ∧ T ⊓ centralizer (V : Set G) = (K ⊔ T).pCoreIn 2 := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  obtain ⟨he,hVP,hPV,hVN,hNV⟩ := normalizer_core_omega_span A X T P hP hA hAX
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hUV : U K ≤ V := (omega_span_of_noncentral_fixed K T hK hfixed).trans
    (conjugateSpanBy_mono le_rfl (le_sup_left.trans hAN))
  have hPT : A.pCoreIn 2 ≤ T := hP ▸ pCoreIn_le_sylow A P
  have hcore := (CounterexampleCharacteristic.ReducedMarking.reduced_baumann_core
    K T hK hT hTK ⟨P,hP⟩).2.2.2.2.2
  exact ⟨he,hVN,hNV,hUV,hVP.trans hPT,
    le_antisymm ((inf_le_inf_left T (centralizer_le hUV)).trans_eq hcore) (le_inf hPT hPV)⟩
/-- The actual omega-center span is two-reduced, with its literal quotient. -/
theorem source_omega_span_reduced (K T X : Subgroup G)
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    Theory.GroupTheory.IsPReduced 2 (V.subgroupOf N) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let Z := omegaOneCenterAmbient T
  let V := conjugateSpanBy Z N
  obtain ⟨he,_hVP,_hPV,hVN,hNV⟩ := normalizer_core_omega_span A X T P hP hA hAX
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hTN : T ≤ N := le_sup_right.trans hAN
  have hZN : Z ≤ N := by
    intro z hz
    exact hTN ((mem_omegaOneCenterAmbient_iff T z).mp hz).1
  obtain ⟨Q,hQ⟩ := Chapter1.IsSylowIn.restrict (show Chapter1.IsSylowIn 2 T X from ⟨S,hS⟩)
    hTN (show N ≤ X from inf_le_left)
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
  let : IsElementaryAbelian 2 V := he
  refine ⟨inferInstance,IsElementaryAbelian.subgroupOf hVN,?_⟩
  apply centralizer_quotient_pCore_eq_bot_of_sylow_fixed_span (V.subgroupOf N) (Z.subgroupOf N) Q
  · exact subgroupOf_mono _ (le_conjugateSpanBy _ _)
  · intro z hz q hq
    apply Subtype.ext
    exact ((mem_omegaOneCenterAmbient_iff T z).mp hz).2.2 q (hQ ▸ mem_map_of_mem N.subtype hq)
  · have hm : (conjugateSpanBy (Z.subgroupOf N) ⊤).map N.subtype = V := by
      rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hZN,← MonoidHom.range_eq_map,range_subtype]
    intro v hv
    obtain ⟨w,hw,heq⟩ := (show (v : G) ∈ (conjugateSpanBy (Z.subgroupOf N) ⊤).map N.subtype from hm.symm ▸ hv)
    exact (Subtype.ext heq : w=v) ▸ hw
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
