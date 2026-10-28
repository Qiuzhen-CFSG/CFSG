module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.CubicInversion
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Core

/-!
# The complete A₃ normalizer conclusion of C.5.13

Starting with the actual reduced block and the C.5.11 Sylow subgroup,
construct the omega-center span, faithful quotient action, cubic image,
order-two Sylow subgroup, and inverting transvection. The cubic image
is normal by the proved order-two-Sylow transvection argument. Its
commutator with the span is exactly the original module U₁; hence
N_X(P₁) normalizes U₁. The reduced core identity is also derived here.
No representation, span, quotient order or normality certificate is
an input to the resulting source normalizer bound.

Source: Aschbacher–Smith C.5.13, printed p.162, A₃ branch.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
/-- The complete A₃ normalizer conclusion of C.5.13, with the span,
faithful action, quotient orders, transvection and inverter constructed. -/
theorem alternating_three_source_normalizes_module
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (X : Subgroup G) (hAX : K ⊔ T ≤ X)
    (PX : Sylow 2 X) (hPX : (PX : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G) ≤ normalizer (U K : Set G) := by
  have hcore := (CounterexampleCharacteristic.ReducedMarking.reduced_baumann_core K T
    h.short hT hTK ⟨P,hP⟩).2.2.2.2.2
  let A := K ⊔ T
  let X₁ := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) X₁
  obtain ⟨he,hVX,hXV,hUV,hVT,_hCV⟩ := alternating_three_source_span h ha hT hTK P hP hA X hAX hcore
  have hAX₁ : A ≤ X₁ := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hKX : K ≤ X₁ := le_sup_left.trans hAX₁
  let : IsElementaryAbelian 2 V := he
  let : (V.subgroupOf X₁).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let : IsElementaryAbelian 2 (V.subgroupOf X₁) := IsElementaryAbelian.subgroupOf hVX
  obtain ⟨Q,hQ,hK⟩ := alternating_three_source_quotient_orders h ha hT hTK P hP hA X hAX hcore PX hPX hx hnc
  obtain ⟨b,hb,hbi,hinv⟩ := alternating_three_source_inverter h ha hT hTK P hP hA X hAX hcore hx hnc
  have ht := alternating_three_omega_span_transvections h ha hT hTK P hP hA X hAX hcore hx hnc
    b hb b.property
  let Vi := V.subgroupOf X₁
  let Ki := K.subgroupOf X₁
  have hN := (cubic_block_closure_image Vi Ki (Representation.centralizerQuotient Vi)
    (Representation.centralizerQuotient_faithful Vi) Q hQ hK b hbi hinv ht).1
  let : ⁅Vi,Ki⁆.Normal := commutator_normal_of_centralizer_image_normal Vi Ki hN
  have hC : X₁ ≤ normalizer ((⁅Vi,Ki⁆.map X₁.subtype) : Set G) := by
    have hh := ⁅Vi,Ki⁆.le_normalizer_map X₁.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hUK : ⁅U K,K⁆ = U K := by
    have hi := commutator_isPPerfect_idempotent K (pCoreIn 2 K)
      h.short.twoPerfect (isPGroup_pCoreIn 2 K)
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
    simpa only [U,pCoreIn,blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hi
  have hVCU : V ≤ centralizer (U K : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hUV)
  have hcomm : ⁅V,K⁆ = U K := by
    apply le_antisymm
    · rw [commutator_comm]
      exact block_fixer_displacement h.short (hVT.trans hTK) hVCU
    · exact hUK.symm.trans_le (commutator_mono hUV le_rfl)
  have hmap : ⁅Vi,Ki⁆.map X₁.subtype = U K := by
    rw [map_commutator,map_subgroupOf_eq_of_le hVX,map_subgroupOf_eq_of_le hKX,hcomm]
  rwa [hmap] at hC
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
