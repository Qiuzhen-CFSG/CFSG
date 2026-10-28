module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OmegaSeed
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.FullFixedPoint
public import Theory.GroupTheory.IndexTwoOmegaDiagonal

/-!
# Omega-center seeds for the exchanged C.5 blocks

The full normalizing two-group has a noncentral fixed vector in each chi-zero
module: use the actual natural central-cover lift, or the zero fixed layer
in degrees three and five. At index two its outside conjugate forms a
central diagonal. The other factor centralizes the selected block, and
[U,K]=U removes this factor, recovering the entire module in the omega span.
No central layer is discarded and no reduced setup marking is assumed.

Source: Aschbacher–Smith C.5.3, printed p.155, and I.2.3(2), p.413.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem chiZero_noncentral_omega_seed (K S : Subgroup G) (hK : IsChiZeroBlock K)
    (hS : IsPGroup 2 S) (hUS : U K ≤ S) (hSK : S ≤ normalizer (K : Set G)) :
    ∃ u : G, u ∈ U K ∧ u ∈ omegaOneCenterAmbient S ∧ u ∉ centralizer (K : Set G) := by
  rcases hK with ⟨n,hn⟩ | ha | ha
  · obtain ⟨u,huC,huK⟩ := exists_natural_block_fixed_point hn hS hSK
    refine ⟨u,u.property,?_,huK⟩
    apply (mem_omegaOneCenterAmbient_iff S _).mpr
    refine ⟨hUS u.property,?_,huC⟩
    let : IsElementaryAbelian 2 (U K) := hn.2.1.elementary.map K.subtype
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) u.property
  · have he : IsElementaryAbelian 2 (U K) := ha.2.1.elementary.map K.subtype
    have hne : U K ≠ ⊥ := fun hz => ha.2.1.blockU_ne_bot
      ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp hz)
    have hfix := CounterexampleCharacteristic.central_witness S (U K) (U K) hS hUS
      (hSK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))) hne he le_rfl
    have hnc : ¬ U K ⊓ omegaOneCenterAmbient S ≤ centralizer (K : Set G) := by
      intro hc
      apply hfix
      apply bot_unique
      rintro u ⟨hu,hΩ⟩
      obtain ⟨v,hv,rfl⟩ := hu
      have hvfix : (⟨v,hv⟩ : blockU K) ∈ blockFixed K := by
        apply mem_center_iff.mpr
        intro k
        apply K.subtype_injective
        exact hc ⟨mem_map_of_mem K.subtype hv,hΩ⟩ k k.property
      rw [alternatingThreeCoverInput K ha,mem_bot] at hvfix
      exact congrArg (fun w : blockU K => ((w : K) : G)) hvfix
    obtain ⟨u,hu,hc⟩ := SetLike.not_le_iff_exists.mp hnc
    exact ⟨u,hu.1,hu.2,hc⟩
  · obtain ⟨u,hu,hc⟩ := SetLike.not_le_iff_exists.mp
      (NormalizerControl.alternating_five_noncentral_fixed K S ha hS hUS hSK)
    exact ⟨u,hu.1,hu.2,hc⟩

private theorem module_commutator (K : Subgroup G) (hK : IsShort K) : ⁅U K,K⁆ = U K := by
  have hh := commutator_isPPerfect_idempotent K (pCoreIn 2 K)
    hK.twoPerfect (isPGroup_pCoreIn 2 K)
    (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  simpa only [U,pCoreIn,blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh

theorem module_le_of_noncentral_diagonal (K W : Subgroup G) (hK : IsShort K)
    (hKW : K ≤ normalizer (W : Set G)) (u v : G) (hu : u ∈ U K)
    (hunc : u ∉ centralizer (K : Set G)) (hv : v ∈ centralizer (K : Set G)) (hvn : v ∈ normalizer (W : Set G))
    (hdiag : u*v ∈ W) : U K ≤ W := by
  let C := centralizer (K : Set G) ⊓ normalizer (W : Set G)
  have hujoin : u ∈ W ⊔ C := by
    have hh := (W ⊔ C).mul_mem ((le_sup_left : W ≤ W ⊔ C) hdiag)
      ((le_sup_right : C ≤ W ⊔ C) (C.inv_mem ⟨hv,hvn⟩))
    simpa only [mul_inv_cancel_right] using hh
  have hKC : K ≤ normalizer (C : Set G) := by
    apply (le_inf (K.le_normalizer.trans (normalizer_le_normalizer_centralizer K))
      (hKW.trans (normalizer (W : Set G)).le_normalizer)).trans
    exact inf_normalizer_le_normalizer_inf
  have hgen := NormalizerControl.block_span_of_noncentral_seed K (zpowers u) hK
    (zpowers_le.mpr hu) (fun hz => hunc (hz (mem_zpowers u)))
  have hU : U K ≤ W ⊔ C := by
    rw [←hgen]
    exact conjugateSpanBy_le (zpowers_le.mpr hujoin)
      ((le_inf hKW hKC).trans (normalizer_inf_normalizer_le_normalizer_sup W C))
  have hWW : ⁅W,K⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hKW
  have hCW : ⁅C,K⁆ ≤ W := (commutator_eq_bot_iff_le_centralizer.mpr inf_le_left).le.trans bot_le
  have hj : ⁅W ⊔ C,K⁆ ≤ W := by
    exact ((le_commutatorPreimage_iff (normalizer (W : Set G)) K W (W ⊔ C) le_rfl).mp
      (sup_le (le_commutatorPreimage W.le_normalizer hWW)
        (le_commutatorPreimage inf_le_right hCW))).2
  exact (module_commutator K hK).symm.le.trans ((commutator_mono hU le_rfl).trans hj)

/-- The raw exchanged-pair source step, preserving the full short-module layer. -/
theorem paired_block_omega_span
    (H T S K : Subgroup G) (hK : IsChiZeroBlock K) (hT : IsPGroup 2 T)
    (hST : S ≤ T) (hi : S.relIndex T = 2) (hTH : T ≤ H) (hKH : K ≤ H)
    (hUS : U K ≤ S) (hSK : S ≤ normalizer (K : Set G))
    (t : G) (ht : t ∈ T) (htS : t ∉ S)
    (hswap : (U K).map (MulAut.conj t).toMonoidHom ≤ centralizer (K : Set G)) :
    U K ≤ conjugateSpanBy (omegaOneCenterAmbient T) H := by
  obtain ⟨u,hu,hΩ,hnc⟩ := chiZero_noncentral_omega_seed K S hK (hT.to_le hST) hUS hSK
  let v := t*u*t⁻¹
  have hv : v ∈ centralizer (K : Set G) := hswap (mem_map_of_mem _ hu)
  have hc : Commute u v := hv u ((map_subtype_le (blockU K)) hu)
  have hdiag := indexTwo_diagonal_mem_omegaCenter S T hST hi t ht htS u hΩ hc
  let W := conjugateSpanBy (omegaOneCenterAmbient T) H
  have hHW : H ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have hvT : v ∈ T := T.mul_mem (T.mul_mem ht (hST (hUS hu))) (T.inv_mem ht)
  exact module_le_of_noncentral_diagonal K W hK.chi.short (hKH.trans hHW)
    u v hu hnc hv (hHW (hTH hvT)) (le_conjugateSpanBy _ _ hdiag)

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
