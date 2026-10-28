module
public import Theory.GroupTheory.ElementaryThompsonQuotient
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.OmegaCenter
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# Lifting the exceptional A₇ action geometry to characteristic control

Maximum elementary subgroups have best-offender images. Uniqueness in a
Sylow image identifies the Thompson image, and Thompson heredity lifts its
normalizer. The pointwise kernel on the fixed space is exactly the image of
the original relative centralizer. Together with the proved omega-center
splitting, quotient generation gives characteristic-normalizer control.
The native A₇ geometry is supplied in the final source application.

Source: Aschbacher–Smith C.1.23(2), printed p.130.
-/

public section
namespace CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem thompson_image (U T : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hUT : U ≤ T)
    (A : Subgroup H)
    (hA : ∀ E : Subgroup H, E ≤ T.map q →
      IsBestOffender (NormalElementaryQuotient.representation U q hq hk) E → E = A) :
    (elementaryAbelianMaxJ T).map q = ⊥ ∨ (elementaryAbelianMaxJ T).map q = A := by
  by_cases hz : (elementaryAbelianMaxJ T).map q = ⊥
  · exact Or.inl hz
  right
  have hJ : ¬ elementaryAbelianMaxJ T ≤ q.ker := fun h => hz ((Subgroup.map_eq_bot_iff _).mpr h)
  have hb := (lemma_B_2_7_local U q hq hk T hUT hJ).2
  have hE : ∃ E ∈ elementaryAbelianMaxSubgroups T, E.map q ≠ ⊥ := by
    by_contra! hn
    exact hJ (sSup_le fun E hE => (Subgroup.map_eq_bot_iff E).mp (hn E hE))
  obtain ⟨E, hE, hEne⟩ := hE
  have he : E.map q = A := hA _ (map_mono hE.1) (hb _ ⟨E,hE,rfl,hEne⟩)
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro B hB
    apply map_le_iff_le_comap.mp
    by_cases hBne : B.map q = ⊥
    · rw [hBne]; exact bot_le
    · rw [hA _ (map_mono hB.1) (hb _ ⟨B,hB,rfl,hBne⟩)]
  · rw [← he]
    exact map_mono (le_sSup hE)

omit [Finite G] [Finite H] in
theorem fixed_kernel_image (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (T L : Subgroup G) (hL : L.map q = ⊤) :
    (L ⊓ centralizer ((U ⊓ centralizer (T : Set G) : Subgroup G) : Set G)).map q =
      subspaceKernel (NormalElementaryQuotient.representation U q hq hk)
        (fixedSpace (NormalElementaryQuotient.representation U q hq hk) (T.map q)) ⊤ := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨mem_top _, fun v hv => ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    have hv' := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk T v).mp hv
    rw [← hg.2 v.toMul ⟨v.toMul.property,hv'⟩, mul_inv_cancel_right]
  · intro ha
    obtain ⟨g,hg,rfl⟩ : ∃ g ∈ L, q g = a := (show a ∈ L.map q by rw [hL]; trivial)
    refine ⟨g, ⟨hg, fun v hv => ?_⟩, rfl⟩
    have hf := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk T
      (Additive.ofMul ⟨v,hv.1⟩)).mpr hv.2
    have he := congrArg (fun w : Additive U => (w.toMul : G)) (ha.2 _ hf)
    rw [NormalElementaryQuotient.representation_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm


open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl

theorem control_of_quotient_generation
    (L : Subgroup G) (hL : IsBlock L) (hm : IsExceptionalA7Block L)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hUn : ((blockU L).map L.subtype).Normal)
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer ((blockU L).map L.subtype : Set G))
    (hkT : q.ker ≤ (T : Subgroup G)) (hLq : L.map q = ⊤)
    (A : Subgroup H)
    (ha : letI := hUn; letI := hm.1.elementary.map L.subtype
      ∀ E : Subgroup H, E ≤ (T : Subgroup G).map q →
        IsBestOffender (NormalElementaryQuotient.representation
          ((blockU L).map L.subtype) q hq hk) E → E = A)
    (hgen : letI := hUn; letI := hm.1.elementary.map L.subtype
      normalizer (A : Set H) ⊔ subspaceKernel
        (NormalElementaryQuotient.representation ((blockU L).map L.subtype) q hq hk)
        (fixedSpace (NormalElementaryQuotient.representation
          ((blockU L).map L.subtype) q hq hk) ((T : Subgroup G).map q)) ⊤ = ⊤) :
    (T : Subgroup G).characteristicNormalizerClosure = ⊤ := by
  let U := (blockU L).map L.subtype
  let := hUn
  let : IsElementaryAbelian 2 U := hm.1.elementary.map L.subtype
  have hUT : U ≤ (T : Subgroup G) :=
    ((map_mono blockU_le_core).trans (pCoreIn_le_of_subnormal 2 hL.subnormal)).trans
      (pCore_isPGroup.le_sylow_of_normal T)
  have hUcard : Nat.card U = 16 :=
    (card_map_of_injective L.subtype_injective).trans hm.u_card
  have hJne : elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥ := by
    obtain ⟨E,hE⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
    have hb := hE.2.2 U hUT inferInstance
    intro he
    have hEbot : E = ⊥ := bot_unique ((le_sSup hE).trans he.le)
    rw [hEbot, card_bot, hUcard] at hb
    omega
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro ht
    exact hJne (bot_unique ((sSup_le fun _ hE => hE.1).trans ht.le))
  let : Nontrivial (T : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hTne
  let M := (T : Subgroup G).characteristicNormalizerClosure
  have hTM : (T : Subgroup G) ≤ M :=
    (T : Subgroup G).le_normalizer.trans
      (normalizer_le_characteristicNormalizerClosure_self _ hTne)
  have hNM : normalizer ((elementaryAbelianMaxJ (T : Subgroup G)).map q : Set H) ≤ M.map q := by
    rw [← normalizer_maxJ_map_of_ker_le (T : Subgroup G) q hq hkT]
    exact map_mono (normalizer_maxJ_le_characteristicNormalizerClosure
      (T : Subgroup G) (T : Subgroup G) (sSup_le fun _ hE => hE.1) le_rfl hJne)
  have hCM : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M := by
    let D := (omega₁ (center (T : Subgroup G)) (p := 2)).map (center (T : Subgroup G)).subtype
    let : (omega₁ (center (T : Subgroup G)) (p := 2)).Characteristic := omega₁_characteristic _
    let : D.Characteristic := inferInstance
    have hd : D ≠ ⊥ := omega_center_ne_bot T.isPGroup'
    exact (Subgroup.centralizer_le_normalizer _).trans
      (normalizer_le_characteristicNormalizerClosure (T : Subgroup G) D hd)
  have hfix : U ⊓ centralizer ((T : Subgroup G) : Set G) = U ⊓ omegaOneCenterAmbient (T : Subgroup G) := by
    apply le_antisymm
    · intro u hu
      exact ⟨hu.1, (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hUT hu.1, elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu.1, hu.2⟩⟩
    · intro u hu
      exact ⟨hu.1, ((mem_omegaOneCenterAmbient_iff _ _).mp hu.2).2.2⟩
  have hK := fixed_kernel_image U q hq hk (T : Subgroup G) L hLq
  rw [hfix] at hK
  have hKM : subspaceKernel (NormalElementaryQuotient.representation U q hq hk)
      (fixedSpace (NormalElementaryQuotient.representation U q hq hk) ((T : Subgroup G).map q)) ⊤ ≤ M.map q := by
    rw [← hK]
    exact map_mono ((fixed_line_centralizer_le L hL hm T hTL hchar).trans hCM)
  have hM : M.map q = ⊤ := by
    rcases thompson_image U (T : Subgroup G) q hq hk hUT A ha with hb | he
    · rw [hb, Subgroup.normalizer_eq_top] at hNM
      exact top_unique hNM
    · rw [he] at hNM
      exact top_unique (hgen ▸ sup_le hNM hKM)
  have hc := congrArg (Subgroup.comap q) hM
  rw [comap_map_eq, comap_top, sup_eq_left.mpr (hkT.trans hTM)] at hc
  exact hc

end CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
