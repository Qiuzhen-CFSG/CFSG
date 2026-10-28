module

public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.ElementaryThompsonComponent

/-!
# The central and Thompson-normal branches of the Baumann alternative

In characteristic two, a nontrivial local center contains a central
involution. If the Sylow omega-center centralizes H, this involution gives
an actual common normal subgroup in the local two-core. Likewise, when
J(T) centralizes V, Thompson heredity identifies it with J(O₂(M₀)); if H
normalizes it, it is a common normal subgroup. Uniqueness excludes both
possibilities and gives the original minimal-parabolic reduction.

These are the first two branches in the proof of source 3.1.7. The final
noncentral Baumann branch, using C.5 and E.2, is a separate obligation.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.575–576.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G]

theorem common_normal_of_center_ne_bot
    (T : Sylow 2 G) {M₀ H : Subgroup G}
    (hT : (T : Subgroup G) ≤ M₀) (hchar : HasCharacteristicTwo M₀)
    (hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype)
    (hc : center M₀ ≠ ⊥) : HasCommonNormal M₀ H (M₀.pCoreIn 2) := by
  have hcore : center M₀ ≤ pCore 2 M₀ := by
    intro z hz
    exact hchar (fun y _ => mem_center_iff.mp hz y)
  have hp : IsPGroup 2 (center M₀) := (show IsPGroup 2 (pCore 2 M₀) from
    pCore_isPGroup).to_le hcore
  let : Nontrivial (center M₀) := (nontrivial_iff_ne_bot _).mpr hc
  obtain ⟨n, hn, hcard⟩ := hp.nontrivial_iff_card.mp inferInstance
  have hd : 2 ∣ Nat.card (center M₀) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' (G := center M₀) 2 hd
  let a : G := x.val.val
  have ha2 : a ^ 2 = 1 := by
    have he : x ^ 2 = 1 := by rw [← hxorder]; exact pow_orderOf_eq_one x
    exact congrArg (M₀.subtype.comp (center M₀).subtype) he
  have hane : a ≠ 1 := by
    intro he
    have hx : x = 1 := Subtype.ext (Subtype.ext he)
    simp [hx] at hxorder
  have haC : a ∈ centralizer (M₀ : Set G) := by
    intro m hm
    exact congrArg M₀.subtype (mem_center_iff.mp x.property ⟨m, hm⟩)
  have haCore : a ∈ M₀.pCoreIn 2 := ⟨x.val, hcore x.property, rfl⟩
  have hcoreT : M₀.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT] using
      pCoreIn_le_sylow M₀ (T.subtype hT)
  have haZ : a ∈ omegaOneCenterAmbient (T : Subgroup G) :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hcoreT haCore, ha2, fun t ht => haC t (hT ht)⟩
  have haH : a ∈ centralizer (H : Set G) := by
    obtain ⟨z, hz, he⟩ := hZ haZ
    intro y hy
    rw [← he]
    exact congrArg H.subtype (mem_center_iff.mp hz ⟨y, hy⟩)
  let N := zpowers a
  have hNR : N ≤ M₀.pCoreIn 2 := zpowers_le.mpr haCore
  have hNM : N ≤ centralizer (M₀ : Set G) := zpowers_le.mpr haC
  have hNH : N ≤ centralizer (H : Set G) := zpowers_le.mpr haH
  refine ⟨N, hNR, ?_, normalIn_iff_le_normalizer.mpr ⟨?_, ?_⟩⟩
  · intro he
    exact hane (mem_bot.mp (he ▸ mem_zpowers a))
  · exact hNR.trans ((pCoreIn_le 2 M₀).trans le_generated_left)
  · rw [generated_eq_sup]
    exact sup_le
      ((le_centralizer_iff.mp hNM).trans (Subgroup.centralizer_le_normalizer _))
      ((le_centralizer_iff.mp hNH).trans (Subgroup.centralizer_le_normalizer _))

theorem QrcHypotheses.center_eq_bot_of_omega_center_centralizes
    {T : Sylow 2 G} {M M₀ H V : Subgroup G}
    (h : QrcHypotheses T M M₀ H V)
    (hE : IsEvenCharacteristicAt T) (hM : IsMaximalTwoLocal M)
    (hu : ∀ Y : Subgroup G, IsMaximalTwoLocal Y → M₀ ≤ Y → Y = M)
    (hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    center M₀ = ⊥ := by
  have hMH : M ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1, h.sylow_le.trans h.left_le⟩
  have h0H := mem_HOver_of_sylow_interval T h.sylow_le h.left_le hMH
  have hchar := Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T hE h0H)
  by_contra hc
  exact h.no_common_normal hu (common_normal_of_center_ne_bot T h.sylow_le hchar hZ hc)

omit [Finite G] in
private theorem normalizer_le_normalizer_maxJ (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change S.map (MulAut.conj g).toMonoidHom = S at hg
  change (elementaryAbelianMaxJ S).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv, hg]

theorem QrcHypotheses.common_normal_of_thompson_normal
    {T : Sylow 2 G} {M M₀ H V : Subgroup G}
    (h : QrcHypotheses T M M₀ H V) (hM : IsMaximalTwoLocal M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hn : H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    HasCommonNormal M₀ H (M₀.pCoreIn 2) := by
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ M₀.pCoreIn 2 := by
    rw [h.core_eq_centralizer]
    exact le_inf hJT hJ
  have hRT : M₀.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [h.core_eq_centralizer]
    exact inf_le_left
  have hje := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G)
    (M₀.pCoreIn 2) hJR hRT
  have hnR : M₀ ≤ normalizer (M₀.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
      range_subtype] using (pCore 2 M₀).le_normalizer_map M₀.subtype
  have hnJ : M₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [← hje]
    exact hnR.trans (normalizer_le_normalizer_maxJ _)
  have hMT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (h.sylow_le.trans h.left_le)] using
      pCoreIn_le_sylow M (T.subtype (h.sylow_le.trans h.left_le))
  have hTne : (T : Subgroup G) ≠ ⊥ := fun he =>
    Chapter1.mem_H_of_isTwoLocal hM.1 (bot_unique (hMT.trans_eq he))
  let : Nontrivial T := (nontrivial_iff_ne_bot (T : Subgroup G)).mpr hTne
  have hJne : elementaryAbelianMaxJ (T : Subgroup G) ≠ ⊥ := by
    intro he
    apply elementaryAbelianMaxJ_top_ne_bot_of_isPGroup T.isPGroup'
    apply (map_eq_bot_iff_of_injective _ (T : Subgroup G).subtype_injective).mp
    rw [← elementaryAbelianMaxJ_map_injective (T : Subgroup G).subtype
      (T : Subgroup G).subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype]
    exact he
  refine ⟨_, hJR, hJne, normalIn_iff_le_normalizer.mpr ⟨?_, ?_⟩⟩
  · exact hJT.trans (h.sylow_le.trans le_generated_left)
  · rw [generated_eq_sup]
    exact sup_le hnJ hn

theorem QrcHypotheses.minimalParabolic_of_thompson_centralizes
    {T : Sylow 2 G} {M M₀ H V : Subgroup G}
    (h : QrcHypotheses T M M₀ H V) (hM : IsMaximalTwoLocal M)
    (hu : ∀ Y : Subgroup G, IsMaximalTwoLocal Y → M₀ ≤ Y → Y = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ChapterB.IsMinimalParabolicOver T H := by
  apply HStar.minimalParabolic T (h.sylow_le.trans h.left_le) h.right_mem (Or.inr ?_)
  intro hn
  have hHN : H ≤ normalizer (T : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.right_mem.1.1.2).mp hn
  exact h.no_common_normal hu (h.common_normal_of_thompson_normal hM hJ
    (hHN.trans (normalizer_le_normalizer_maxJ _)))

end CFSG.Quasithin.Chapter3
