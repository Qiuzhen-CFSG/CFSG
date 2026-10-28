module
public import CFSG.Quasithin.Chapter14.Section06.SourceF9
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# Normalizer control in the abelian plane branch

A nontrivial normal two-perfect subgroup of the original H cannot lie in M.
Otherwise its action on the four-group V fixes the central point, so its image
has order at most two and is trivial. Normality extends this centralization
to the H-conjugate span of V; the actual F.9 kernel then places the subgroup
in O₂(H), contradicting two-perfectness. This proves 14.6.1(4) directly.

For O₂(H) ≤ T₁ normal in T, characteristic two puts Ω₁Z(T₁) inside
Ω₁Z(O₂(H)). The already proved 14.6.1(5) centralizes this subgroup with the
generalized-Fitting preimage. That preimage has a nontrivial two-residual:
otherwise H/O₂(H) would have trivial generalized Fitting subgroup and thus
be trivial. Part (4) and the actual uniqueness of Mc now force the entire
omega-center normalizer into Mc. The suitable-involution condition (U3)
then identifies N_G(T₀) with T.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemmas 14.6.1(4,6) and 14.6.3(2), pp. 1020–1021.
All statements use the original rank-two source input and ambient subgroups.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem normal_twoPerfect_not_le_seedNormalizer
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (hcard : Nat.card D.V = 4)
    (X : Subgroup G) (hXH : X ≤ D.H) (hHX : D.H ≤ normalizer (X : Set G))
    (hp : IsPPerfect 2 X) (hne : X ≠ ⊥) : ¬ X ≤ normalizer (D.V : Set G) := by
  intro hXV
  let f := setupSeedAction X D.V hXV
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp
    (show D.V₁ ≠ ⊥ by intro hh; have hc := h.point_card; simp [hh] at hc)
  let v : D.V := ⟨z, h.plus_le (h.point_lt.le z.property)⟩
  have hv : v ≠ 1 := fun he => hz (Subtype.ext (congrArg (fun w : D.V => (w : G)) he))
  have hfix : ∀ a ∈ f.range, a v = v := by
    rintro a ⟨x, rfl⟩
    apply Subtype.ext
    change (x : G) * (z : G) * (x : G)⁻¹ = z
    rw [← h.H_centralizes (hXH x.property) z z.property, mul_inv_cancel_right]
  have hbound := card_mulAut_subgroup_le_two_of_fixed_point hcard v hv f.range hfix
  have hftwo : IsPGroup 2 f.range := by
    have hpos := Nat.card_pos (α := f.range)
    have hc : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by omega
    rcases hc with hc | hc
    · exact IsPGroup.of_card (n := 0) (by simpa using hc)
    · exact IsPGroup.of_card (n := 1) (by simpa using hc)
  have hf := hp.hom_eq_one_of_isPGroup hftwo f.rangeRestrict
  have hXC : X ≤ centralizer (D.V : Set G) := by
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun hf ⟨x, hx⟩)
    exact (setupSeedAction_ker X D.V hXV).le hh
  have hXU : X ≤ centralizer (D.UH : Set G) := by
    change X ≤ centralizer (conjugateSpanBy D.Vplus D.H : Set G)
    exact le_centralizer_conjugateSpanBy_of_normalizes X D.Vplus D.H hHX
      (hXC.trans (centralizer_le h.plus_le))
  have hXQ : X ≤ D.QH := by
    rw [← h.kernel_UH_eq_QH]
    intro x hx
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hXH hx, fun a ha => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hXU hx a ha)]
      exact D.V₁.one_mem⟩
  have htriv := hp.hom_eq_one_of_isPGroup (isPGroup_pCoreIn 2 D.H) (inclusion hXQ)
  apply hne
  apply eq_bot_iff.mpr
  intro x hx
  change x = 1
  exact congrArg (fun q : D.QH => (q : G)) (DFunLike.congr_fun htriv ⟨x,hx⟩)

omit [Finite G] in
private theorem intermediate_core_ne_bot
    {H J : Subgroup G} (hne : H.pCoreIn 2 ≠ ⊥)
    (hQJ : H.pCoreIn 2 ≤ J) (hJH : J ≤ H) : J.pCoreIn 2 ≠ ⊥ := by
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hle := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hQJ (hJH.trans hHQ)
  exact fun hz => hne (le_bot_iff.mp (hz ▸ hle))

/-- Original 14.6.1(4): adjoining T to a nontrivial normal two-perfect
subgroup of H gives another member of the literal H(T,M) family. -/
theorem source_lemma_14_6_1_4
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (X : Subgroup G) (hXH : X ≤ H) (hHX : H ≤ normalizer (X : Set G))
    (hp : IsPPerfect 2 X) (hne : X ≠ ⊥) :
    X ⊔ (T : Subgroup G) ∈ Chapter1.HOutside G (T : Set G) (M : Set G) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH
  have hn := normal_twoPerfect_not_le_seedNormalizer h hcard X hXH hHX hp hne
  have hMV : M ≤ normalizer (localModule T M : Set G) := by
    simpa only [Section02.rankTwoSeed_eq_localModule] using
      (RankTwoHypothesis.M_normalizes_seed (T := T) (M := M))
  refine ⟨⟨intermediate_core_ne_bot hH.1.1 (h.QH_le_T.trans le_sup_right)
    (sup_le hXH hH.1.2), fun x hx =>
      (le_sup_right : (T : Subgroup G) ≤ X ⊔ (T : Subgroup G)) hx⟩, ?_⟩
  exact fun hle => hn (le_sup_left.trans (hle.trans hMV))

private theorem fittingPreimage_residual_nontrivial
    (T : Sylow 2 G) {H M : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hTM : (T : Subgroup G) ≤ M) (hout : ¬ H ≤ M) :
    (pResidual 2 (ChapterA.Section04.twoGeneralizedFittingPreimage H)).map
      (ChapterA.Section04.twoGeneralizedFittingPreimage H).subtype ≠ ⊥ := by
  let F := ChapterA.Section04.twoGeneralizedFittingPreimage H
  let F₀ := (generalizedFitting (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))
  have hFH : F ≤ H := map_subtype_le _
  have hHF : H ≤ normalizer (F : Set G) := by
    change H ≤ normalizer (F₀.map H.subtype : Set G)
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      F₀.le_normalizer_map H.subtype
  intro hz
  have hr : pResidual 2 F = ⊥ := (map_eq_bot_iff_of_injective _ F.subtype_injective).mp hz
  have hFp : IsPGroup 2 F := (isPGroup_quotient_pResidual (G := F) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 F)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk', hr])
  have hFQ : F ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes hFp hFH hHF
  have hFbot : generalizedFitting (H ⧸ pCore 2 H) = ⊥ := by
    apply eq_bot_iff.mpr
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) y
    have hx : (x : G) ∈ F := mem_map_of_mem H.subtype hy
    have hxQ : x ∈ pCore 2 H := by
      obtain ⟨q, hq, he⟩ := hFQ hx
      exact (Subtype.ext he : q = x) ▸ hq
    exact (QuotientGroup.eq_one_iff x).mpr hxQ
  have htriv : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ ⊥ := by
    have hc := centralizer_generalizedFitting_le (H ⧸ pCore 2 H)
    rw [hFbot] at hc
    apply le_trans ?_ hc
    intro y _ z hz
    have hz1 : z = 1 := hz
    simp [hz1]
  apply hout
  intro x hx
  have hxQ : (⟨x,hx⟩ : H) ∈ pCore 2 H :=
    (QuotientGroup.eq_one_iff ⟨x,hx⟩).mp
      (htriv (mem_top (QuotientGroup.mk' (pCore 2 H) ⟨x,hx⟩)))
  exact hTM (((pCoreIn_le_sylow H (T.subtype hTH)).trans_eq
    (map_subgroupOf_eq_of_le hTH)) (mem_map_of_mem H.subtype hxQ))

omit [Finite G] in
private theorem normalizer_le_omegaCenter_normalizer (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer (omegaOneCenterAmbient A : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective, hx]

/-- Original 14.6.1(6), including the intermediate omega-center normalizer. -/
theorem source_lemma_14_6_1_6
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (T1 : Subgroup G) (hQT1 : H.pCoreIn 2 ≤ T1) (hT1T : T1 ≤ (T : Subgroup G))
    (hTT1 : (T : Subgroup G) ≤ normalizer (T1 : Set G)) :
    normalizer (T1 : Set G) ≤ normalizer (omegaOneCenterAmbient T1 : Set G) ∧
      normalizer (omegaOneCenterAmbient T1 : Set G) ≤ Mc := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH
  let F := ChapterA.Section04.twoGeneralizedFittingPreimage H
  let F₀ := (generalizedFitting (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H))
  let X := (pResidual 2 F).map F.subtype
  have hXF : X ≤ F := map_subtype_le _
  have hFH : F ≤ H := map_subtype_le _
  have hHF : H ≤ normalizer (F : Set G) := by
    change H ≤ normalizer (F₀.map H.subtype : Set G)
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      F₀.le_normalizer_map H.subtype
  have hHX : H ≤ normalizer (X : Set G) := hHF.trans
    (normalizer_le_normalizer_characteristic_image F (pResidual 2 F))
  have hXne : X ≠ ⊥ := fittingPreimage_residual_nontrivial T hH.1.2 hM.1.2 hH.2
  have hXP : IsPPerfect 2 X := isPPerfect_embedded_pResidual 2 F
  have hXT := source_lemma_14_6_1_4 hG T hempty hM hu hmany hcard e hab H hH X
    (hXF.trans hFH) hHX hXP hXne
  have huniq := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    (X ⊔ (T : Subgroup G)) hXT.1 hXT.2).1
  let W := omegaOneCenterAmbient T1
  have hNW : normalizer (T1 : Set G) ≤ normalizer (W : Set G) :=
    normalizer_le_omegaCenter_normalizer T1
  have hself : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2 := by
    intro x hx
    have hc : (⟨x,hx.1⟩ : H) ∈ centralizer (pCore 2 H : Set H) := by
      intro q hq
      exact Subtype.ext (hx.2 q (mem_map_of_mem H.subtype hq))
    have hh := centralizer_generalizedFitting_le H
    rw [h.characteristic_H] at hh
    exact mem_map_of_mem H.subtype (hh hc)
  have hWcore : W ≤ omegaOneCenterAmbient (H.pCoreIn 2) := by
    intro w hw
    obtain ⟨hwT1, hw2, hwc⟩ := (mem_omegaOneCenterAmbient_iff T1 w).mp hw
    have hwcQ : w ∈ centralizer (H.pCoreIn 2 : Set G) :=
      (centralizer_le hQT1) hwc
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hself ⟨hH.1.2 (hT1T hwT1), hwcQ⟩, hw2, hwcQ⟩
  have hHZ := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1 hH.2).2
  have hFC : F ≤ centralizer (W : Set G) :=
    (source_generalizedFittingPreimage_centralizes_omegaCore hG T hempty hH hHZ).trans
      (centralizer_le hWcore)
  have hXTN : X ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) := sup_le
    ((hXF.trans hFC).trans (Subgroup.centralizer_le_normalizer _)) (hTT1.trans hNW)
  have hT1ne : T1 ≠ ⊥ := fun hz => hH.1.1 (le_bot_iff.mp (hz ▸ hQT1))
  let : Nontrivial T1 := (nontrivial_iff_ne_bot T1).mpr hT1ne
  have hWne : W ≠ ⊥ := by
    intro hz
    exact omega_center_ne_bot (T.isPGroup'.to_le hT1T)
      ((map_eq_bot_iff_of_injective _ T1.subtype_injective).mp hz)
  have hlocal : IsTwoLocal (normalizer (W : Set G)) :=
    ⟨W, hWne, (omegaOneCenterAmbient_elementaryAbelian T1).isPGroup, rfl⟩
  obtain ⟨N, hWN, hN⟩ := Finite.exists_le_maximal hlocal
  have hNMc : N = Mc := Set.mem_singleton_iff.mp
    (huniq ▸ (show N ∈ maximalTwoLocalOvergroups (X ⊔ (T : Subgroup G)) from
      ⟨hN, hXTN.trans hWN⟩))
  exact ⟨hNW, hNMc ▸ hWN⟩

/-- Original 14.6.3(2). Core containment is the preceding part (1), the
index is (U1), and the relative normalizer equality is the literal (U3). -/
theorem source_lemma_14_6_3_2
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (T0 : Subgroup G) (hQT0 : H.pCoreIn 2 ≤ T0) (hT0T : T0 ≤ (T : Subgroup G))
    (hindex : T0.relIndex (T : Subgroup G) = 2)
    (hU3 : Mc ⊓ normalizer (T0 : Set G) = (T : Subgroup G)) :
    normalizer (T0 : Set G) = (T : Subgroup G) := by
  have hTT0 : (T : Subgroup G) ≤ normalizer (T0 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hT0T).mp (normal_of_index_eq_two hindex)
  obtain ⟨hN, hMc⟩ := source_lemma_14_6_1_6 hG T hempty hM hu hmany hcard e hab H hH
    T0 hQT0 hT0T hTT0
  apply le_antisymm _ hTT0
  exact (le_inf (hN.trans hMc) le_rfl).trans_eq hU3

end CFSG.Quasithin.Chapter14.Section06
