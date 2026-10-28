module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Inputs
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.ModuleSize
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.ComponentRows
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.SectionKernel
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter4.Section04.OddActorLargeComponent.Action
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleModels
public import CFSG.Quasithin.Chapter4.Section04.PerfectCentralizer
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Escape
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.HallConjugacy
public import CFSG.Quasithin.Chapter4.Section04.OddActorResidual
public import Theory.GroupTheory.PCoreCoverEquiv
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality
public import Theory.GroupTheory.TwoFixedLinesIrreducible

/-!
# The original Mathieu Hall-kernel obstruction

The non-FF hypothesis makes each original H-star subgroup centralize the
Sylow omega-center. In the invariant-seed branch, fixed-space vanishing and
Irr-plus minimality show that the T-fixed vectors generate the original V.
The perfect-centralizer factorization of 4.4.5 then proves that every odd
section kernel in H centralizes V, discharging the module premise of 4.4.14.

If an arbitrary Hall subgroup of the literal overlap is not faithful, Hall
conjugacy and the proved 4.4.13 construct an elementary odd actor A fixing V,
permuting with T, and with normalizer outside N_G(L). The actual residual
L_A = C_L(A)^infinity covers L modulo O2(L), contains V in its two-core, and
retains the same Mathieu central quotient through the inclusion-induced map.

The Mathieu quotient forces |V| > 8, so the odd core of N_G(A) centralizes
V and lies in N_G(L), completing the actual 4.4.8 step without a uniqueness
callback. Given genuine residual uniqueness, component detection supplies
an outside component with its full Theorem B central-quotient model and
with the literal actions of V and the fixed residual. The prime-eleven outer
section exclusion now places both inside one normal component. The original
module has binary rank at least ten, leaving only relative-rank-two and J₄
central quotients. Every nonfaithful literal Hall choice produces either this
configuration or an actual maximal pushing-up pair.

These are the source reductions for SourceMathieuHallFaithfulAt. The Mathieu
instance of 4.4.3 excluding this final odd-normalizer obstruction remains to
be proved; no Hall-faithfulness or generation callback is assumed here.
Final Hall assembly stays in this module, and the generation-bound assembly
belongs to MathieuGeneration and task qt-d-1222-mathieu-generation-cap.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.5,
4.4.13--14 and 7.3.4, printed pp.620,623--625,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original non-FF orbit forces every original H-star member to fix the
Sylow omega-center, by the proved movement implication of 3.1.8(3). -/
theorem sourceOrbit_hstar_centralizes_omega
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) :
    H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let F := D.fundamentalSetup h
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hHF : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := by
    simpa only [F, Chapter3.Section02.FundamentalSetup.maximalLocal, D.localOrbit_eq] using hH
  have hq := F.qrcHypotheses h127 hHF
  have hu := F.lemma_3_2_3_uniqueness h127
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (F.moduleSubgroup : Set G) := by
    simpa only [F, D.fundamentalSetup_module, ← D.sourceOrbit_eq] using
      D.sourceOrbit_thompson_centralizes h hnon
  have hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      (center H).map H.subtype := by
    by_contra hn
    exact hq.thompson_moves_of_noncentral_omega h.simpleQTKE hu.1 hu.2.2
      F.module_ne_bot hn hJ
  intro x hx z hz
  obtain ⟨zH, hzH, rfl⟩ := hZ hz
  exact (congrArg Subtype.val (mem_center_iff.mp hzH ⟨x, hx⟩)).symm

/-- The literal fixed-seed generation premise in 4.4.14(a). The invariant
Irr-plus seed has no L-fixed vectors, so its nonzero T-fixed vectors generate it. -/
theorem sourceOrbit_fixedSeed_generates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    V = conjugateSpanBy (V ⊓ centralizer (T : Set G)) L := by
  let Z := V ⊓ centralizer (T : Set G)
  let W := conjugateSpanBy Z L
  have hWV : W ≤ V := conjugateSpanBy_le inf_le_left D.normalizes
  have hTW : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    hVW.symm ▸ D.sourceOrbit_weakClosure_setup.normalizes
  let := D.elementary
  have hZ : Z ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups
    (T : Subgroup G) V T.isPGroup' (IsElementaryAbelian.isPGroup 2 V) hTW D.ne_bot
  have hmin := ReducedNormal.subspaceImage_eq_or_le_centralizer
    (L ⊔ (T : Subgroup G)) L le_sup_left D.irrPlus.isIrrPlus W
    (hWV.trans_eq D.image_eq.symm) (le_normalizer_conjugateSpanBy Z L)
  rcases hmin with he | hc
  · exact (he.trans D.image_eq).symm
  · have hfix := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
    exact (hZ (bot_unique ((le_conjugateSpanBy Z L).trans
      ((le_inf hWV hc).trans_eq hfix)))).elim

/-- The actual module-centralization step of 4.4.14. This concerns the
section centralizer of L/O2(L), rather than the centralizer of L itself. -/
theorem sourceOrbit_odd_sectionKernel_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G)))
    (A : Subgroup G) (hAH : A ≤ H) (hAC : A ≤ Chapter4.sectionCentralizer L)
    (hodd : Odd (Nat.card A)) : A ≤ centralizer (V : Set G) := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) := by
    apply le_trans ?_ D.core_centralizes
    exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hseed : V ⊓ centralizer (T : Set G) ≤ centralizer (A : Set G) := by
    have hΩ : V ⊓ centralizer (T : Set G) ≤
        Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
      intro z hz
      apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      refine ⟨D.le_sylow hz.1, ?_, hz.2⟩
      let := D.elementary
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1
    exact hΩ.trans (le_centralizer_iff.mp
      (hAH.trans (D.sourceOrbit_hstar_centralizes_omega h.toHypothesis1221 hnon hH)))
  exact le_centralizer_iff.mp
    (Chapter4.Section04.centralization_in_4_4_14 L A V T hAC hodd hcore hseed
      (D.sourceOrbit_fixedSeed_generates h hmany hVW hnon)).1

/-- Failure for any Hall subgroup of the original overlap produces an
elementary odd actor from the intrinsic Hall witness. Hall conjugacy retains H;
the selected actor need not lie in the originally prescribed Hall subgroup. -/
theorem sourceOrbit_nonfaithful_hall_escaping_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ Chapter4.sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have hM : F.maximalLocal = normalizer (L : Set G) := by
    change normalizer (Chapter3.Section02.localOrbit T L : Set G) = _
    rw [D.localOrbit_eq]
  have hHF : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := hM.symm ▸ hH
  obtain ⟨hP, f, _, _, d, he, _, _⟩ :=
    Chapter10.source_hstar_cartan_data_of_generation_gt_one F hHF hlarge
  have hk : d.witness.abelianGroup ⊓
      (Chapter4.sectionCentralizer (Chapter3.Section02.localOrbit T L)).subgroupOf H ≠ ⊥ := by
    intro hk
    rw [D.localOrbit_eq] at hk
    have he' := he.trans (congrArg (fun M : Subgroup G => M.subgroupOf H) hM)
    exact hker (Chapter10.source_hall_sectionKernel_faithful_of_hall_conjugacy
      (M := normalizer (L : Set G)) (X := L) le_rfl
      (he' ▸ d.maximal_solvable) hBN hHall (he' ▸ d.hall) hk)
  obtain ⟨p, A, hp, ho, hA, hAe, hAY, hAC, hAT, hout⟩ :=
    Chapter10.source_hstar_hall_kernel_escaping_elementary F hHF hlarge hP d hk
  rw [D.localOrbit_eq] at hAC
  rw [hM] at hout
  have hAH : A ≤ H := hAY.trans (map_subtype_le _)
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  exact ⟨p, A, hp, ho, hA, hAe, hAH, hAC,
    D.sourceOrbit_odd_sectionKernel_centralizes h hmany hVW hnon hH A hAH hAC hodd,
    hAT, hout⟩

/-- The fixed residual contains the original module in its two-core and
has the same two-core quotient as L. The equivalence preserves inclusion on
every representative, including any nontrivial covering center. -/
theorem sourceOrbit_oddActorResidual_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G)))
    (A : Subgroup G) (hAH : A ≤ H) (hAC : A ≤ Chapter4.sectionCentralizer L)
    (hodd : Odd (Nat.card A)) :
    let R := Chapter4.Section04.oddActorResidual L A
    (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
      V = ⁅V, R⁆ ∧ V ≤ R.pCoreIn 2 ∧ R.pCoreIn 2 ≠ ⊥ ∧
      ∃ e : (R ⧸ pCore 2 R) ≃* (L ⧸ pCore 2 L),
        ∀ r : R, e (QuotientGroup.mk' (pCore 2 R) r) =
          QuotientGroup.mk' (pCore 2 L)
            (inclusion ((Chapter4.Section04.oddActorResidual_le L A).trans inf_le_left) r) := by
  have hc := (Chapter4.le_sectionCentralizer_iff A L).mp hAC
  obtain ⟨hcover, hgen, hcore, hne⟩ := Chapter4.Section04.chosen_oddActorResidual_cover
    h.toHypothesis1221 D A hc.1 hc.2 hodd
    (D.sourceOrbit_odd_sectionKernel_centralizes h hmany hVW hnon hH A hAH hAC hodd)
  exact ⟨hcover, hgen, hcore, hne, exists_pCoreQuotientEquiv_of_cover
    ((Chapter4.Section04.oddActorResidual_le L A).trans inf_le_left) hcover.subset⟩

/-- The literal classification consumer of the preceding reductions. A
nonfaithful original Hall subgroup yields an escaping odd actor whose actual
fixed residual still has one of the four concrete Mathieu central quotients. -/
theorem sourceOrbit_mathieu_hall_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ Chapter4.sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      let R := Chapter4.Section04.oddActorResidual L A
      (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
        V = ⁅V, R⁆ ∧ V ≤ R.pCoreIn 2 ∧ R.pCoreIn 2 ≠ ⊥ ∧
        Chapter7.NormalizedSource.HasMathieuCentralQuotient (R ⧸ pCore 2 R) := by
  obtain ⟨p, A, hp, ho, hA, hAe, hAH, hAC, hAV, hAT, hout⟩ :=
    D.sourceOrbit_nonfaithful_hall_escaping_actor h hmany hVW hnon hH hlarge
      B hBN hHall hker
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := hAe
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  obtain ⟨hcover, hgen, hcore, hne, e, _⟩ :=
    D.sourceOrbit_oddActorResidual_quotient h hmany hVW hnon hH A hAH hAC hodd
  refine ⟨p, A, hp, ho, hA, hAe, hAH, hAC, hAV, hAT, hout,
    hcover, hgen, hcore, hne, ?_⟩
  have hc : (center _).map e.toMonoidHom = center _ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr e ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e.symm x, ((Subgroup.centerCongr e).symm ⟨x, hx⟩).property,
        e.apply_symm_apply x⟩
  let q := (QuotientGroup.congr _ _ e hc).trans (D.orbitCentralQuotientEquiv h.toHypothesis1221)
  rcases hm with ⟨⟨j⟩⟩ | ⟨⟨j⟩⟩ | ⟨⟨j⟩⟩ | ⟨⟨j⟩⟩
  · exact Or.inl ⟨q.trans j⟩
  · exact Or.inr (Or.inl ⟨q.trans j⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨q.trans j⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨q.trans j⟩))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Source 4.4.8 for the actual Mathieu module: its original odd section
kernel centralizes V, and V centralizes the whole odd core of its normalizer. -/
theorem sourceOrbit_mathieu_oddNormalizer_centralizes_oddCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G)))
    (A : Subgroup G) (hAH : A ≤ H) (hAC : A ≤ Chapter4.sectionCentralizer L)
    (hodd : Odd (Nat.card A)) :
    ⁅V, (pPrimeCore 2 (normalizer (A : Set G))).map
      (normalizer (A : Set G)).subtype⁆ = ⊥ := by
  have hc := (Chapter4.le_sectionCentralizer_iff A L).mp hAC
  exact Chapter4.Section04.chosen_oddNormalizer_centralizes_oddCore_of_large_module
    h.toHypothesis1221 D (D.sourceOrbit_mathieu_card_gt_eight hVW hm) A hc.1 hc.2 hodd
    (D.sourceOrbit_odd_sectionKernel_centralizes h hmany hVW hnon hH A hAH hAC hodd)

/-- The source orbit already has normalizer control. Thus the odd core of
the actual odd normalizer lies in N_G(L), without the unresolved residual
uniqueness premise of 4.4.6. This completes 4.4.8 for the Mathieu instance. -/
theorem sourceOrbit_mathieu_oddNormalizer_oddCore_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G)))
    (A : Subgroup G) (hAH : A ≤ H) (hAC : A ≤ Chapter4.sectionCentralizer L)
    (hodd : Odd (Nat.card A)) :
    (pPrimeCore 2 (normalizer (A : Set G))).map
      (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) := by
  have hc := D.sourceOrbit_mathieu_oddNormalizer_centralizes_oddCore
    h hmany hVW hm hnon hH A hAH hAC hodd
  have hNV : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
    (congrArg (fun W : Subgroup G => normalizer (W : Set G)) hVW).symm ▸
      D.sourceOrbit_normalizer_le h.toHypothesis1221
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNV)

/-- The Mathieu source instance of the component-detection step in 4.4.9--10.
Only the earlier pushing-up uniqueness is still explicit. The chosen V, fixed
residual and component all use the literal inclusion into N_G(A). -/
theorem sourceOrbit_mathieu_oddNormalizer_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAH : A ≤ H) (hAC : A ≤ Chapter4.sectionCentralizer L)
    (hodd : Odd (Nat.card A))
    (hunique : Chapter4.UniqueMaximalOvergroup (Chapter4.Section04.oddActorResidual L A)
      (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧
      ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (Chapter4.Section04.oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) := by
  have hc := (Chapter4.le_sectionCentralizer_iff A L).mp hAC
  obtain ⟨K, hK, hKV, hKM, hcore, hqt, _, hRK, hVK⟩ :=
    Chapter4.Section04.chosen_oddNormalizer_exists_full_component_action_of_large
    h.toHypothesis1221 D (D.sourceOrbit_mathieu_card_gt_eight hVW hm) A hne hc.1 hc.2 hodd
    (D.sourceOrbit_odd_sectionKernel_centralizes h hmany hVW hnon hH A hAH hAC hodd)
    hunique hout
  let : IsQuasisimple K := hK.2
  have hproper := (Chapter4.Section04.oddNormalizer_properQTK h.simpleQTKE A hne).1
  have hkg : IsKGroup KnownSimple.IsKnownSimple K :=
    (h.simpleQTKE.properK _ hproper).subgroup K
  exact ⟨K, hK, hKV, hKM, hcore, hqt,
    ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
      ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
      hqt hkg, hRK, hVK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Literal Hall-kernel application of 4.4.8. Every nonfaithful Hall choice
produces an escaping elementary actor whose whole odd-normalizer odd core
centralizes the original module. The cover and Mathieu quotient stay attached
to the same fixed residual. -/
theorem sourceOrbit_mathieu_hall_oddCore_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hVW : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ Chapter4.sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      ⁅V, (pPrimeCore 2 (normalizer (A : Set G))).map
        (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map
        (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      let R := Chapter4.Section04.oddActorResidual L A
      (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
        V = ⁅V, R⁆ ∧ V ≤ R.pCoreIn 2 ∧ R.pCoreIn 2 ≠ ⊥ ∧
        HasMathieuCentralQuotient (R ⧸ pCore 2 R) := by
  obtain ⟨p, A, hp, ho, hA, he, hAH, hAC, hAV, hAT, hout, hR⟩ :=
    D.sourceOrbit_mathieu_hall_obstruction h hmany hVW hm hnon hH hlarge B hBN hHall hker
  have hodd : Odd (Nat.card A) := by
    let : Fact p.Prime := ⟨hp⟩
    let := he
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  exact ⟨p, A, hp, ho, hA, he, hAH, hAC, hAV, hAT, hout,
    D.sourceOrbit_mathieu_oddNormalizer_centralizes_oddCore h hmany hVW hm hnon
      hH A hAH hAC hodd,
    D.sourceOrbit_mathieu_oddNormalizer_oddCore_le h hmany hVW hm hnon
      hH A hAH hAC hodd, hR⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- With genuine fixed-residual uniqueness, the original Mathieu module and
full residual lie in one normal component of the odd normalizer. The model
outer-section premise is discharged by the prime-eleven argument. -/
theorem sourceOrbit_mathieu_normal_component_of_unique
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    NormalComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent) := by
  let := D.orbitComponent_quasisimple h
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let := h.quasisimple
  have hsect : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L := by
    apply relative_module_centralizer_le_sectionCentralizer L V D.normalizes
      _ D.ne_bot D.eq_commutator
    exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  have hc := (le_sectionCentralizer_iff A L).mp (hA.trans hsect)
  have hAV := hA.trans inf_le_right
  have hcover := (chosen_oddActorResidual_cover h D A hc.1 hc.2 ho hAV).1
  obtain ⟨q,_⟩ := exists_pCoreQuotientEquiv_of_cover
    (p := 2) (A := oddActorResidual L A) (L := L)
    ((oddActorResidual_le L A).trans inf_le_left) hcover.subset
  have hz : (center _).map q.toMonoidHom = center _ := by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr q ⟨z,hz⟩).property
    · intro z hz
      exact ⟨q.symm z,(centerCongr q.symm ⟨z,hz⟩).property,q.apply_symm_apply z⟩
  let e := (QuotientGroup.congr _ _ q hz).trans (D.orbitCentralQuotientEquiv h)
  apply normal_component_of_unique_and_no_outer_sections
    (S := D.orbitComponent ⧸ center D.orbitComponent) h D
    (D.sourceOrbit_mathieu_card_gt_eight hV hm) hsect A hne hc.1 hc.2 ho hAV hu hout e
  intro K hcomp hmodel U f
  let : IsQuasisimple K := hcomp.2
  exact mathieu_centralQuotient_no_outer_section hmodel hm U f

set_option maxHeartbeats 400000 in
/-- Every nonfaithful literal Hall subgroup yields either the actual maximal
pushing-up configuration or a normal component of relative rank two or J₄.
No uniqueness or model-exclusion callback is assumed. Eliminating these
remaining configurations is still required for `SourceMathieuHallFaithfulAt`. -/
theorem sourceOrbit_mathieu_hall_component_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (PushingUpCase L V A ∨
        MathieuComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent)) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout⟩ :=
    @sourceOrbit_nonfaithful_hall_escaping_actor G instG finG T L V D
      h hmany hV hnon H hH hlarge B hBN hHall hker
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  have hc := (le_sectionCentralizer_iff A L).mp hAC
  refine ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,?_⟩
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · have hcomp := D.sourceOrbit_mathieu_normal_component_of_unique h.toHypothesis1221 hV hm
      A hne (le_inf hc.1 hAV) hodd hu hout
    exact .inr (D.sourceOrbit_mathieu_component_rows h.toHypothesis1221 hV hm
      A hc.1 hc.2 hodd hAV hcomp)
  · have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    have hjoin : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
      ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
    exact .inl (pushingUp_case_of_not_unique h.toHypothesis1221 D hjoin
      A hc.1 hc.2 hodd hAV hu)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
