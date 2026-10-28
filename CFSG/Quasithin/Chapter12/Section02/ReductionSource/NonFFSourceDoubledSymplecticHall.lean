module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSetup
public import Theory.GroupTheory.ReducedNormal.OrbitMinimality
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Transport

/-!
# Hall kernels on the whole doubled symplectic orbit

The actual T-fixed subgroup generates the whole chosen orbit under L:
homogeneous-orbit minimality applies because T normalizes both L and the
fixed seed, and the multiple-overgroup/non-FF hypotheses kill the fixed
layer. The perfect-centralizer factorization then makes every odd section
kernel in an original H-star subgroup centralize this whole orbit.

Hall conjugacy and the original 4.4.13 escape theorem produce an elementary
odd actor if the prescribed Hall action is not faithful. The final reduction
retains the original quotient-conjugation image on L/O₂(L), its actual Sylow
and cyclic Cartan witness. No identification of the chosen seed with its
orbit, or of L/O₂(L) with its central quotient, is made. The symplectic
applications are in NonFFSourceDoubledSymplecticHallParameters; the odd
normalizer and Cartan exclusions are still required for 7.3.4.

Source: Aschbacher--Smith 4.4.5, 4.4.13--14 and 7.3.4,
printed pp.620,623--625,699 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The whole orbit has trivial L-fixed subgroup under the original ambient hypotheses. -/
theorem sourceOrbit_whole_fixed_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    D.sourceOrbit ⊓ centralizer (L : Set G) = ⊥ := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (F.moduleSubgroup : Set G) := by
    simpa only [F, D.fundamentalSetup_module, ← D.sourceOrbit_eq] using
      D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon
  have hf := Chapter10.source_fullModule_fixed_eq_bot_of_many F hmany hJ
  rw [D.localOrbit_eq] at hf
  have hWF : D.sourceOrbit ≤ F.fullModule := by
    change D.sourceOrbit ≤ componentOrbit F.moduleSubgroup F.maximalLocal
    rw [D.fundamentalSetup_module, ← D.sourceOrbit_eq]
    exact le_componentOrbit _ _
  exact bot_unique ((inf_le_inf_right _ hWF).trans_eq hf)

/-- The T-fixed vectors generate the whole orbit under L, including the doubled case. -/
theorem sourceOrbit_sylowFixed_generates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    D.sourceOrbit = conjugateSpanBy (D.sourceOrbit ⊓ centralizer (T : Set G)) L := by
  let Z := D.sourceOrbit ⊓ centralizer (T : Set G)
  let U := conjugateSpanBy Z L
  have hUW : U ≤ D.sourceOrbit :=
    conjugateSpanBy_le inf_le_left D.sourceOrbit_component_normalizes
  have hZ : Z ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups
    (T : Subgroup G) D.sourceOrbit T.isPGroup'
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
    D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.nontrivial
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    exact (le_centralizer_iff.mpr (show Z ≤ centralizer (T : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    normalizes_conjugateSpanBy Z L T hTZ D.sylow_normalizes_component
  have hI : ReducedNormal.subspaceImage (L ⊔ (T : Subgroup G)) D.space = V := D.image_eq
  have hmin := ReducedNormal.subspaceImage_orbit_eq_or_le_centralizer
    (L ⊔ (T : Subgroup G)) L (T : Subgroup G) le_sup_left le_sup_right
    D.irrPlus U (by simpa only [hI, ← D.sourceOrbit_eq] using hUW)
    (le_normalizer_conjugateSpanBy Z L) hTU
  rcases hmin with he | hc
  · simpa only [hI, ← D.sourceOrbit_eq] using he.symm
  · exact (hZ (bot_unique ((le_conjugateSpanBy Z L).trans
      ((le_inf hUW hc).trans_eq (D.sourceOrbit_whole_fixed_eq_bot h hmany hnon))))).elim

/-- The literal odd section kernel fixes the whole orbit in the source 4.4.14 argument. -/
theorem sourceOrbit_whole_odd_sectionKernel_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G)))
    (A : Subgroup G) (hAH : A ≤ H) (hAC : A ≤ Chapter4.sectionCentralizer L)
    (hodd : Odd (Nat.card A)) : A ≤ centralizer (D.sourceOrbit : Set G) := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hcore : L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
    apply le_trans (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component))
    have hh := (D.orbit_centralizer h.toHypothesis1221).symm.le.trans inf_le_right
    simpa only [← D.sourceOrbit_eq] using hh
  have hseed : D.sourceOrbit ⊓ centralizer (T : Set G) ≤ centralizer (A : Set G) := by
    have hΩ : D.sourceOrbit ⊓ centralizer (T : Set G) ≤
        Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
      intro z hz
      apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      exact ⟨D.sourceOrbit_weakClosure_setup.le_sylow hz.1,
        elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1, hz.2⟩
    exact hΩ.trans (le_centralizer_iff.mp
      (hAH.trans (D.sourceOrbit_hstar_centralizes_omega h.toHypothesis1221 hnon hH)))
  exact le_centralizer_iff.mp
    (Chapter4.Section04.centralization_in_4_4_14 L A D.sourceOrbit T hAC hodd hcore hseed
      (D.sourceOrbit_sylowFixed_generates h hmany hnon)).1

/-- Any nonfaithful Hall choice gives an actual elementary odd actor fixing the whole orbit and having an escaping normalizer. -/
theorem sourceOrbit_whole_nonfaithful_hall_escaping_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ Chapter4.sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
      A ≤ centralizer (D.sourceOrbit : Set G) ∧
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
    D.sourceOrbit_whole_odd_sectionKernel_centralizes h hmany hnon hH A hAH hAC hodd,
    hAT, hout⟩

open ChapterE.Section06.FixedPointBounds Chapter7.NormalizedSource.MathieuGeneration in
/-- The original generation parameter is bounded by the actual quotient Cartan parameter, or there is an explicit odd-normalizer obstruction. -/
theorem sourceOrbit_whole_generation_or_odd_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < generationParameter H) :
    generationParameter H ≤ nPrime (normalizerPCoreQuotientAction L).range ∨
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have hFM : F.maximalLocal = normalizer (L : Set G) := by
    change normalizer (Chapter3.Section02.localOrbit T L : Set G) = _
    rw [D.localOrbit_eq]
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := hFM.symm ▸ hH
  obtain ⟨hP, f, _, hf, d, he, _, _⟩ :=
    Chapter10.source_hstar_cartan_data_of_generation_gt_one F hH' hlarge
  have he' : ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H := by simpa only [hFM] using he
  by_cases hk : d.witness.abelianGroup.map H.subtype ⊓ Chapter4.sectionCentralizer L = ⊥
  · left
    let w := overlapWitness hH.1.1.2 D.sylow_normalizes_component d he'
    apply hf.trans (le_nPrime_quotientAction_of_faithful L w ?_)
    exact (congrArg (fun C : Subgroup G => C ⊓ Chapter4.sectionCentralizer L)
      (overlapWitness_cyclic_image hH.1.1.2 D.sylow_normalizes_component d he')).trans
        (bot_unique ((inf_le_inf_right _ (map_mono d.witness.cyclic_le)).trans_eq hk))
  · exact Or.inr (D.sourceOrbit_whole_nonfaithful_hall_escaping_actor h hmany hnon hH hlarge
      d.witness.abelianGroup (d.hall_le.trans_eq he') (he' ▸ d.hall) hk)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
