module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentNaturalResidualAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredComparisonAt

/-!
# Both nonsplit component quotients are ordinary at the original G,T

Cubic generation identifies the reciprocal residuals with their literal
subgroup maps. A covered selected component is impossible: if the original
component is ordinary, the common point residual has three-rank one; if
both are covered, their common point radical has the Baumann subgroup of
the selected KT two-core and forces K into N_G(L). The earlier fixed-module
clause constructs each augmentation marking on the actual moved orbit.

With K ordinary, its nonfixed augmentation point bounds the original L1
by three-rank one and makes L ordinary too. The final theorem constructs
both quotients and the reciprocal two-residual identity. These are the
same-G,T proofs from Nonsolvable/ComponentSix and ComponentContainment;
only genuine earlier structural and fixed-module inputs remain. The
ComponentSixGeometryAt application retains the original five-dimensional V.
Source: Aschbacher--Smith 12.2.8, 13.4.10(2--5), printed pp.797,908--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Both selected A₆ covering rows have the same literal reciprocal point
residual as the original component, without a whole-module hypothesis. -/
theorem six_component_reciprocal_residual_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    {z : G} (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z} : Set G)))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (eK : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* alternatingGroup (Fin 6)) :
    Solvable.firstCentralizerResidual K m.constant.val =
      Solvable.firstCentralizerResidual L z := by
  let := h.quasisimple
  let := hqK
  have htK := component_theta_of_six_central_quotient h₀ hzT hz1 hK hHN hqK eK
  have htL := h.toHypothesis1221.source_theta_eq_of_central_quotient_six
    D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) (augmentationCentralQuotient D m)
  have hd := fixed_generator_centralizer_at h structural D m
    ⟨m.constant.property,m.constant_fixed⟩
    (fun hh => m.constant_ne_one (Subtype.ext hh))
  rw [six_point_residual_cubic K eK,
    six_point_residual_cubic L (augmentationCentralQuotient D m),hd]
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro x ⟨⟨hxK,hxM⟩,h3⟩
    exact ⟨⟨htL ▸ Subgroup.subset_closure ⟨hxM,h3⟩,hK.1 hxK⟩,h3⟩
  · apply Subgroup.closure_mono
    rintro x ⟨⟨hxL,hxz⟩,h3⟩
    exact ⟨⟨htK ▸ Subgroup.subset_closure ⟨hxz,h3⟩,L.le_normalizer hxL⟩,h3⟩

/-- A covered augmentation module on the actual nonsplit selected component
is impossible. Reciprocal cubic generation supplies the common point radical. -/
theorem covered_component_excluded_of_source_fixed_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hcK : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) : False := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hqK := component_quotient_quasisimple h1332 hfK
  let := hqK
  let := h.quasisimple
  obtain ⟨DK,⟨mK⟩,hfix,_,_,_,_⟩ := component_core_marking_of_source_fixed_at
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K = U := by
    have hh := component_seed_split h₀ hzT hz1 hK.1 (h1332 K hfK).1
    rw [component_full_fixed_line_at h structural z.val hz1 hzT hindex K hK.1 hKM,
      sup_eq_left.mpr (show zpowers z.val ≤ U from hfix.symm ▸ inf_le_left)] at hh
    exact hh
  have hdT := (m.constant_mem_central_four_at h structural).2
  have hdU : m.constant.val ∈ U := hsplit ▸ le_conjugateSpanBy _ _ hdT
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hrec := six_component_reciprocal_residual_at h₀ h structural D m
    hzT hz1 hK hHN hqK (augmentationCentralQuotient DK mK)
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
      (augmentationCentralQuotient D m) ho with hcL | ⟨_,hcL⟩
  · let eL := GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (augmentationCentralQuotient D m) hcL
    have hr : primeRank 3 (Solvable.firstCentralizerResidual K m.constant.val) ≤ 1 := by
      rw [hrec,Solvable.firstCentralizerResidual_threeRank]
      exact core_component_point_threeRank_le_one D m eL z hzL
    obtain ⟨eK⟩ := Solvable.ordinary_of_firstCentralizerResidual_threeRank DK mK
      ⟨m.constant.val,hdU⟩ hdK hr
    have hone : Nat.card (center (K ⧸ pCore 2 K)) = 1 := by
      rw [Nat.card_congr (centerCongr eK).toEquiv,
        alternatingGroup.center_eq_bot (by simp),Subgroup.card_bot]
    omega
  · have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
    have hK12 := h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩ hqK
    let P := Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
    let X := K ⊔ (T : Subgroup G)
    have he := (covered_augmentation_thompson_baumann_at hK12 structural DK mK hcK
      ⟨m.constant.val,hdU⟩ hdT hdK).2
    rw [hrec] at he
    have hKB : K ≤ normalizer (ChapterB.baumann (P.pCoreIn 2) : Set G) := by
      rw [he]
      exact (le_sup_left.trans (X.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))).trans
          (normalizer_le_normalizer_baumann (X.pCoreIn 2))
    exact hKM (hKB.trans
      (covered_augmentation_baumann_normalizer_at h structural D m hcL z hzT hzL))

/-- The nonsplit source branch has an ordinary selected A₆ quotient. Its
augmentation marking and the exclusion of the covering row are constructed. -/
theorem ordinary_component_of_source_fixed_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  let := component_quotient_quasisimple h1332 hfK
  obtain ⟨DK,⟨mK⟩,_,_,_,_,_⟩ := component_core_marking_of_source_fixed_at
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hn : ¬ 2 ∣ Nat.card (center (K ⧸ pCore 2 K)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (K ⧸ pCore 2 K)) le_rfl
  have ho : Odd (Nat.card (center (K ⧸ pCore 2 K))) :=
    Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
      (augmentationCentralQuotient DK mK) ho with hc | ⟨_,hc⟩
  · exact ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (augmentationCentralQuotient DK mK) hc⟩
  · exact (covered_component_excluded_of_source_fixed_at h₀ h structural D m h1332 fixed
      hindex z hzT hzL hK hHN hKM hfK hc hfixed).elim

/-- The actual nonsplit orbit, not a separately chosen component module,
puts L₁ in a point centralizer of K and excludes the covered original L. -/
theorem ordinary_original_of_nonsplit_ordinary_component_at
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Solvable.firstCentralizerResidual L z.val ≤ K ∧
      primeRank 3 (Solvable.firstCentralizerResidual L z.val) = 1 ∧
      m.constant.val ∈ U ∧
      (pResidual 2 (K ⊓ centralizer
          (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Subgroup G)).map
          (K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype =
        (pResidual 2 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({z.val} : Set G)).subtype := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hqK := component_quotient_quasisimple h1332 hfK
  have hTK := (h1332 K hfK).1
  obtain ⟨_,hL₁K⟩ := component_residual_of_ordinary_six h₀ hzT hz1 hK hHN hqK eK
  obtain ⟨DK,⟨mK⟩,hfix,_,_,_,hZcard⟩ := component_core_marking_of_source_fixed_at
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hzU : zpowers z.val ≤ U := hfix.symm ▸ inf_le_left
  have hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K = U := by
    have hh := component_seed_split h₀ hzT hz1 hK.1 hTK
    rw [component_full_fixed_line_at h structural z.val hz1 hzT hindex K hK.1 hKM,
      sup_eq_left.mpr hzU] at hh
    exact hh
  have hdU : m.constant.val ∈ U := hsplit ▸
    le_conjugateSpanBy _ _ (m.constant_mem_central_four_at h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hCKZ := component_four_seed_centralizer_at h structural D m hzT hz1 hK.1 hKM hZcard
  have hLC : Solvable.firstCentralizerResidual L z.val ≤
      K ⊓ centralizer ({m.constant.val} : Set G) := by
    refine le_inf hL₁K ?_
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (m.constant_fixed a ((Solvable.firstCentralizerResidual_le L z.val ha).1))
  have hr : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≤ 1 :=
    (_root_.primeRank_le_of_injective 3 (inclusion hLC) (inclusion_injective _)).trans
      (core_component_point_threeRank_le_one DK mK eK ⟨m.constant.val,hdU⟩ hdK)
  let := h.quasisimple
  have hordinary := Solvable.ordinary_of_firstCentralizerResidual_threeRank D m z hzL hr
  obtain ⟨_,hthree⟩ := Solvable.firstCentralizerResidual_order_of_marking D m z hzL
  have hrne : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≠ 0 :=
    fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hthree
  obtain ⟨eL⟩ := hordinary
  refine ⟨⟨eL⟩,hL₁K,by omega,hdU,?_⟩
  rw [hCKZ]
  exact (core_component_point_twoResidual DK mK eK ⟨m.constant.val,hdU⟩ hdK).trans
      ((component_reciprocal_residual_of_ordinary_six_at h₀ h structural m hzT hz1
        hK hHN hqK eK eL).trans (core_component_point_twoResidual D m eL z hzL).symm)


/-- Source application: neither component quotient is supplied as ordinary.
Both are constructed on the nonsplit branch, together with the literal
L₁ containment and the reciprocal O² centralizer identity. -/
theorem nonsplit_component_ordinary_residuals_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Solvable.firstCentralizerResidual L z.val ≤ K ∧
      primeRank 3 (Solvable.firstCentralizerResidual L z.val) = 1 ∧
      m.constant.val ∈ U ∧
      (pResidual 2 (K ⊓ centralizer
          (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Subgroup G)).map
          (K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype =
        (pResidual 2 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({z.val} : Set G)).subtype := by
  obtain ⟨eK⟩ := ordinary_component_of_source_fixed_at h₀ h structural D m h1332 fixed hindex
    z hzT hzL hK hHN hKM hfK hfixed
  exact ⟨⟨eK⟩,ordinary_original_of_nonsplit_ordinary_component_at h₀ h structural m h1332
    fixed hindex z hzT hzL hK hHN hKM hfK eK hfixed⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
