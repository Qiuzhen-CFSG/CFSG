module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PointKernelAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredSelection

/-!
# Covered solvable-centralizer exclusion from structural facts at G,T

Use the literal R = O₂(L₁T), with L₁ = O^{3′}(C_L(z)). The covered
augmentation comparison already bounds N_G(Baum(R)) by N_G(L). Augmentation
13.3.9 places the selected kernel residual in L₁. Since that residual is
normal in H = C_G(z), core restriction puts its commutator with R in its
own two-core. Thus R lies in the full residual-section centralizer.

The two action-kernel cases now give Thompson noncentrality and the
three-rank bound, which excludes the triple cover. This is a specialized
covered-row argument: it never identifies R with the source R₁, nor uses
an ordinary-only residual or quotient equality. All selection and Baumann
premises are discharged at the original G,T. The original chosen-module
application is in AugmentationSolvableAt; full symplectic recognition still
requires the ordinary and nonsolvable assembly and earlier source inputs.

Source: Aschbacher--Smith 13.3.9, 13.4.4 and 13.4.8, pp.887,897,904--905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable Nonsolvable
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual larger action kernel supplies every residual premise of the
three-rank argument, using structural facts only at the original G,T. -/
theorem centralizer_firstResidual_threeRank_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (R : Subgroup G) (hRT : R ≤ T)
    (hQR : (centralizer ({z.val} : Set G)).pCoreIn 2 ≤ R)
    (hRC : R ≤ centralizerResidualSection T z.val)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) :
    primeRank 3 (firstCentralizerResidual L z.val) ≤ 1 := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  let H := centralizer ({z.val} : Set G)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let K := centralizer (U : Set H)
  let A := (pResidual 2 K).map K.subtype
  let C := residualSectionCentralizer 2 K
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let N := I.subgroupOf H
  let B := (firstCentralizerResidual L z.val).subgroupOf H
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hIH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  let : A.Normal := inferInstance
  let : (A.pCoreIn 2).Normal := inferInstanceAs ((pCore 2 A).map A.subtype).Normal
  have hIC := (centralizer_intersection_of_residual_section h₀ hz hz1 R hRT hQR hRC).2
  have hnC : N ≤ C := by
    intro x hx
    exact (mem_map_iff_mem H.subtype_injective).mp (hIC hx)
  have hcomm : ⁅N,A⁆ ≤ A.pCoreIn 2 :=
    (commutator_mono hnC le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ A (A.pCoreIn 2) le_normalizer_of_normal)
  let eN : N ≃* I := subgroupOfEquivOfLe hIH
  have hpJ : IsPGroup 2 (elementaryAbelianMaxJ R) :=
    (T.isPGroup'.to_le hRT).to_le (sSup_le fun _ hA => hA.1)
  obtain ⟨n,hn⟩ := hpJ.exists_card_eq
  have hperf : IsPPerfect 3 I := isPPerfect_conjugateSpanBy_of_coprime _ _
    (by rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_right n)
  have hperfN := hperf.of_surjective eN.symm.toMonoidHom eN.symm.surjective
  obtain ⟨hAplus,hcard⟩ := centralizer_kernel_residual_at h₀ h structural D m z hz hzL hout hlarge
  have hQK : pCore 2 H ≤ K := le_centralizer_iff.mp hU.le_centralizer_pCore
  have hm := centralizer_thompson_span_models h₀ hz hz1 R hRT hQR hJ hsolv
  have hrank : primeRank 3 H ≤ 2 :=
    (isQuasithin_iff_twoLocal.mp h₀.qtke.quasithin) H
      (isTwoLocal_involution_centralizer
        (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1))
      3 (by decide) (by decide)
  have hBH : firstCentralizerResidual L z.val ≤ H :=
    (firstCentralizerResidual_le L z.val).trans inf_le_right
  have hSB : (T.subtype hTH : Subgroup H) ≤ normalizer (B : Set H) := by
    rw [← subgroupOf_normalizer_eq hBH]
    exact subgroupOf_mono H (firstCentralizerResidual_sylow_normalizes D hz)
  let eB : B ≃* firstCentralizerResidual L z.val := subgroupOfEquivOfLe hBH
  have hBperf : IsPPerfect 2 B := (firstCentralizerResidual_twoPerfect L z.val).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  let := h.quasisimple
  obtain ⟨ho,hthree⟩ := firstCentralizerResidual_order_of_marking D m z hzL
  have hoB : ∃ a b : ℕ, Nat.card B ∣ 2 ^ a * 3 ^ b := by
    rwa [Nat.card_congr eB.toEquiv]
  have hthreeB : 3 ∣ Nat.card B := by rwa [Nat.card_congr eB.toEquiv]
  have hclass : ∀ Y : Subgroup H, Y.Normal → IsPPerfect 2 Y → Y ≤ B → Y ≤ K := by
    intro Y hYn hYp hYB
    let := hYn
    let Z := Y.map H.subtype
    have hZB : Z ≤ firstCentralizerResidual L z.val := by
      have hh := map_mono (f := H.subtype) hYB
      rwa [map_subgroupOf_eq_of_le hBH] at hh
    have hZn : H ≤ normalizer (Z : Set G) := by
      have hh := Y.le_normalizer_map H.subtype
      simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
    have hZp : IsPPerfect 2 Z := hYp.of_surjective
      (H.subtype.subgroupMap Y) (H.subtype.subgroupMap_surjective Y)
    have hZM : Z ≤ normalizer (L : Set G) :=
      hZB.trans ((firstCentralizerResidual_le L z.val).trans (inf_le_left.trans L.le_normalizer))
    rcases augmentation_point_residual_at h structural D m z hz hzL hout
      (map_subtype_le _) hZn hZM hZp with he | ⟨he,_⟩
    · have hY : Y = ⊥ := (map_eq_bot_iff_of_injective _ H.subtype_injective).mp he
      rw [hY]; exact bot_le
    · apply le_trans _ (map_subtype_le (pResidual 2 K))
      exact (map_le_map_iff_of_injective H.subtype_injective).mp (by
        change Z ≤ A.map H.subtype
        exact he.le.trans hAplus.ge)
  have hr := CubicResidualSelection.actor_rank_le_one K N B hQK hcard hperfN hcomm hm hrank
    (T.subtype hTH) hSB hBperf hoB hthreeB hclass
  rwa [primeRank_congr 3 eB] at hr


/-- The selected covered residual lies in the literal L₁, so it normalizes
O₂(L₁T). This does not identify that two-core with the original R₁. -/
theorem covered_selectedFirstResidual_le_first_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    selectedFirstResidual T L V z.val ≤ firstCentralizerResidual L z.val := by
  classical
  unfold selectedFirstResidual
  split_ifs
  · exact le_rfl
  · rw [←covered_firstFlagNormalizer_residual_at h structural D m hc z hz hzL]
    exact plus_le_one L _ _ ((sylow_le_firstFlagNormalizer (L := L) (V := V)).trans inf_le_right)

/-- The two-core of the literal first parabolic centralizes the selected
kernel residual modulo its own two-core. All residual-selection premises
are supplied by augmentation 13.3.9 at this same G,T. -/
theorem covered_firstParabolicCore_le_residualSection_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G))) :
    firstParabolicCore T L z.val ≤ centralizerResidualSection T z.val := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  let H := centralizer ({z.val} : Set G)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let K := centralizer (U : Set H)
  let A := (pResidual 2 K).map K.subtype
  let Y := A.map H.subtype
  let P := firstCentralizerResidual L z.val ⊔ (T : Subgroup G)
  let R := firstParabolicCore T L z.val
  have hY := (centralizer_kernel_residual_at h₀ h structural D m z hz hzL hout hlarge).1
  have hYP : Y ≤ P := hY.le.trans
    ((covered_selectedFirstResidual_le_first_at h structural D m hc z hz hzL).trans le_sup_left)
  have hPH : P ≤ H := sup_le ((firstCentralizerResidual_le L z.val).trans inf_le_right)
    (original_sylow_le_centralizer hz)
  have hnY : H ≤ normalizer (Y : Set G) := by
    have hh := A.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hnR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hcomm : ⁅R,Y⁆ ≤ Y.pCoreIn 2 := by
    apply le_trans ?_ (inf_pCoreIn_le_of_le 2 hYP)
    exact le_inf
      (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 P).trans (hPH.trans hnY)))
      (le_normalizer_iff_commutator_le_left.mp (hYP.trans hnR))
  rw [centralizerResidualSection_eq_of_residual h₀ hz hz1 Y rfl]
  exact le_commutatorPreimage ((pCoreIn_le 2 P).trans hPH) hcomm

/-- Covered solvable escape is impossible using the literal O₂(L₁T).
Both full action-kernel cases are discharged, without a universal Chapter 12
record, an R₁ identification, or an additional residual premise. -/
theorem covered_solvable_escape_impossible_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) : False := by
  classical
  let H := centralizer ({z.val} : Set G)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  let R := firstParabolicCore T L z.val
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨hRT,hnR,hAN,hQR⟩ := firstParabolicCore_local_data (L := L) hz
  have hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G) :=
    covered_augmentation_baumann_normalizer_at h structural D m hc.2.1 z hz hzL
  have hsel := covered_selectedFirstResidual_le_first_at h structural D m hc.2.1 z hz hzL
  have hord : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
    let := h.quasisimple
    by_cases hkernel : centralizer (U : Set H) = pCore 2 H
    · have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
      have hcore : R ⊓ centralizer (centralizerOmegaOrbit T z.val : Set G) = H.pCoreIn 2 := by
        apply le_antisymm
        · intro a ha
          have hc : (⟨a,hRH ha.1⟩ : H) ∈ centralizer (U : Set H) := by
            intro v hv
            exact Subtype.ext (ha.2 v.val hv)
          exact mem_map_of_mem H.subtype (hkernel ▸ hc)
        · intro a ha
          refine ⟨hQR ha,?_⟩
          obtain ⟨b,hb,rfl⟩ := ha
          have hc : b ∈ centralizer (U : Set H) := hkernel.symm ▸ hb
          intro v hv
          exact congrArg Subtype.val (hc ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
      have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hcore hB hout
      exact ordinary_of_centralizer_source1339 h₀ D m z hz hzL R hRT hnR hQR hJ
        hsolv hkernel (selectedFirstResidual T L V z.val) (hsel.trans hAN)
        (fun Y hYH hnY hYM hp =>
          (augmentation_point_residual_at h structural D m z hz hzL hout hYH hnY hYM hp).imp_right
            (fun hh => hh.1))
    · have hRC := covered_firstParabolicCore_le_residualSection_at h₀ h structural D m
        hc.2.1 z hz hzL hout hkernel
      have hcore := (centralizer_intersection_of_residual_section h₀ hz hz1 R hRT hQR hRC).1
      have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hcore hB hout
      exact ordinary_of_firstCentralizerResidual_threeRank D m z hzL
        (centralizer_firstResidual_threeRank_at h₀ h structural D m z hz hzL hkernel hout
          R hRT hQR hRC hJ hsolv)
  obtain ⟨e⟩ := hord
  have hh := Nat.card_congr (centerCongr e).toEquiv
  rw [hc.2.1,alternatingGroup.center_eq_bot (by simp),card_bot] at hh
  omega

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
