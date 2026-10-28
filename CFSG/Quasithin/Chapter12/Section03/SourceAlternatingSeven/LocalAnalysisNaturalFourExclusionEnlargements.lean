module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionSourceEndgame
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedInput
public import Theory.GroupTheory.Fitting.TwoCoreMonotonicity
public import Theory.GroupTheory.CComponent.FittingNormalizerQuotient

/-!
# Quasisimple enlargements of the central-line residual

For the four-dimensional A₇ row, write D=C_L(z)∞ and Q=O₂(DT).
The relative 1.2.4 theorem makes every C-component containing D normal
in C_G(z). Its two-Fitting subgroup normalizes D, which forces its
quotient by O₂ to be quasisimple.

Every T-invariant overgroup of D has its two-core inside Q: the two-core
lies in T and centralizes D/O₂(D), where Q is Sylow. This controls the
literal O₂(N_K(V)) and identifies O₂(KQ) with O₂(KT). The resulting C.2.7
input uses the original groups, and its moved star module is exactly
the embedded source module V(K,O₂(KT)).

The final theorem applies these facts to the strict overcomponent already
constructed by the block/Frattini argument. Selecting its natural module
and excluding the resulting enlargement remain subsequent steps.

Source: Aschbacher–Smith, Lemma 12.3.3, printed pp.807–808;
1.2.4 and C.2.7–C.2.8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

private theorem sylow_le_centralizer {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    (T : Subgroup G) ≤ S.fourPointCentralizer z := by
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)

private theorem point_le_local (z : G) :
    S.fourComponentPointPerfect z ≤ S.fourPointLocal z :=
  (map_subtype_le _).trans (inf_le_inf_right _ L.le_normalizer)

theorem four_overcomponent_normalized
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z))
    (hDK : S.fourComponentPointPerfect z ≤ K) :
    S.fourPointCentralizer z ≤ normalizer (K : Set G) := by
  let H := S.fourPointCentralizer z
  let TH : Sylow 2 H := T.subtype (S.sylow_le_centralizer hzT)
  let D := S.fourComponentPointPerfect z
  have hDH : D ≤ H := (S.point_le_local z).trans inf_le_right
  have hD : D.subgroupOf H ∈ Chapter1.L H (TH : Subgroup H) :=
    (Chapter1.mem_LIn_iff_subgroupOf (S.sylow_le_centralizer hzT) hDH).mp
      ⟨hDH,S.four_componentPointPerfect_local hz hz1 hzT e hd⟩
  have hTD : (TH : Subgroup H) ≤ normalizer (D.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hDH]
    exact comap_mono ((le_inf S.chosen.sylow_normalizes_component
      (S.sylow_le_centralizer hzT)).trans S.four_componentPointPerfect_normalized)
  have hsq := S.hypothesis.simpleQTKE.involution_centralizer_sqtk
    (orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hzT).2.2 hz1)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  obtain ⟨A,⟨hA,hDA,hnA⟩,hu⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ TH hD hTD
  have he : K.subgroupOf H = A :=
    Chapter1.Section02.IndexTwo.cComponent_unique_over_nonsolvable
      (Chapter1.mem_L_not_isSolvable hD)
      hK.2 hA (comap_mono hDK) hDA
  exact (normal_subgroupOf_iff_le_normalizer hK.1).mp (he.symm ▸ hnA)

theorem four_overcomponent_quasisimple
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z))
    (hDK : S.fourComponentPointPerfect z ≤ K) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let H := S.fourPointCentralizer z
  let D := S.fourComponentPointPerfect z
  let KH := K.subgroupOf H
  have hn := S.four_overcomponent_normalized e hd hz hz1 hzT hK hDK
  let : KH.Normal := (normal_subgroupOf_iff_le_normalizer hK.1).mpr hn
  let k : KH ≃* K := subgroupOfEquivOfLe hK.1
  let B := (D.subgroupOf H).subgroupOf KH
  have hbH : D ≤ H := hDK.trans hK.1
  have hb : D.subgroupOf H ≤ KH := comap_mono hDK
  let d : B ≃* D := (subgroupOfEquivOfLe hb).trans (subgroupOfEquivOfLe hbH)
  let := Theory.SpecificGroups.LinearHigher.psl_isQuasisimple (F := ZMod 2) (n := 3) (by decide)
  have hq : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans
      (S.fourComponentPointCoreEquiv e hd ⟨z,hz⟩
        (fun he => hz1 (congrArg Subtype.val he)))).symm
  have htop : (⊤ : Subgroup KH).IsCComponent := by
    have hk : KH.IsCComponent := hK.2
    simpa only [subgroupOf_self] using hk.subgroupOf (le_refl KH)
  have hf : twoFittingCore KH ≤ normalizer (B : Set KH) := by
    have hFM := (twoFittingCore_map_subtype_le_of_normal KH).trans
      (S.four_component_pushingUp structural e hd hz hz1 hzT).fitting_preimage_le
    rw [← subgroupOf_normalizer_eq hb]
    intro x hx
    change (x : H) ∈ normalizer (D.subgroupOf H : Set H)
    rw [← subgroupOf_normalizer_eq hbH]
    exact S.four_componentPointPerfect_normalized
      (hFM (mem_map_of_mem KH.subtype hx))
  let hKH := quasisimple_quotient_of_fitting_normalizes htop B hq hf
  exact IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ k (pCore_map_iso 2 k))

/-- Every T-invariant overgroup of D has its two-core in the source Q. -/
theorem four_core_le_pointCore
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {N : Subgroup G} (hDN : S.fourComponentPointPerfect z ≤ N)
    (hTN : (T : Subgroup G) ≤ normalizer (N : Set G)) :
    N.pCoreIn 2 ≤ S.fourComponentPointCore z := by
  let D := S.fourComponentPointPerfect z
  let U := N.pCoreIn 2
  let Q := S.fourComponentPointCore z
  have hUT : U ≤ (T : Subgroup G) := by
    have huj : U ≤ (N ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le N.le_normalizer hTN)
    have hjt := pCoreIn_le_sylow (N ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hjt
    exact huj.trans hjt
  have hTM : (T : Subgroup G) ≤ S.fourPointLocal z :=
    le_inf S.chosen.sylow_normalizes_component (S.sylow_le_centralizer hzT)
  have hsig : ChapterA.Section04.IsTwoSignalizer D (S.fourPointLocal z) U := by
    apply (ChapterA.Section04.isTwoSignalizer_iff _ _ _).mpr
    exact ⟨hUT.trans hTM,isPGroup_pCoreIn 2 N,
      (hDN.trans N.le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image N (pCore 2 N))⟩
  have hsection := ChapterA.Section04.signalizer_le_twoSectionCentralizer D
    (S.fourPointLocal z) U (S.point_le_local z)
    (normal_subgroupOf_of_le_normalizer S.four_componentPointPerfect_normalized).isSubnormal
    (S.four_componentPointPerfect_faithful structural e hd hz hz1 hzT).1.2.1 hsig
  have hUH : U ≤ ChapterA.Section04.twoSectionCentralizer D (S.fourPointCentralizer z) :=
    fun _ hu => ⟨(hsection hu).1.2,(hsection hu).2⟩
  have hs := Chapter1.isSylowIn_iff.mp (S.four_componentPointCore_section_sylow hzT)
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (D ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact le_sup_left.trans (hs.2.2 (U ⊔ Q)
    (T.isPGroup'.to_le (sup_le hUT hQT)) le_sup_right (sup_le hUH hs.2.1)).le

/-- The literal O₂(N_K(V)) is contained in Q, as needed for the
transvection contradiction. -/
theorem four_overcomponent_moduleNormalizer_core_le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z))
    (hDK : S.fourComponentPointPerfect z ≤ K) :
    (K ⊓ normalizer (V : Set G)).pCoreIn 2 ≤ S.fourComponentPointCore z := by
  apply S.four_core_le_pointCore structural e hd hz hz1 hzT
    (le_inf hDK ((map_subtype_le _).trans (inf_le_left.trans S.chosen.normalizes)))
  apply le_trans (le_inf
    ((S.sylow_le_centralizer hzT).trans
      (S.four_overcomponent_normalized e hd hz hz1 hzT hK hDK))
    (((structural G T L S.hypothesis).2.2 V S.chosen).1.trans
      (normalizer (V : Set G)).le_normalizer)) inf_normalizer_le_normalizer_inf

/-- Hence the original normalizer core has trivial action on V. The A₈
module geometry must provide the conflicting transvection action. -/
theorem four_overcomponent_moduleNormalizer_core_centralizes
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z))
    (hDK : S.fourComponentPointPerfect z ≤ K) :
    (K ⊓ normalizer (V : Set G)).pCoreIn 2 ≤ centralizer (V : Set G) :=
  (S.four_overcomponent_moduleNormalizer_core_le structural e hd hz hz1 hzT hK hDK).trans
    (S.four_componentPointCore_centralizes structural e hd hz hz1 hzT)

/-- C.2.7's join KQ has the same core as the source join KT. -/
theorem four_overcomponent_joinCore_eq
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z))
    (hDK : S.fourComponentPointPerfect z ≤ K) :
    (K ⊔ S.fourComponentPointCore z).pCoreIn 2 = (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let D := S.fourComponentPointPerfect z
  let Q := S.fourComponentPointCore z
  let J := K ⊔ (T : Subgroup G)
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (D ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hsub : K ⊔ Q ≤ J := sup_le_sup_left hQT K
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (S.sylow_le_centralizer hzT).trans
      (S.four_overcomponent_normalized e hd hz hz1 hzT hK hDK)
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (le_sup_right.trans (D ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image (D ⊔ (T : Subgroup G)) (pCore 2 _))
  apply le_antisymm
  · apply pCoreIn_mono_of_normalizes hsub
    exact sup_le (le_sup_left.trans (K ⊔ Q).le_normalizer)
      ((le_inf hTK hTQ).trans (normalizer_inf_normalizer_le_normalizer_sup K Q))
  · have hc : J.pCoreIn 2 ≤ Q := S.four_core_le_pointCore structural e hd hz hz1 hzT
      (hDK.trans le_sup_left) (le_sup_right.trans J.le_normalizer)
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) (hc.trans le_sup_right)
      ((hsub.trans J.le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

theorem four_overcomponent_C27_input
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z))
    (hDK : S.fourComponentPointPerfect z ≤ K)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hout : ¬ K ≤ S.fourPointLocal z) :
    Input KnownSimple.IsKnownSimple (S.fourPointCentralizer z)
      (S.fourComponentPointCore z) (S.fourPointLocal z) K := by
  have hp := S.four_component_pushingUp structural e hd hz hz1 hzT
  have hn := S.four_overcomponent_normalized e hd hz hz1 hzT hK hDK
  have hf := Chapter1.Section02.Adequate.mem_L_isSignalizerType T
    (S.hypothesis.simpleQTKE.evenCharacteristic T) hKL
  exact ⟨hp.constrained_pushingUpSetup,hK,
    S.four_overcomponent_quasisimple structural e hd hz hz1 hzT hK hDK,
    hf.2.2,hout,(hp.radical_le.trans hp.local_le).trans hn⟩

/-- The actual C.2.7 moved star module is the source module V(K,O₂(KT)).
In particular this comparison retains the original embedding in G. -/
theorem four_overcomponent_star_moved_eq
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    {K : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn (S.fourPointCentralizer z))
    (hDK : S.fourComponentPointPerfect z ≤ K) :
    (⁅starV K (S.fourComponentPointCore z),
      K.subgroupOf (K ⊔ S.fourComponentPointCore z)⁆).map
        (K ⊔ S.fourComponentPointCore z).subtype =
      ChapterA.Section04.signalizerModule K ((K ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let Q := S.fourComponentPointCore z
  let J := K ⊔ Q
  have he : (starV K Q).map J.subtype = Stellmacher.omegaOneCenterAmbient (J.pCoreIn 2) := by
    change (Stellmacher.omegaOneCenterAmbient (pCore 2 J)).map J.subtype = _
    exact (Stellmacher.omegaOneCenterAmbient_map_injective _
      J.subtype_injective (pCore 2 J)).symm
  rw [map_commutator, map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left), he,
    S.four_overcomponent_joinCore_eq structural e hd hz hz1 hzT hK hDK,
    ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter, commutator_comm]

/-- The actual strict overcomponent has a quasisimple quotient and supplies
C.2.7, its kernel and offender conclusions, and the original nonzero fixed
point in its canonical module. -/
theorem four_exists_quasisimple_C27_enlargement
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ∃ K : Subgroup G,
      S.fourComponentPointPerfect z < K ∧
      Input KnownSimple.IsKnownSimple (S.fourPointCentralizer z)
        (S.fourComponentPointCore z) (S.fourPointLocal z) K ∧
      S.fourPointCentralizer z ≤ normalizer (K : Set G) ∧
      KernelConclusion K (S.fourComponentPointCore z) ∧
      OffenderConclusion K (S.fourComponentPointCore z) ∧
      (K ⊓ normalizer (V : Set G)).pCoreIn 2 ≤ centralizer (V : Set G) ∧
      (K ⊔ S.fourComponentPointCore z).pCoreIn 2 = (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      V ≤ ChapterA.Section04.signalizerModule K ((K ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      z ∈ ChapterA.Section04.signalizerModule K ((K ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
        centralizer (K : Set G) := by
  obtain ⟨K,hK,hDK,hout,hKL,hf,hTK,hV,hzK⟩ :=
    S.four_component_exists_strict_overcomponent structural escape e hd hz hz1 hzT
  have hi := S.four_overcomponent_C27_input structural e hd hz hz1 hzT hK hDK.le hKL hout
  have ho := ChapterC.C27Source.kernel_offender_from_source hi
  exact ⟨K,hDK,hi,S.four_overcomponent_normalized e hd hz hz1 hzT hK hDK.le,
    ho.1,ho.2,
    S.four_overcomponent_moduleNormalizer_core_centralizes structural e hd hz hz1 hzT hK hDK.le,
    S.four_overcomponent_joinCore_eq structural e hd hz hz1 hzT hK hDK.le,hV,hzK⟩

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
