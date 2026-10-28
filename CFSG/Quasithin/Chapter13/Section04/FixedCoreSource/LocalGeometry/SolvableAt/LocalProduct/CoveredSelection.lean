module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.CoveredPlacement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.FirstFlagCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.LargerRow
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.OrdinaryOriginal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredPlacement

/-!
# Covered-row exclusion and the original solvable local product: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/CoveredSelection` proof for the local step.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original R₁ and the cubic conclusion of13.3.9 exclude the covered row
when C_H(V_H)=O₂(H). No normalization assumption on L₁,+ remains. -/
theorem ordinary_of_twoCore_kernel_original_R1_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hB : normalizer (ChapterB.baumann (firstFlagCore_at h structural D m) : Set G) ≤
      normalizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G))) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  classical
  let H := centralizer ({z.val} : Set G)
  let R := firstFlagCore_at h structural D m
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨hRT,hnR,hQR⟩ := firstFlagCore_local_data_at h structural D m z hz hzL
  have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
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
  let := h.quasisimple
  have hchoice : ∃ A : Subgroup G, A ≤ normalizer (R : Set G) ∧
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y → Y = ⊥ ∨ Y = A := by
    by_cases hex : ∃ Y : Subgroup G, Y ≤ H ∧ H ≤ normalizer (Y : Set G) ∧
        Y ≤ normalizer (L : Set G) ∧ IsPPerfect 2 Y ∧ Y ≠ ⊥
    · obtain ⟨Y,hYH,hnY,hYM,hpY,hne⟩ := hex
      obtain ⟨he,hc⟩ := (h1339 Y hYH hnY hYM hpY).resolve_left hne
      have hYL : Y ≤ L := he ▸ selectedFirstResidual_le_component D z.val
      refine ⟨Y,(normal_cubic_firstFlagCore_action_at h structural D m z hz hzL hout
        Y hYL hYH hnY hpY hc).2,?_⟩
      intro Z hZH hnZ hZM hpZ
      exact (h1339 Z hZH hnZ hZM hpZ).imp_right (fun hh => hh.1.trans he.symm)
    · refine ⟨⊥,bot_le,?_⟩
      intro Y hYH hnY hYM hpY
      exact Or.inl (by by_contra hn; exact hex ⟨Y,hYH,hnY,hYM,hpY,hn⟩)
  obtain ⟨A,hAN,hclass⟩ := hchoice
  exact ordinary_of_centralizer_source1339 h₀ D m z hz hzL R hRT hnR hQR hJ hsolv
    hkernel A hAN hclass
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal action core centralizes the normal kernel residual modulo
its own two-core, in either covering row. -/
theorem firstFlagCore_le_residualSection_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G))) :
    firstFlagCore_at h structural D m ≤ centralizerResidualSection T z.val := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  let H := centralizer ({z.val} : Set G)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let K := centralizer (U : Set H)
  let A := (pResidual 2 K).map K.subtype
  let Y := A.map H.subtype
  obtain ⟨hA,hcard⟩ := centralizer_kernel_residual_of_source1339_at h₀ h structural D m
    z hz hzL hlarge (selectedFirstResidual T L V z.val) h1339
  have hYL : Y ≤ L := by
    calc
      Y = selectedFirstResidual T L V z.val := hA
      _ ≤ L := selectedFirstResidual_le_component D z.val
  have hnY : H ≤ normalizer (Y : Set G) := by
    have hh := A.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hpY : IsPPerfect 2 Y := (isPPerfect_embedded_pResidual 2 K).of_surjective
    (H.subtype.subgroupMap A) (H.subtype.subgroupMap_surjective A)
  let e := A.equivMapOfInjective H.subtype H.subtype_injective
  have hcY : Nat.card (Y ⧸ pCore 2 Y) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans hcard
  have hcomm := (normal_cubic_firstFlagCore_action_at h structural D m z hz hzL hout Y hYL
    (map_subtype_le _) hnY hpY hcY).1
  rw [centralizerResidualSection_eq_of_residual h₀ hz hz1 Y rfl]
  apply le_commutatorPreimage
    ((firstFlagCore_local_data_at h structural D m z hz hzL).1.trans (original_sylow_le_centralizer hz))
  rwa [commutator_comm]

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- The weaker residual-section containment already suffices to bound the
original centralizer residual's three-rank. -/
theorem centralizer_firstResidual_threeRank_of_residual_section_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (Aplus : Subgroup G)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = Aplus ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
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
  obtain ⟨hAplus,hcard⟩ := centralizer_kernel_residual_of_source1339_at h₀ h structural
    D m z hz hzL hlarge Aplus h1339
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
    rcases h1339 Z (map_subtype_le _) hZn hZM hZp with he | ⟨he,_⟩
    · have hY : Y = ⊥ := (map_eq_bot_iff_of_injective _ H.subtype_injective).mp he
      rw [hY]; exact bot_le
    · apply le_trans _ (map_subtype_le (pResidual 2 K))
      exact (map_le_map_iff_of_injective H.subtype_injective).mp (by
        change Z ≤ A.map H.subtype
        rw [hAplus,he])
  have hr := CubicResidualSelection.actor_rank_le_one K N B hQK hcard hperfN hcomm hm hrank
    (T.subtype hTH) hSB hBperf hoB hthreeB hclass
  rwa [primeRank_congr 3 eB] at hr

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- Both action-kernel cases exclude the covered row before invoking the
ordinary local-product construction. -/
theorem centralizer_pair_quotient_of_baumann_original_R1_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hB : normalizer (ChapterB.baumann (firstFlagCore_at h structural D m) : Set G) ≤
      normalizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) ∧
      I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  classical
  have ordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
    by_cases hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
        pCore 2 (centralizer ({z.val} : Set G))
    · exact ordinary_of_twoCore_kernel_original_R1_at h₀ h structural D m z hz hzL hB hout
        h1339 hsolv hkernel
    · have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
      let R := firstFlagCore_at h structural D m
      obtain ⟨hRT,_,hQR⟩ := firstFlagCore_local_data_at h structural D m z hz hzL
      have hRC := firstFlagCore_le_residualSection_at h₀ h structural D m z hz hzL hout h1339 hkernel
      have hcore := (centralizer_intersection_of_residual_section h₀ hz hz1 R hRT hQR hRC).1
      have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hcore hB hout
      have hr := centralizer_firstResidual_threeRank_of_residual_section_at h₀ h structural D m z hz hzL
        hkernel (selectedFirstResidual T L V z.val) h1339 R hRT hQR hRC hJ hsolv
      let := h.quasisimple
      exact ordinary_of_firstCentralizerResidual_threeRank D m z hzL hr
  exact centralizer_pair_quotient_of_ordinary_baumann_original_R1_at h₀ h structural D m ordinary
    z hz hzL hB hout h1339 hsolv hindex (h1342 ordinary)

/-- The source local product on the original R₁ in every row and both Baumann alternatives. -/
theorem centralizer_pair_quotient_of_original_R1_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore_at h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore_at h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore_at h structural D m)) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) ∧
      I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  rcases hcase with hB | hb
  · exact centralizer_pair_quotient_of_baumann_original_R1_at
      h₀ h structural D m z hz hzL hB hout h1339 hsolv hindex h1342
  · exact centralizer_pair_quotient_of_short_block_original_R1_at
      h₀ h structural D m hb z hz hzL hVJ hout hfusion h1339 hsolv hindex
        (h1342 (ordinary_of_short_core_marking D m hb))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
