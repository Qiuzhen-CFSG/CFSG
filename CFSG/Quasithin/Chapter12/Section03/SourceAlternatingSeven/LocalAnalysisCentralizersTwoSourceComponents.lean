module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceRigidity
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceNonquasisimple
public import CFSG.Quasithin.Chapter1.Section02.Adequate.OrbitFaithful

/-!
# Containing components of the weight-two centralizer

The literal A₅ residual is a faithful local component. The source
containment theorem supplies a normal containing component in C_G(e).
Both the nonquasisimple maximal branch and the second natural A₇ branch
are excluded. Only recognition of proper quasisimple maximal overcomponents
remains explicit in the normality theorem; its discharge belongs to
qt-d-1236-1238-point-centralizers, as does final assembly of 12.3.8.

Source: Aschbacher–Smith, 1.2.4, 1.2.9 and 12.3.8, pp.505,507,809–810.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Subgroup Theory.GroupTheory Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

/-- The original A₅ residual belongs to the T-local component family. -/
theorem five_local_family
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    P.five ∈ Chapter1.L G (T : Subgroup G) := by
  have hJ : P.five ⊔ (T : Subgroup G) ≤
      centralizer ({(P.two : G)} : Set G) ⊓ normalizer (L : Set G) :=
    sup_le (le_inf ((pointResidual_le L (P.two : G)).trans inf_le_right)
      ((pointResidual_le L (P.two : G)).trans (inf_le_left.trans L.le_normalizer)))
      (le_inf (fun t ht => mem_centralizer_singleton_iff.mpr (P.two_central t ht))
        (S.hypothesis.source_sylow_normalizes structural))
  refine ⟨P.two_local_component.subgroupOf_of_le le_sup_left hJ, ?_, ?_⟩
  · exact ⟨T.subtype le_sup_right, by
      simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]⟩
  · intro he
    have hV : V ≤ (P.five ⊔ (T : Subgroup G)).pCoreIn 2 :=
      S.chosen.le_core.trans (Setup.NaturalCoordinates.core_le_subjoin_core P.five
        ((pointResidual_le L (P.two : G)).trans inf_le_left))
    exact S.chosen.ne_bot (bot_unique (he ▸ hV))

/-- The containing component is normal in the actual ambient point centralizer. -/
theorem two_containing_component
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({(P.two : G)} : Set G)) ∧
      centralizer ({(P.two : G)} : Set G) ≤ normalizer (K : Set G) ∧
      P.five ≤ K ∧ K ∈ Chapter1.L G (T : Subgroup G) := by
  let H := centralizer ({(P.two : G)} : Set G)
  have hTH : (T : Subgroup G) ≤ H := fun t ht =>
    mem_centralizer_singleton_iff.mpr (P.two_central t ht)
  have hBH : P.five ≤ H := (pointResidual_le L (P.two : G)).trans inf_le_right
  let TH := T.subtype hTH
  have hB : P.five.subgroupOf H ∈ Chapter1.L H (TH : Subgroup H) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTH hBH).mp ⟨hBH,P.five_local_family structural⟩
  have hTB : (TH : Subgroup H) ≤ normalizer (P.five.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hBH]
    exact comap_mono (pointResidual_normalized S.chosen.sylow_normalizes_component P.two_central)
  have ho : orderOf (P.two : G) = 2 :=
    orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp P.two_mem_omega).2.2 P.two_ne_one
  have hH := S.hypothesis.simpleQTKE.involution_centralizer_sqtk ho
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hH.isKGroup.quotient _⟩
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hd _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp hd)
  obtain ⟨A,⟨hA,hBA,hnA⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ TH hB hTB
  let K := A.map H.subtype
  have hKH : K ≤ H := map_subtype_le _
  have he : K.subgroupOf H = A := comap_map_eq_self_of_injective H.subtype_injective A
  have hc : K ∈ Chapter1.cComponentsIn H := ⟨hKH,he.symm ▸ hA⟩
  have hlocal := (Chapter1.lemma_1_2_6 T
    (show H ∈ Chapter1.HOver G (T : Set G) from
      ⟨Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer ho),hTH⟩)).1 hc
  refine ⟨K,hc,(normal_subgroupOf_iff_le_normalizer hKH).mp (he.symm ▸ hnA),?_,hlocal.2⟩
  calc
    P.five = (P.five.subgroupOf H).map H.subtype := (map_subgroupOf_eq_of_le hBH).symm
    _ ≤ K := map_mono hBA

/-- A nonquasisimple maximal overcomponent cannot enlarge the point component. -/
theorem two_component_eq_of_nonquasisimple_maximal
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    {K Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({(P.two : G)} : Set G)))
    (hfive : P.five ≤ K) (hKY : K ≤ Y)
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (Y ⧸ pCore 2 Y)) : K = P.five :=
  P.two_container_eq_of_le_normalizer hK.1 hK.2 hfive
    (hKY.trans (le_sup_left.trans (E.nonquasisimple_overgroup_le_normalizer structural escape hY hn)))

/-- The second-A₇ argument applies at the maximal overcomponent itself;
no identification of the intermediate component with that overcomponent is needed. -/
theorem two_component_eq_of_seven_maximal
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    {K Y W : Subgroup G} (SY : Setup T Y W)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({(P.two : G)} : Set G)))
    (hfive : P.five ≤ K) (hKY : K ≤ Y) : K = P.five := by
  obtain ⟨EY⟩ := natural Y W SY
  exact P.two_container_eq_of_le_normalizer hK.1 hK.2 hfive
    (hKY.trans (P.second_seven_le_normalizer structural escape SY EY (hfive.trans hKY)))

/-- Component rigidity now retains only recognition of proper quasisimple
maximal overcomponents. The source assembly must discharge that model premise. -/
theorem two_normalizes_of_quasisimple_maximal_models
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (models : ∀ Y : Subgroup G, Y ∈ Chapter1.LStar G (T : Subgroup G) →
      P.five < Y → IsQuasisimple (Y ⧸ pCore 2 Y) →
      ∃ W : Subgroup G, Nonempty (Setup T Y W)) :
    centralizer ({(P.two : G)} : Set G) ≤ normalizer (P.five : Set G) := by
  obtain ⟨K,hK,hnK,hBK,hlocal⟩ := P.two_containing_component structural
  obtain ⟨Y,hY,hKY⟩ := Chapter1.exists_mem_LStar_ge hlocal
  have hBY := hBK.trans hKY
  have he : K = P.five := by
    by_cases he : P.five = Y
    · exact le_antisymm (hKY.trans_eq he.symm) hBK
    by_cases hq : IsQuasisimple (Y ⧸ pCore 2 Y)
    · obtain ⟨W,⟨SY⟩⟩ := models Y hY (lt_of_le_of_ne hBY he) hq
      exact P.two_component_eq_of_seven_maximal structural escape natural SY hK hBK hKY
    · exact P.two_component_eq_of_nonquasisimple_maximal structural escape hK hBK hKY hY hq
  exact he ▸ hnK
end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Subgroup Theory.GroupTheory Section02 ChapterA.Section04 Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

/-- The source point residual lies in the faithful local family. Its
intrinsic signalizer module detects movement of the central weight-six point. -/
theorem five_faithful_local
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    P.five ∈ MainForward.faithfulLocalComponents T := by
  have hlocal := P.five_local_family structural
  have hTK : (T : Subgroup G) ≤ normalizer (P.five : Set G) :=
    pointResidual_normalized S.chosen.sylow_normalizes_component P.two_central
  let J := P.five ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  have hKQ : P.five ≤ normalizer (Q : Set G) := le_sup_left.trans
    (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hc : Q = twoSectionCentralizer P.five (T : Subgroup G) := by
    simpa only [inf_of_le_left hTK] using local_normalizer_core_eq_sectionCentralizer hlocal
  have hcore : P.five.pCoreIn 2 ≤ Q :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le P.five.le_normalizer hTK)
  have hcomm : ⁅P.five,Q⁆ ≤ P.five.pCoreIn 2 := by
    rw [hc]
    exact ((le_twoSectionCentralizer_iff _ _ _).mp le_rfl).2.2
  have hZ : omegaCenterIn (T : Subgroup G) ≤ omegaCenterIn Q := by
    have hHe := Chapter1.lemma_1_1_4_6 T (S.hypothesis.simpleQTKE.evenCharacteristic T)
      ⟨hlocal.2.2,show (T : Subgroup G) ≤ J from le_sup_right⟩
    have hQT : Q ≤ (T : Subgroup G) := Setup.NaturalCoordinates.subjoin_core_le_sylow P.five
    intro z hz
    obtain ⟨hzT,hzC,hz2⟩ := (mem_omegaCenterIn_iff _ _).mp hz
    have hzQ := centralizer_le hQT hzC
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hHe ⟨(show (T : Subgroup G) ≤ J from le_sup_right) hzT,hzQ⟩,hzQ,hz2⟩
  apply (mem_faithfulLocalComponents_iff_module T
    (S.hypothesis.simpleQTKE.evenCharacteristic T)).mpr
  refine ⟨hlocal,?_⟩
  intro hzero
  have hz : signalizerModule P.five Q = ⊥ :=
    bot_unique ((signalizerModule_le_intrinsicModule P.five Q
      (mem_L_isPPerfect hlocal) hKQ hcore hcomm).trans_eq hzero)
  have hfix : P.five ≤ centralizer (omegaCenterIn Q : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      ((signalizerModule_eq_commutator_omegaCenter P.five Q).symm.trans hz)
  exact P.five_moves_six structural escape
    (hfix.trans (centralizer_le (Set.singleton_subset_iff.mpr (hZ P.six_mem_omega))))

/-- Any maximal overcomponent used in the model sieve is genuinely faithful. -/
theorem five_overgroup_faithful
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) {Y : Subgroup G}
    (hY : Y ∈ Chapter1.LStar G (T : Subgroup G)) (hBY : P.five ≤ Y) :
    FaithfulMaximalLocal T Y := by
  have hf := faithful_local_overgroup T (S.hypothesis.simpleQTKE.evenCharacteristic T)
    (P.five_faithful_local structural escape) hY.1 hBY
  exact ⟨hY,((mem_faithfulLocalComponents_iff T Y).mp hf).2⟩

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
