module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.LocalFamily
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# An elementary-factor witness for the component dichotomy

The elementary factor itself supplies the existential commutator witness in
1.2.11. Its marked point block is perfect and acts irreducibly and nontrivially,
so the factor is its own commutator with the residual of its normalizer in the
marked centralizer. This uses the literal marked block and centralizer.
The index-two local-family argument then supplies an actual containing C-component.

Source: Aschbacher--Smith, 14.3.20, pp.997--998; 1.2.5 and 1.2.11(a).
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition BinaryPermutation.SixNaturalSplit
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

namespace MarkedPoint
variable {T : Sylow 2 G} {V L A : Subgroup G} {F : InvariantFlag T V 2}
variable (P : MarkedPoint F L A)

theorem factor_residual_commutator [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16) :
    ⁅A, (pResidual 2 (P.globalCentralizer ⊓ normalizer (A : Set G) : Subgroup G)).map
      (P.globalCentralizer ⊓ normalizer (A : Set G)).subtype⁆ = A := by
  let B := P.blockCentralizer
  let X := P.globalCentralizer ⊓ normalizer (A : Set G)
  have hBX : B ≤ X := le_inf inf_le_right P.blockCentralizer_normalizes_factor
  have hcomm : ⁅A, B⁆ = A := by
    rcases pointBlock_invariant_factor (factorBlock F L A) A ⁅A,B⁆ P.marking
      P.factor_map P.factor_le P.point P.point_action
      (le_normalizer_iff_commutator_le_left.mp P.blockCentralizer_normalizes_factor)
      (normalizer_commutator_ge_right A B) with hb | he
    · have hAC : A ≤ centralizer (B : Set G) :=
        commutator_eq_bot_iff_le_centralizer.mp hb
      have he := pointBlock_factor_centralizer (factorBlock F L A) A hcard P.marking
        P.factor_map P.factor_le P.point P.point_action
      change A ⊓ centralizer (B : Set G) = ⊥ at he
      rw [inf_of_le_left hAC] at he
      have hc1 : Nat.card A = 1 := Subgroup.card_eq_one.mpr he
      omega
    · exact he
  let : Group.IsPerfect B := pointBlock_isPerfect (factorBlock F L A) A hcard
    P.marking P.factor_map P.factor_le P.point P.point_action P.factor_le_blockCentralizer
  let : Group.IsPerfect (B.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hBX).symm.toMonoidHom)
      (subgroupOfEquivOfLe hBX).symm.surjective
  have hp : IsPPerfect 2 (B.subgroupOf X) := by
    intro N hN hq
    let := hN
    by_contra hn
    let : Nontrivial ((B.subgroupOf X) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
    let : Group.IsPerfect ((B.subgroupOf X) ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent ((B.subgroupOf X) ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((B.subgroupOf X) ⧸ N) inferInstance
  have hBR : B ≤ (pResidual 2 X).map X.subtype := by
    have hh := map_mono (f := X.subtype) (le_pResidual_of_isPPerfect (B.subgroupOf X) hp)
    rwa [map_subgroupOf_eq_of_le hBX] at hh
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans inf_le_right)
  · exact hcomm.ge.trans (commutator_mono le_rfl hBR)

/-- The source Chapter 1 applications, retaining the specified z throughout. -/
theorem classifiedComponent_of_factor_witness
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16) (hVA : V ≤ A) (hVT : V ≤ (T : Subgroup G))
    (z : G) (hz : F.Vi 1 = zpowers z)
    (hSylow : Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer)
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element)
    (hcontaining : ∃ B : Subgroup G, B ∈ Chapter1.cComponentsIn P.globalCentralizer ∧
      P.blockCentralizer ≤ B) : P.ClassifiedComponent z := by
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← hz]
    simpa using F.card 1 (by decide)
  have hzmem : z ∈ F.Vi 1 := hz.symm ▸ mem_zpowers z
  have hzT : z ∈ (T : Subgroup G) := hVT (F.le_seed 1 hzmem)
  have hzB0 : z ∈ P.blockCentralizer := P.factor_le_blockCentralizer (hVA (F.le_seed 1 hzmem))
  have hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t := by
    intro t ht
    exact (normalizer_le_centralizer_of_card_two (F.Vi 1)
      (by simpa using F.card 1 (by decide)) (F.invariant 1 ht) z hzmem).symm
  have hlocal : P.globalCentralizer ∈ Chapter1.H G := by
    change P.globalCentralizer.pCoreIn 2 ≠ ⊥
    rw [hcore]
    exact zpowers_ne_bot.mpr (by intro he; simpa [he] using P.point_order)
  obtain ⟨B, hB, hKB⟩ := hcontaining
  have hq : IsQuasisimple B :=
    (Chapter1.lemma_1_2_11_involution hG T P.globalCentralizer B z hlocal hSylow hB
      hz2 (hKB hzB0) ⟨hzT, hzB0.2⟩ hzc
      ⟨A, P.factor_le_blockCentralizer.trans inf_le_right,
        inferInstance, (P.factor_residual_commutator hcard).symm ▸
          hVA (F.le_seed 1 hzmem)⟩ (by
        rw [hcore, zpowers_eq_closure, centralizer_closure])).resolve_right
      (P.not_characteristicTwo_of_core_eq hcore)
  let := hq
  have hcomponent : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer) :=
    ⟨hB.2.subnormal, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hB.1).symm⟩
  obtain ⟨S, hS⟩ := hSylow
  obtain ⟨M₁, hCM₁, hM₁⟩ :=
    Finite.exists_le_maximal (isTwoLocal_involution_centralizer hz2)
  have hdne : zpowers P.element ≠ ⊥ :=
    zpowers_ne_bot.mpr (by intro he; simpa [he] using P.point_order)
  have hdgroup : IsPGroup 2 (zpowers P.element) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, P.point_order]; decide)
  have hdC : zpowers P.element ≤ P.globalCentralizer :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCC : centralizer (zpowers P.element : Set G) = P.globalCentralizer := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hCN : P.globalCentralizer ≤ normalizer (zpowers P.element : Set G) :=
    hCC ▸ _root_.centralizer_le_normalizer _
  have h115 : Chapter1.Lemma115Hypotheses P.globalCentralizer S M₁ z := by
    apply Chapter1.lemma_1_1_6 hdne hdgroup hdC hCC.le hCN S T
      (hS.le.trans inf_le_left) hz2 hzT hzc hM₁ hCM₁
    intro N hN hTN
    exact Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T N hN hTN)
  have hmodel := Chapter1.lemma_1_1_5_three_knownSimple hG P.globalCentralizer S M₁ z h115
    (B.subgroupOf P.globalCentralizer) hcomponent
  refine ⟨B, hB.1, hKB, hcomponent, ?_, hmodel.2.2⟩
  simpa only [map_subgroupOf_eq_of_le hB.1] using hmodel.1

end MarkedPoint
theorem source_containing_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    {A : Subgroup G} (hA : ElementaryFactor F (sourceResidual M Mc) A)
    (hlt : A < centralizer (A : Set G))
    (P : MarkedPoint F (sourceResidual M Mc) A) (z : G) (hz : F.Vi 1 = zpowers z)
    (hgeom : P.FourCenterGeometry z)
    (hSylow : Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer) :
    ∃ B : Subgroup G, B ∈ Chapter1.cComponentsIn P.globalCentralizer ∧
      P.blockCentralizer ≤ B := by
  have hlocal := localFamilySource_of_source_hypotheses hG T hempty hM hu hmany hcard e
    hnot F hne g hgP hgH hs
  have hcore := source_global_core_eq hG T hempty hM hu hmany hcard e hnot F hne
    g hgP hgH hs A hA hlt P z hz hSylow
  have hS := source_localSylow_comparison hG T hempty hM hu hmany hcard e hnot F hne
    g hgP hgH hs P
  have hR : P.localSylow ≤ P.globalCentralizer := inf_le_right
  have hB : P.blockCentralizer ≤ P.globalCentralizer := inf_le_right
  have hl := (Chapter1.mem_LIn_iff_subgroupOf hR hB).mp
    ⟨hB,hlocal A hA hlt P z hz hgeom hSylow⟩
  obtain ⟨S,hSmap⟩ := hSylow
  have hRS : P.localSylow.subgroupOf P.globalCentralizer ≤ (S : Subgroup P.globalCentralizer) := by
    have hh := comap_mono (f := P.globalCentralizer.subtype) hS.1
    rw [← hSmap,comap_map_eq_self_of_injective P.globalCentralizer.subtype_injective] at hh
    exact hh
  have hi : (P.localSylow.subgroupOf P.globalCentralizer).relIndex
      (S : Subgroup P.globalCentralizer) ≤ 2 := by
    rw [← relIndex_map_map_of_injective _ _ P.globalCentralizer.subtype_injective,
      map_subgroupOf_eq_of_le hR,hSmap]
    exact hS.2
  have hH : P.globalCentralizer ∈ Chapter1.H G := by
    change P.globalCentralizer.pCoreIn 2 ≠ ⊥
    rw [hcore]
    exact zpowers_ne_bot.mpr (by intro he; simpa [he] using P.point_order)
  obtain ⟨B,hBcomp,_⟩ := Chapter1.Section02.index_le_two_local_component_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hH) S hRS hi hl
  refine ⟨B.map P.globalCentralizer.subtype,⟨map_subtype_le _,?_⟩,?_⟩
  · change ((B.map P.globalCentralizer.subtype).comap P.globalCentralizer.subtype).IsCComponent
    rw [comap_map_eq_self_of_injective P.globalCentralizer.subtype_injective]
    exact hBcomp.1
  · have hh := map_mono (f := P.globalCentralizer.subtype) hBcomp.2
    rwa [map_subgroupOf_eq_of_le hB] at hh


end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
