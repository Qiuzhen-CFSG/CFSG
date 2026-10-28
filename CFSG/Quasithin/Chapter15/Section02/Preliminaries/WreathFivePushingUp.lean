module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveOvercomponent
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveNormality
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction

/-!
# The original marked-five pushing-up setup

For the original residual Y and S=N_T(K), let W=⟨YRc,K,S⟩ and
M₁=W∩M. When O₂(W) is nontrivial, the proved source Sylow argument
makes S Sylow in M₁. The marked-five normality theorem supplies Y normal
in M₁. A.4.2 then makes R=O₂(YS) a maximal Y-signalizer in M₁ and a
Sylow subgroup of its M₁-normal closure.

Since T normalizes both Y and its index-two subgroup S, YT normalizes R.
The actual source uniqueness M=!M(YT) controls every characteristic
normalizer of R. Restricting this control to W proves radicality in W
and completes the literal C.2.3 hypotheses. SQTK(W) follows from its
nontrivial two-core; no characteristic-two conclusion for W is required.
The final source wrapper retains the same wreath component and the already
proved normal overcomponent. The later C.2.5/C.2.7 comparison is separate.

Source: Aschbacher--Smith, original 15.2.4, printed p.1106;
C.2.3, p.144; A.4.2(5),(7), p.57.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Chapter1 ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

private theorem pushingUp_of_normal
    {κ : GroupClass} {Y S W M : Subgroup G}
    (hY : IsPPerfect 2 Y) (hYM : Y ≤ M) (hMY : M ≤ normalizer (Y : Set G))
    (hS : IsSylowIn 2 S M) (hMW : M ≤ W) (hW : IsSQTK κ W)
    (hne : (Y ⊔ S).pCoreIn 2 ≠ ⊥)
    (hcontrol : (((Y ⊔ S).pCoreIn 2).subgroupOf W).characteristicNormalizerClosure ≤
      M.subgroupOf W) :
    RadicalExclusions.PushingUpSetup κ W ((Y ⊔ S).pCoreIn 2) M := by
  let R := (Y ⊔ S).pCoreIn 2
  have hSM := (isSylowIn_iff.mp hS).2.1
  have hRM : R ≤ M := (pCoreIn_le 2 (Y ⊔ S)).trans (sup_le hYM hSM)
  have hRW : R ≤ W := hRM.trans hMW
  have hYW : Y ≤ W := hYM.trans hMW
  obtain ⟨P,hP⟩ := hS
  have hmax : IsMaximalTwoSignalizer Y M R := by
    simpa only [hP] using normal_sylow_core_isMaximal Y M hYM hMY hY P
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp hmax
  have hn : (Y.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMY
  have hRC := signalizer_le_twoSectionCentralizer Y M R hYM hn.isSubnormal hY hm.1
  have hsyl : IsSylowIn 2 R (twoSectionCentralizer Y M) :=
    (maximal_signalizer_iff_sylow Y M R hYM hn.isSubnormal hY).mp hmax
  have hN : W ⊓ normalizer (R : Set G) ≤ M := by
    have hne' : R.subgroupOf W ≠ ⊥ := by
      intro hb
      apply hne
      simpa only [map_subgroupOf_eq_of_le hRW,Subgroup.map_bot] using congrArg (map W.subtype) hb
    intro x hx
    change (⟨x,hx.1⟩ : W) ∈ M.subgroupOf W
    apply hcontrol
    apply normalizer_le_characteristicNormalizerClosure_self (R.subgroupOf W) hne'
    rw [←subgroupOf_normalizer_eq hRW]
    exact hx.2
  let N := W ⊓ normalizer (R : Set G)
  have hRN : R ≤ N := le_inf hRW R.le_normalizer
  have hYN : Y ≤ N := le_inf hYW hm.1.normalizes
  have hRB : R ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes hm.1.isPGroup hRN inf_le_right
  have hBN : Y ≤ normalizer (N.pCoreIn 2 : Set G) := hYN.trans
    (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
  have he : N.pCoreIn 2 = R := le_antisymm
    (hm.2 _ ((isTwoSignalizer_iff _ _ _).mpr
      ⟨(pCoreIn_le 2 N).trans hN,isPGroup_pCoreIn 2 N,hBN⟩) hRB) hRB
  refine ⟨hW,hRW,hMW,?_,hcontrol,?_⟩
  · refine ⟨?_,?_⟩
    · intro hb
      change R.subgroupOf W = ⊥ at hb
      apply hne
      simpa only [map_subgroupOf_eq_of_le hRW,Subgroup.map_bot] using congrArg (map W.subtype) hb
    · apply map_injective W.subtype_injective
      change ((normalizer (R.subgroupOf W : Set W)).pCoreIn 2).map W.subtype =
        (R.subgroupOf W).map W.subtype
      rw [map_pCoreIn_of_injective 2 _ W.subtype W.subtype_injective,
        ←subgroupOf_normalizer_eq hRW,subgroupOf_map_subtype]
      simpa only [inf_comm,map_subgroupOf_eq_of_le hRW] using he
  · apply hsyl.restrict
    · have hr := map_mono (f := M.subtype) (le_normalClosure (H := R.subgroupOf M))
      simpa only [map_subgroupOf_eq_of_le hRM] using hr
    · let C := twoSectionCentralizer Y M
      let : (C.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
        (twoSectionCentralizer_normalized Y M hMY)
      exact (map_le_iff_le_comap).mpr (normalClosure_le_normal (N := C.subgroupOf M)
        (fun _ hr => hRC hr))
open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

private theorem residual_notation (K : Subgroup G) :
    twoResidualAmbient K = (pResidual 2 K).map K.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hn⟩
    exact ⟨hN,IsPGroup.iff_card.mp hn⟩

private theorem residual_perfect (T : Sylow 2 G) (M M₀ Mc : Subgroup G) :
    IsPPerfect 2 (caseIIResidual T M M₀ Mc) := by
  change IsPPerfect 2 (twoResidualAmbient (conjugateSpanBy ((M ⊓ Mc).pCoreIn 2)
    (twoResidualAmbient M₀ ⊔ (T : Subgroup G))))
  rw [residual_notation]
  exact isPPerfect_embedded_pResidual 2 _

/-- The literal nontrivial-core marked-five group satisfies C.2.3. -/
public theorem source_dihedral_five_pushingUp_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V K : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2) (hout : ¬ K ≤ M)
    (hi : ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2)
    (hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) ⊓ normalizer (K : Set G)) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
    pCore 2 W ≠ ⊥ →
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W
      ((Y ⊔ S).pCoreIn 2) (W ⊓ M) := by
  intro Y S W hcore
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hnormal : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_dihedral_five_residual_normal T hM.1.2 hu hV l hd)
  have hYW : Y ≤ W := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hSW : S ≤ W := le_sup_right
  have hSM : S ≤ M := inf_le_left.trans hM.1.2
  have hSyl := source_dihedral_five_nontrivial_core_sylow
    hG T hempty hM hJ hu hmany hV l hd hout hi hJS hcore
  have hSylM : Chapter1.IsSylowIn 2 S (W ⊓ M) :=
    hSyl.restrict (le_inf hSW hSM) inf_le_left
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hVY : V ≤ Y :=
    (source_dihedral_five_residual_core_normalizer hG T hempty hM hJ hu hmany hV l hp hd).1.trans
      (pCoreIn_le 2 Y)
  have hVR : V ≤ (Y ⊔ S).pCoreIn 2 := le_pCoreIn_of_normalizes hV.elementary.isPGroup
    (hVY.trans le_sup_left) ((sup_le hYM hSM).trans hV.normalized)
  have hne : (Y ⊔ S).pCoreIn 2 ≠ ⊥ :=
    fun hb => hV.nontrivial (bot_unique (hVR.trans hb.le))
  have hTN : (T : Subgroup G) ≤ normalizer (S : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (show S ≤ (T : Subgroup G) from inf_le_left)).mp
    exact normal_of_index_eq_two hi
  have hTjoin : (T : Subgroup G) ≤ normalizer ((Y ⊔ S : Subgroup G) : Set G) :=
    (le_inf (hM.1.2.trans hnormal) hTN).trans (normalizer_inf_normalizer_le_normalizer_sup Y S)
  have huY := source_dihedral_five_residual_sylow_unique hG T hempty hM hJ hu hmany hV l hp hd
  have hctrl : ((Y ⊔ S).pCoreIn 2).characteristicNormalizerClosure ≤ M := by
    apply characteristicNormalizerClosure_le_of_unique_maximalTwoLocal
      (J := Y ⊔ (T : Subgroup G)) (fun N hN hYN => ?_) (isPGroup_pCoreIn 2 (Y ⊔ S))
    · exact (sup_le (le_sup_left.trans (Y ⊔ S).le_normalizer) hTjoin).trans
        (normalizer_le_normalizer_characteristic_image (Y ⊔ S) (pCore 2 (Y ⊔ S : Subgroup G)))
    · have hm : N ∈ maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) := ⟨hN,hYN⟩
      rw [huY] at hm
      exact hm
  have hWH : W ∈ Chapter1.H G :=
    fun hb => hcore ((map_eq_bot_iff_of_injective _ W.subtype_injective).mp hb)
  have hctrlW := characteristicNormalizerClosure_subgroupOf_le
    ((pCoreIn_le 2 (Y ⊔ S)).trans (sup_le hYW hSW)) hctrl
  have he : M.subgroupOf W = (W ⊓ M).subgroupOf W := by
    ext x
    exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩
  rw [he] at hctrlW
  exact pushingUp_of_normal (residual_perfect T M _ Mc) (le_inf hYW hYM)
    (inf_le_right.trans hnormal) hSylM inf_le_left
    (Chapter1.RadicalExclusions.sqtk_of_mem_H hG hWH) hne hctrlW


/-- The actual chosen H-star wreath configuration supplies C.2.3 and the normal
source overcomponent on the same K and S, in every nontrivial-core branch. -/
public theorem source_HStar_wreath_five_pushingUp_configuration
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (pCore 2 W ≠ ⊥ →
        Chapter1.IsSylowIn 2 S W ∧
        Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W
          ((Y ⊔ S).pCoreIn 2) (W ⊓ M) ∧
        ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn W ∧ K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
          W ≤ normalizer (L₁ : Set G) ∧ W = L₁ ⊔ (W ⊓ M)) := by
  obtain ⟨l,K,hd,hK,heK,_,hout,hi,hJS,_⟩ :=
    source_HStar_wreath_five_configuration_with_Rc_le_S
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore
  have hc := source_dihedral_five_nontrivial_core_component
    hG T hempty hM hJ hu hmany hV l hd hH.1.1.2 hK hout hi hJS hcore
  exact ⟨hc.1,source_dihedral_five_pushingUp_setup
    hG T hempty hM hJ hu hmany hV l hd hout hi hJS hcore,hc.2⟩

end CFSG.Quasithin.Chapter15.Section02
