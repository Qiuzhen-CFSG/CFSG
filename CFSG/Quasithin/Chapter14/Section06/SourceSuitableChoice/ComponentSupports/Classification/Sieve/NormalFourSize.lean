module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.NormalFourSupport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.LocalStructure
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.Local
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.NormalTypes
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.SingleLinearThree
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# The original normal field-four core and the mixed size obstruction

For J=KT and W=[⟨V^J⟩,K], the preceding marked duality gives
|W|=32 and |Q:C_Q(W)|=16, where Q=O₂(J). Since W is abelian
and lies in Q, it lies in C_Q(W). Thus |Q|≥512. The original
A₅ or S₅ core quotient then forces |T|≥2048.

The literal pair (K,Y S₂,T), with Y the original source residual and
S₂=O₂(Y)(T∩K), satisfies every premise of the shared mixed F.1.12
size contract. In particular the cubic quotient, actual Sylow placement
in the generated group, whole Borel, and first parabolic J are retained.
Its upper bound |T|≤256 excludes the normal field-four component.
Combining this with the completed remaining sieve and both paired-component
exclusions gives the actual L₃(2)/A₆ catalogue, diagram action, uniqueness
of the component and Mc=KT with O²(Mc)=Mc∞.

The final exclusion and catalogue are conditional on `MixedSizeInput`,
whose source proof belongs to `qt-d-tensor-mixed-size-bound`; that task
is blocked on mixed Borel recognition. No recognition is asserted here.
The full A₆ supports, markings and same-vector suitability construction
are supplied by `Modules/Recognition/AlternatingSixFullSupports.lean`;
`TerminalSupports.lean` assembles the remaining component branch. Final
instantiation of the mixed-size input belongs to `qt-e-suitable-existence`.
Original 14.6.18 is the explicit hsolv premise, owned by `qt-e-14625-source`.

Source: Aschbacher--Smith 14.6.20--23, printed pp.1037--1038, using
14.3.6(1), 14.2.16 and F.1.12(I), printed pp.991,986,262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Modules.Recognition
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv


/-- The support and its dual are two separate sections of the original core. -/
theorem source_normal_four_core_card
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    512 ≤ Nat.card (pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) := by
  let J := K ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) J
  let W := ⁅U,K⁆
  let Q := J.pCoreIn 2
  let C := Q ⊓ centralizer (W : Set G)
  have hKJ : K ≤ J := le_sup_left
  have hJH : J ≤ H := sup_le hKH hH.1.2
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  have hJ := (source_normal_four_join_minimal hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hm).1
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab J hJ
  let : IsElementaryAbelian 2 U :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hp := source_component_support_placement hG T hempty hM hunique hmany hcard e hab hsolv
    J hJ K hKJ hc
  have hWU : W ≤ U := hp.2.1.trans inf_le_left
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWU
  have hWC : W ≤ C := le_inf (hWU.trans h.UH_le_QH)
    (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  obtain ⟨eK,f,d,sQ,hker,hf,hWcard,hWK,hWfix,hcomm,hindex,hpair⟩ :=
    source_normal_four_core_duality hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn hm
  have hCcard : 32 ≤ Nat.card C := by
    rw [←hWcard]
    exact Nat.card_le_card_of_injective (inclusion hWC) (inclusion_injective hWC)
  have hind : C.relIndex Q = 16 := by
    rw [show C = centralizer (W : Set G) ⊓ Q from inf_comm _ _,inf_relIndex_right]
    exact hindex
  have hcount := relIndex_mul_card_of_le (show C ≤ Q from inf_le_left)
  rw [hind] at hcount
  have hQcard : 512 ≤ Nat.card Q := by omega
  simpa only [Q,pCoreIn,card_map_of_injective J.subtype_injective] using hQcard

/-- All hypotheses of the shared mixed F.1.12 size theorem on the literal pair. -/
theorem source_normal_four_mixed_hypotheses
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    let Y := sourceResidual M Mc
    let S₂ := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
    let A := Y ⊔ S₂
    ChapterF.Source.HypothesisF11 ![K,A] (T : Subgroup G) ∧
      IsQuasithin (ChapterF.Source.generated ![K,A] (T : Subgroup G)) ∧
      Chapter1.IsSylowIn 2 (T : Subgroup G)
        (ChapterF.Source.generated ![K,A] (T : Subgroup G)) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) ∧
      ChapterF.Source.borel A (T : Subgroup G) ≤ normalizer (T : Set G) ∧
      ChapterF.Source.parabolic ![K,A] (T : Subgroup G) 0 = K ⊔ (T : Subgroup G) := by
  dsimp only
  let J := K ⊔ (T : Subgroup G)
  let Y := sourceResidual M Mc
  let R := Y.pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ K)
  let A := Y ⊔ R
  have hKJ : K ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJH : J ≤ H := sup_le hKH hH.1.2
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  let : (K.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))
  have hgen : K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hKJ hTJ]
    exact subgroupOf_self J
  have hres := source_twoResidual_eq_normal_cComponent T J hTJ (K.subgroupOf J) hc
    inferInstance hgen
  have hmap : (K.subgroupOf J).map J.subtype = K := map_subgroupOf_eq_of_le hKJ
  obtain ⟨eK,f,hker,hr,hf,hstar,_,hF,hmove,hBK,hBA⟩ :=
    source_normal_four_marked_amalgam hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn hm
  let a := subgroupOfEquivOfLe hKJ
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hq : ChapterF.Source.IsRankOneModel ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J)) :=
    .linear 2 (by decide) (by simpa using hm.of_mulEquiv aq)
  obtain ⟨hS,_,hR,_⟩ := Section02.source_normal_amalgam_core
    hG T hempty hM hunique hmany hcard e J hstar (K.subgroupOf J) hgen
  have hRT : R ≤ (T : Subgroup G) := by
    simpa only [hmap] using hR.trans_eq hS
  have hnot : ¬Y ≤ normalizer (R : Set G) := by
    simpa only [hmap] using Section02.source_normal_amalgam_not_normalizes
      hG T hempty hM hunique hmany hcard e J hstar (K.subgroupOf J) hgen hres hq
  obtain ⟨_,eA⟩ := Section02.source_residual_actor_movement
    hG T hempty hM hunique hmany hcard e R hRT le_sup_left hnot
  have ht : (T : Subgroup G) ≤ ChapterF.Source.generated ![K,A] (T : Subgroup G) := le_sup_right
  refine ⟨hF,hG.quasithin.subgroup _,⟨T.subtype ht,map_subgroupOf_eq_of_le ht⟩,
    ⟨eK⟩,eA,?_,?_⟩
  · exact hF.cubic_borel_normalizes_S 1 eA.some
  · change K ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel A (T : Subgroup G) = J
    rw [hBA,sup_eq_left.mpr (hRT.trans le_sup_right)]

/-- Both possible original quotient actions force the ambient Sylow to have order at least 2048. -/
theorem source_normal_four_sylow_card
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    2048 ≤ Nat.card T := by
  obtain ⟨hF,_,_,eK,eA,_,hp⟩ := source_normal_four_mixed_hypotheses
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hm
  have hlo := source_normal_four_core_card
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hm
  have hc := hF.mixed_first_core_size_cases eK.some eA.some
  rw [hp] at hc
  rcases hc with hc | hc <;> omega

/-- The original normal field-four case is excluded once the independently
owned mixed F.1.12 size theorem is supplied. -/
theorem source_normal_four_false_of_mixed_size
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) : False := by
  obtain ⟨hF,hqt,hsyl,eK,eA,hB,_⟩ := source_normal_four_mixed_hypotheses
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hm
  have hu := size _ _ (T : Subgroup G) hF hqt hsyl eK eA hB
  have hl := source_normal_four_sylow_card
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hm
  omega

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Modules.Recognition
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv



open Classification Classification.Sieve

/-- The mixed size theorem completes the original catalogue and excludes both
paired alternatives. The remaining A₆ supports are not assumed here. -/
theorem terminal_component_catalogue_of_mixed_size
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    ComponentQuotientModels K ∧ ComponentModelDiagram T K ∧
      (K.subgroupOf Mc).Normal ∧
      (solvableResidual Mc).map Mc.subtype = K ∧
      K ⊔ (T : Subgroup G) = Mc ∧
      (∀ C : Subgroup G, C ≤ Mc → (C.subgroupOf Mc).IsCComponent → C = K) ∧
      solvableResidual Mc = pResidual 2 Mc := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hmodels (C : Subgroup G) (hCM : C ≤ Mc) (hC : (C.subgroupOf Mc).IsCComponent) :
      ComponentQuotientModels C := by
    rcases source_component_four_or_terminal_models
        hG T hempty hM hunique hmany hcard e hab hsolv Mc hout C hCM hC with
      ⟨hn,hm⟩ | hm
    · exact (source_normal_four_false_of_mixed_size
        hG T hempty hM hunique hmany hcard e hab hsolv size Mc hout C hCM hC hn hm).elim
    · exact hm
  have hr := terminal_residual_eq_component_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv hmodels K hKM hK
  obtain ⟨hn,hgen⟩ := terminal_single_component_generated
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr (hmodels K hKM hK)
  refine ⟨hmodels K hKM hK,source_component_diagram_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK (hmodels K hKM hK),
    hn,hr,hgen,?_,?_⟩
  · intro C hCM hC
    exact (terminal_residual_eq_component_of_models
      hG T hempty hM hunique hmany hcard e hab hsolv hmodels C hCM hC).symm.trans hr
  · exact (terminal_residual_structure_of_component_models
      hG T hempty hM hunique hmany hcard e hab hsolv hmodels).1

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
