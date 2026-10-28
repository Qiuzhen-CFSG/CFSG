module
public import CFSG.Quasithin.Chapter10.SourceElementCentralizerComponent
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupTheory.CComponent.PrimeGroupOvergroup
/-!
# The characteristic-two entry to the constrained point-centralizer branch

The original moved module W=[V,L] is elementary and fully moved by L.
A.1.26 therefore makes W centralize the odd core of C_G(v). If C_G(W)≤M,
that odd core is a normal odd subgroup of C_M(v), which has characteristic
two by1.1.3. Thus the entire point centralizer has trivial odd core.
C-component calculus now makes I C_T(v) characteristic two whenever the
containing component I is not quasisimple. These are the actual inputs to
B.2.14 in source10.2.9; no reduced-module or FF classification is assumed.
Source: Aschbacher–Smith10.2.9, printed p.751.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    D.simpleQTKE T D.maximal

/-- The odd core of the full point centralizer vanishes once the original
moved factor has controlled centralizer. -/
theorem source_a5_point_centralizer_oddCore_eq_bot
    {v : G} (hv : v ∈ D.fullModule) (hvne : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal) :
    pPrimeCore 2 (centralizer ({v} : Set G)) = ⊥ := by
  let H := centralizer ({v} : Set G)
  let W := ⁅D.fullModule,L⁆
  let O := (pPrimeCore 2 H).map H.subtype
  let K := D.maximalLocal ⊓ H
  have hLH : L ≤ H := fun l hl => mem_centralizer_singleton_iff.mpr (hvL l hl)
  have hWH : W ≤ H := (source_full_moved_le_component D).trans hLH
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 (W.subgroupOf H) := IsElementaryAbelian.subgroupOf hWH
  have hv2 : orderOf v = 2 := by
    let := D.fullModule_elementary (uniqueness D)
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian v hv) hvne
  have hcomm : ⁅W.subgroupOf H,L.subgroupOf H⁆ = W.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le hLH]
    exact source_full_moved_eq_commutator D
  have hperfect : IsPPerfect 2 (L.subgroupOf H) :=
    D.faithful.1.2.1.of_surjective (subgroupOfEquivOfLe hLH).symm.toMonoidHom
      (subgroupOfEquivOfLe hLH).symm.surjective
  have hc := ChapterA.lemma_A_1_26_1_of_stronglyQuasithin
    (D.simpleQTKE.involution_centralizer_sqtk hv2).stronglyQuasithin
    (L.subgroupOf H) (W.subgroupOf H) hperfect hcomm
  have hm := congrArg (Subgroup.map H.subtype) hc
  have hWO : ⁅W,O⁆ = ⊥ := by
    simpa only [map_commutator,map_subgroupOf_eq_of_le hWH,Subgroup.map_bot] using hm
  have hOM : O ≤ D.maximalLocal :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hWO)).trans hCW
  have hOH : O ≤ H := map_subtype_le _
  have hOK : O ≤ K := le_inf hOM hOH
  have hHO : H ≤ normalizer (O : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pPrimeCore 2 H).le_normalizer_map H.subtype
  let : (O.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer (inf_le_right.trans hHO)
  have hcop : Nat.Coprime 2 (Nat.card (O.subgroupOf K)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hOK).toEquiv,
      show Nat.card O = Nat.card (pPrimeCore 2 H) from card_map_of_injective H.subtype_injective]
    exact pPrimeCore_coprime_card
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hM : D.maximalLocal ∈ Chapter1.He G :=
    (inf_centralizer_pCoreIn_le_iff 2 D.maximalLocal).mpr
      (D.simpleQTKE.evenCharacteristic T D.maximalLocal
        (uniqueness D).normalizer_maximal hTM)
  have hvT : v ∈ (T : Subgroup G) := D.fullModule_le_sylow (uniqueness D) hv
  have hK : K ∈ Chapter1.He G := by
    change K ⊓ centralizer (K.pCoreIn 2 : Set G) ≤ K.pCoreIn 2
    have hh := pCoreIn_selfCentralizing_centralizer hM
      (T.isPGroup'.to_le (zpowers_le.mpr hvT))
      (zpowers_le.mpr (hTM hvT))
    simpa only [zpowers_eq_closure,centralizer_closure] using hh
  have hO0 : pPrimeCore 2 K = ⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    ((inf_centralizer_pCoreIn_le_iff 2 K).mp hK)
  have hsub : O.subgroupOf K = ⊥ :=
    (pPrimeCore_eq_bot_iff.mp hO0) (O.subgroupOf K) inferInstance hcop
  have he : O = ⊥ := by
    have hh := congrArg (Subgroup.map K.subtype) hsub
    simpa only [map_subgroupOf_eq_of_le hOK,Subgroup.map_bot] using hh
  exact (map_eq_bot_iff_of_injective _ H.subtype_injective).mp he

/-- A nonquasisimple containing component has a characteristic-two join
with the prescribed point-centralizer Sylow subgroup. -/
theorem source_a5_point_component_characteristicTwo
    {v : G} (hv : v ∈ D.fullModule) (hvne : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (I : Subgroup G) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hnot : ¬ IsQuasisimple I) :
    generalizedFitting (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Subgroup G) =
      pCore 2 (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Subgroup G) := by
  let H := centralizer ({v} : Set G)
  let S := (T : Subgroup G) ⊓ H
  let J := I ⊔ S
  have hSH : S ≤ H := inf_le_right
  have hp : IsPGroup 2 (S.subgroupOf H) := (T.isPGroup'.to_le inf_le_left).comap_subtype
  have ho : pPrimeCore 2 H = ⊥ := source_a5_point_centralizer_oddCore_eq_bot D hv hvne hvL hCW
  rcases hI.component_or_generalizedFitting_sup_eq_pCore hp ho with hc | hc
  · let := hc.2
    exact (hnot (IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hIX))).elim
  · rw [←subgroupOf_sup hIX hSH] at hc
    let e := subgroupOfEquivOfLe (sup_le hIX hSH)
    have hh := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [map_generalizedFitting_equiv,pCore_map_iso] at hh
    exact hh
end CFSG.Quasithin.Chapter10
