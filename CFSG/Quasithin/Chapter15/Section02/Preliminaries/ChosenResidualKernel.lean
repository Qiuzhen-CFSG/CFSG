module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenResidualNormalizer
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.GroupTheory.TwoLocalUniquenessControl.NormalSubgroups
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import CFSG.Quasithin.Chapter15.Section01.MinimalParabolicSource

/-!
# Residual normalizer control and the actual outside-parabolic kernels

The literal Case-II residual centralizes C_M(V) in M/O₂(M). If a
T-invariant two-perfect subgroup X lies in C_M(V), the quotient kernel
O₂(M) normalizes X. Recovering X as the two-residual of XO₂(M) lifts this
to normalization by Y. Once the original YT has unique maximal overgroup M,
characteristic-two inheritance in XYT puts the full N_G(X) inside M.

For an outside minimal parabolic H, apply this to the two-residual of a
normal subgroup contained in H∩M. It must be trivial, so that normal
subgroup lies in O₂(H). Consequently every nontrivial quotient of H with
trivial two-core has exactly O₂(H) as kernel. This is the kernel step in
15.2.8; the marked-five consumer discharges the retained YT uniqueness.

Source: Aschbacher--Smith 15.2.3(5), 15.2.7 and the opening of 15.2.8,
printed pp.1105 and 1109--1110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Original Y normalizes every T-invariant two-perfect subgroup of C_M(V). -/
theorem source_chosen_residual_normalizes_twoPerfect (T : Sylow 2 G)
    {M Mc V X : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hXM : X ≤ M ⊓ centralizer (V : Set G))
    (hX : IsPPerfect 2 X) (hTX : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ≤
      normalizer (X : Set G) := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let q := QuotientGroup.mk' (pCore 2 M)
  let A := X.subgroupOf M
  have hXM' : X ≤ M := hXM.trans inf_le_left
  have hYM : Y ≤ M := source_caseIIResidual_le T hTM (map_subtype_le _)
  have hA : IsPPerfect 2 A := hX.of_surjective
    (subgroupOfEquivOfLe hXM').symm.toMonoidHom (subgroupOfEquivOfLe hXM').symm.surjective
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hnorm : q.ker ≤ normalizer (A : Set M) := by
    rw [QuotientGroup.ker_mk', ←subgroupOf_normalizer_eq hXM']
    intro x hx
    exact hTX ((pCore_isPGroup.le_sylow_of_normal (T.subtype hTM)) hx)
  have hstar : (Y.subgroupOf M).map q ≤ centralizer (A.map q : Set (M ⧸ pCore 2 M)) :=
    (le_sup_right.trans (source_chosen_lemma_15_2_3_5 T hTM hu hV)).trans
      (centralizer_le (map_mono (comap_mono hXM)))
  have hlocal : Y.subgroupOf M ≤ normalizer (A : Set M) := by
    rw [←comap_normalizer_map_of_pPerfect q A hA hq hnorm]
    exact map_le_iff_le_comap.mp (hstar.trans (Subgroup.centralizer_le_normalizer _))
  rw [←subgroupOf_normalizer_eq hXM'] at hlocal
  intro y hy
  exact hlocal (show (⟨y,hYM hy⟩ : M) ∈ Y.subgroupOf M from hy)

/-- The original YT uniqueness supplies the full normalizer bound in 15.2.7. -/
theorem source_chosen_twoPerfect_normalizer_of_residual_unique
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V X : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hunique : maximalTwoLocalOvergroups
      (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
        (T : Subgroup G)) = {M})
    (hXM : X ≤ M ⊓ centralizer (V : Set G))
    (hX : IsPPerfect 2 X) (hne : X ≠ ⊥)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    normalizer (X : Set G) ≤ M := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let J := X ⊔ Y ⊔ (T : Subgroup G)
  have hJM : J ≤ M := sup_le (sup_le (hXM.trans inf_le_left)
    (source_caseIIResidual_le T hM.2 (map_subtype_le _))) hM.2
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJ : centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      (generalizedFitting_eq_pCore_of_sylow_overgroup T J M hTJ hJM
        (hG.evenCharacteristic T M hM.1 hM.2))
  apply normalizer_le_of_characteristic_two_unique hJ _
    (le_sup_left.trans le_sup_left) hne
    (sup_le (sup_le X.le_normalizer (source_chosen_residual_normalizes_twoPerfect T hM.2 hu hV hXM hX hTX)) hTX)
  intro N hN hJN
  exact Set.mem_singleton_iff.mp (hunique ▸
    (show N ∈ maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) from
      ⟨hN,(sup_le (le_sup_right.trans le_sup_left) le_sup_right).trans hJN⟩))

/-- A normal subgroup of the actual H-star lying in M is a two-subgroup. -/
theorem source_HStar_normal_le_core_of_residual_unique
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V H K : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hunique : maximalTwoLocalOvergroups
      (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
        (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G)) (hKM : K ≤ M) :
    K ≤ H.pCoreIn 2 := by
  let X := (pResidual 2 K).map K.subtype
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    hH.1.1.2.trans (hHK.trans (normalizer_le_normalizer_characteristic_image K (pResidual 2 K)))
  have hXM : X ≤ M ⊓ centralizer (V : Set G) := le_inf
    ((map_subtype_le _).trans hKM)
    ((embedded_pResidual_mono 2 (le_inf hKH hKM)).trans (hV.intersection_residual H hH))
  have hXbot : X = ⊥ := by
    by_contra hne
    exact hH.1.2 ((hHK.trans (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))).trans
      (source_chosen_twoPerfect_normalizer_of_residual_unique hG T hM hu hV hunique hXM
        (isPPerfect_embedded_pResidual 2 K) hne hTX))
  have hRbot : pResidual 2 K = ⊥ :=
    ((pResidual 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp hXbot
  have hKtwo : IsPGroup 2 K := (isPGroup_quotient_pResidual 2).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hRbot).trans QuotientGroup.quotientBot)
  exact le_pCoreIn_of_normalizes hKtwo hKH hHK

/-- The literal quotient kernel in the opening of 15.2.8 is O₂(H). -/
theorem source_HStar_reduced_kernel_of_residual_unique
    {D : Type*} [Group D] [Finite D]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hunique : maximalTwoLocalOvergroups
      (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
        (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hne : q.ker ≠ ⊤) : q.ker = pCore 2 H := by
  obtain ⟨_,hP,hmax,_,_⟩ := source_centralizing_minimalParabolic hG T hM hJ H hH
  let S := T.subtype hH.1.1.2
  have hker : q.ker ≤ (H ⊓ M).subgroupOf H := by
    rcases normal_le_core_or_sup_eq_top_of_uniqueMaximal
      (M := (H ⊓ M).subgroupOf H) (N := q.ker) hP.1
      ⟨(fun x hx => ⟨x.property,hM.1.2 hx⟩),hmax⟩ with hle | htop
    · exact hle.trans (normalCore_le _)
    · exfalso
      have hm := congrArg (map q) htop
      have ht : (S : Subgroup H).map q = ⊤ := by
        simpa only [Subgroup.map_sup,Subgroup.map_ker_self,sup_bot_eq,
          map_top_of_surjective q hq] using hm
      have hp : IsPGroup 2 (⊤ : Subgroup D) := ht ▸ S.isPGroup'.map q
      have hd : (⊤ : Subgroup D) ≤ pCore 2 D := le_sSup ⟨inferInstance,hp⟩
      rw [hc] at hd
      exact hne (top_unique (fun x _ => mem_bot.mp (hd (mem_top (q x)))))
  have hKM : q.ker.map H.subtype ≤ M := by
    rintro x ⟨y,hy,rfl⟩
    exact (hker hy).2
  have hHK : H ≤ normalizer (q.ker.map H.subtype : Set G) := by
    have hh := q.ker.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hbound := source_HStar_normal_le_core_of_residual_unique hG T hM.1 hu hV hunique hH
    (map_subtype_le q.ker) hHK hKM
  apply le_antisymm
  · exact (map_le_map_iff_of_injective H.subtype_injective).mp hbound
  · have hmap : (pCore 2 H).map q ≤ pCore 2 D :=
      le_sSup ⟨Normal.map inferInstance q hq,pCore_isPGroup.map q⟩
    rw [hc] at hmap
    exact (Subgroup.map_eq_bot_iff _).mp (bot_unique hmap)

end CFSG.Quasithin.Chapter15.Section02
