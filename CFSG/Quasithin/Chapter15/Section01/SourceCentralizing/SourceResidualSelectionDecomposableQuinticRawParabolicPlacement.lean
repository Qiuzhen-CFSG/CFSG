module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawThompson
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.Definitions
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Normalized
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.ResidualGeneration

/-!
Original normalized parabolics lie in one of the two original marked
intersections. The same universal characteristic pair is transported from
Baum(T), and the small quotient makes its closure minimal parabolic.
An actual moving A3 block would pull back a forbidden residual product.
The closure has characteristic two directly because the original two-group
normalizes the characteristic-two parabolic. No component record, ambient
M-generation or prior residual-normalization hypothesis is used.

The two import-all edges intentionally reuse only the record-free intrinsic
helpers minimal_of_small_core_quotient, residual_product_pullback, and
twoThree_of_small_quotient. Their private names do not enter the public API.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

private noncomputable def rawPairEquiv (T : Sylow 2 G) (S H : Subgroup G)
    (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = S)
    (hB : baumann S = baumann (T : Subgroup G)) :
    baumann (R : Subgroup H) ≃* baumann (T : Subgroup G) :=
  ((baumann (R : Subgroup H)).equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (by
      unfold baumann thompsonAlpha at hB ⊢
      rw [baumann_map_injective H.subtype H.subtype_injective,hR]
      exact hB))

omit [Finite G] in
private theorem rawPair_member_map (T : Sylow 2 G) (S H : Subgroup G)
    (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = S)
    (hB : baumann S = baumann (T : Subgroup G))
    (A : Subgroup (baumann (T : Subgroup G))) :
    ((A.map (rawPairEquiv T S H R hR hB).symm.toMonoidHom).map
      (baumann (R : Subgroup H)).subtype).map H.subtype =
        A.map (baumann (T : Subgroup G)).subtype := by
  rw [map_map,map_map]
  congr 1
  ext b
  exact congrArg (baumann (T : Subgroup G)).subtype
    ((rawPairEquiv T S H R hR hB).apply_symm_apply b)

omit [Finite G] in
private theorem rawPair_firstSeed_map (T : Sylow 2 G) (S H : Subgroup G)
    (R : Sylow 2 H) (hR : (R : Subgroup H).map H.subtype = S)
    (hB : baumann S = baumann (T : Subgroup G))
    (D : CharacteristicPair (baumann (T : Subgroup G))) :
    (FixedPair.firstSeed R (D.map (rawPairEquiv T S H R hR hB).symm)).map H.subtype =
      omegaOneCenterAmbient S ⊓ D.first.map (baumann (T : Subgroup G)).subtype := by
  rw [FixedPair.firstSeed,Subgroup.map_inf _ _ _ H.subtype_injective,
    ←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,hR]
  exact congrArg (fun A => omegaOneCenterAmbient S ⊓ A)
    (rawPair_member_map T S H R hR hB D.first)

private theorem rawPair_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L P H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hLG : L ≤ centralizer (Z1 : Set G)) (hPL : P ≤ L) (hPH : P ≤ H)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (R : Sylow 2 H)
    (hR : (R : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ centralizer (Z1 : Set G))
    (hB : baumann ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) = baumann (T : Subgroup G))
    (halt :
      FixedPair.firstSeed R (D.map (rawPairEquiv T _ H R hR hB).symm) ≤ center H ∨
      ((D.map (rawPairEquiv T _ H R hR hB).symm).second.map
        (baumann (R : Subgroup H)).subtype).Normal) :
    P ≤ M ⊓ L ∨ P ≤ (centralizer (Z1 : Set G) ⊓ Mc) ⊓ L := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let Z := omegaOneCenterAmbient S ⊓ D.first.map (baumann (T : Subgroup G)).subtype
  have hseed : FixedPair.firstSeed T D ≤ Z := by
    intro x hx
    obtain ⟨hxT,hx2,hxc⟩ := (mem_omegaOneCenterAmbient_iff _ x).mp hx.1
    have hxB : x ∈ baumann (T : Subgroup G) := (map_subtype_le D.first) hx.2
    have hxS : x ∈ S := (show baumann S ≤ S from inf_le_left) (hB.symm ▸ hxB)
    exact ⟨(mem_omegaOneCenterAmbient_iff _ x).mpr
      ⟨hxS,hx2,fun s hs => hxc s hs.1⟩,hx.2⟩
  have hCMc : centralizer (Z : Set G) ≤ Mc :=
    (centralizer_le hseed).trans (UniformControl.firstSeed_centralizer_le_partner T D hu)
  have hnM : normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ≤ M := by
    let := D.second_characteristic
    have hc := (h.caseI_marked_thompson_control hG T hM hJ hZ).2.2.1
    rw [hB] at hc
    exact (normalizer_le_characteristicNormalizerClosure _ D.second D.second_ne_bot).trans hc
  rcases halt with hc | hn
  · right
    refine le_inf (le_inf (hPL.trans hLG) (hPH.trans (?_ : H ≤ Mc))) hPL
    apply le_trans _ hCMc
    intro x hx z hz
    change z ∈ omegaOneCenterAmbient S ⊓ D.first.map (baumann (T : Subgroup G)).subtype at hz
    rw [←rawPair_firstSeed_map T S H R hR hB D] at hz
    obtain ⟨a,ha,rfl⟩ := hz
    exact (congrArg H.subtype ((mem_center_iff.mp (hc ha)) ⟨x,hx⟩)).symm
  · left
    refine le_inf (hPH.trans ((?_ : H ≤ normalizer
      (D.second.map (baumann (T : Subgroup G)).subtype : Set G)).trans hnM)) hPL
    let := hn
    have hh := ((D.map (rawPairEquiv T S H R hR hB).symm).second.map
      (baumann (R : Subgroup H)).subtype).le_normalizer_map H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    change H ≤ normalizer (((D.second.map
      (rawPairEquiv T S H R hR hB).symm.toMonoidHom).map
        (baumann (R : Subgroup H)).subtype).map H.subtype : Set G) at hh
    rwa [rawPair_member_map] at hh

/-- A normalized original source parabolic is placed in one of the same
original intersections. All inputs concern actual subgroups and the literal
closure quotient; no placement or generation hypothesis is supplied. -/
theorem PreparedChosenModule.raw_parabolic_placement_of_sylow_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L P : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hLG : L ≤ centralizer (Z1 : Set G)) (hPL : P ≤ L)
    (hnP : ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (P : Set G))
    (hfit : generalizedFitting P = pCore 2 P)
    (hquot :
      Nonempty (((P ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) : Subgroup G) ⧸
        pCore 2 (P ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) : Subgroup G)) ≃*
          Equiv.Perm (Fin 3)) ∨
      Nonempty (((P ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) : Subgroup G) ⧸
        pCore 2 (P ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) : Subgroup G)) ≃*
          RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hno : ¬CaseIComponentData.IsAThreeProduct P) :
    P ≤ M ⊓ L ∨ P ≤ (centralizer (Z1 : Set G) ⊓ Mc) ⊓ L := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let H := P ⊔ S
  have hHG : H ≤ centralizer (Z1 : Set G) := sup_le (hPL.trans hLG) inf_le_right
  have hSH : Chapter1.IsSylowIn 2 S H := hSyl.restrict le_sup_right hHG
  obtain ⟨R,hR⟩ := hSH
  have hB := (h.caseI_marked_thompson_control hG T hM hJ hZ).2.1
  let : (P.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hnP)
  have hfitH : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_sup_le 2 P S
        (hfit ▸ centralizer_generalizedFitting_le P) (T.isPGroup'.to_le inf_le_left) hnP)
  have hpi := CaseIComponentData.twoThree_of_small_quotient H hquot
  let : Group.IsSolvable H := by
    apply isSolvable_of_prime_dvd_card_eq_two_or_three
    intro q hq hd
    exact (IsPiGroup_iff _ _).mp hpi ⟨q,hq⟩ hd
  have hmin := CaseIComponentData.minimal_of_small_core_quotient R hquot
  let := h.elementary
  have hsq := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  have h3 : primeRank 3 H ≤ 2 :=
    (hsq.stronglyQuasithin.of_injective (inclusion hHG)
      (inclusion_injective hHG)) 3 Nat.prime_three (by decide)
  have hres : (pResidual 2 H).map H.subtype = (pResidual 2 P).map P.subtype := by
    let E := (pResidual 2 P).map P.subtype
    obtain ⟨U,hU⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      (show Chapter1.IsSylowIn 2 S H from ⟨R,hR⟩) le_sup_left
      (inferInstance : (P.subgroupOf H).Normal).isSubnormal
    have hgenP := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top U)
    rw [Subgroup.map_sup,hU,←MonoidHom.range_eq_map,range_subtype] at hgenP
    have hgen : E ⊔ S = H := by
      calc
        E ⊔ S = (E ⊔ (S ⊓ P)) ⊔ S := by
          rw [sup_assoc,sup_eq_right.mpr (show S ⊓ P ≤ S from inf_le_left)]
        _ = H := congrArg (· ⊔ S) hgenP
    rw [←hgen]
    exact embedded_pResidual_join_pGroup E S
      ((isPPerfect_pResidual 2).of_surjective
        ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).toMonoidHom
        ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).surjective)
      (T.isPGroup'.to_le inf_le_left)
      (hnP.trans (normalizer_le_normalizer_characteristic_image P (pResidual 2 P)))
  obtain ⟨D,hD,_⟩ := FixedPair.exists_uniform_pair.{u,u} T (MainForward.sylow_ne_bot hG T)
  let D0 := D.map (rawPairEquiv T S H R hR hB).symm
  have hplace := rawPair_placement hG T hM hJ hu h hZ hLG hPL
    (show P ≤ H from le_sup_left) D R hR hB
  by_cases hc : FixedPair.firstSeed R D0 ≤ center H
  · exact hplace (Or.inl hc)
  by_cases hn : (D0.second.map (baumann (R : Subgroup H)).subtype).Normal
  · exact hplace (Or.inr hn)
  obtain ⟨A,hb,ha,_⟩ :=
    FixedPairSolvable.NormalBaumann.minimal_parabolic_moving_alternatingThree_of_fixed_pair_escape
      R hmin hfitH D0 (hD.map _)
      (CaseIComponentData.fixed_pair_control_ne_top R hmin D0 hc hn) h3 inferInstance
  obtain ⟨F,_,hF,hcomm,hgen⟩ := alternatingThree_residual_product hfitH h3 R hmin A hb ha
  let f : P →* H := inclusion le_sup_left
  have he : (pResidual 2 P).map f = pResidual 2 H := by
    apply map_injective H.subtype_injective
    rw [map_map,hres]
    rfl
  exact (hno (CaseIComponentData.residual_product_pullback f (inclusion_injective _)
    F hF hcomm (hgen.trans he.symm))).elim

end CFSG.Quasithin.Chapter15.Section01
