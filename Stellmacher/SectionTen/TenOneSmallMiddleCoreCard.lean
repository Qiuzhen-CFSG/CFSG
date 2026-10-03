module
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreCenter
public import Theory.GroupTheory.CentralLayerCentralizerIndex

/-!
# The exact small middle-core order and residual product

For the actual order-eight first-module case with SL₂(2) quotient, put
W*=C_Qmiddle(W₀). Then |Qmiddle|=4|W*| and Qmiddle=O₂(Emiddle)W*.
Thus either W*=W₀ with |Qmiddle|=32, or |W*|=16 with |Qmiddle|=64.
The subgroups are the literal ones from the Section Ten configuration.

The central four-subgroup Zmiddle has index two in the elementary W₀.
The class-two core centralizes Zmiddle and has its commutators with W₀
inside Zmiddle, so the central-layer centralizer bound gives |Qmiddle:W*|≤4.
The known intersection W*∩O₂(Emiddle)=Zmiddle and residual-core order sixteen
give the reverse index bound. The two W* orders now give the stated cases;
in the order-eight case containment and equal cardinalities give W*=W₀.
Finally, normality of the residual core and the subgroup-product cardinal
formula identify the residual product with the whole middle core.

Source: Stellmacher (10.1)(a3), printed p.61 of
`refs/files/stellmacher-n-group.pdf`, the first W* paragraph and the two
subsequent normalizer branches.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_middle_core_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    Nat.card (QAt ctx.Γ middle) = 4 * Nat.card Wstar := by
  let Q := QAt ctx.Γ middle
  let D := twoCoreIn (EAt ctx.Γ middle)
  let K := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle)
  let W := GeneratedNeighborhoodV ctx.Γ middle
  let W0 := K ⊓ W
  let U := W0.subgroupOf Q
  let Z := ZAt ctx.Γ middle
  let ZQ := Z.subgroupOf Q
  let Wstar := Q ⊓ Subgroup.centralizer (W0 : Set G)
  have hW0Q : W0 ≤ Q := inf_le_right.trans
    (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext
      (by change 2 < ctx.criticalPath.length; rw [ctx.critical_length]; decide) middle)
  have hZQ : Z ≤ Q := by
    rw [show Z = omegaOneCenter Q from (sectionTenOpeningData ctx middle hpath).center_omega]
    exact Subgroup.map_subtype_le _
  have hZU : Z ≤ W0 := by
    refine le_inf ?_ ?_
    · apply le_sInf
      rintro D ⟨neighbor,hneighbor,rfl⟩
      exact (nine_seven_neighbor_center_le_module ctx.Γ
        (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor))).trans
          (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath
            (by rw [ctx.critical_length]; decide) neighbor)
    · obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
      exact (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst)).trans
        (show VAt ctx.Γ ctx.criticalPath.firstStep ≤ W from
          le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst,rfl⟩)
  have hcenter : Subgroup.center Q = ZQ := by
    have hh := congrArg (Subgroup.comap Q.subtype)
      (ten_one_small_middle_core_center ctx middle hpath hsmall hmodel)
    change ((Subgroup.center Q).map Q.subtype).comap Q.subtype = ZQ at hh
    rw [Subgroup.comap_map_eq_self_of_injective Q.subtype_injective] at hh
    exact hh
  have hZcard : Nat.card Z = 4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hZQcard : Nat.card ZQ = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv]
    exact hZcard
  have hZQU : ZQ ≤ U := Subgroup.subgroupOf_mono Q hZU
  have hUcard : Nat.card U = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW0Q).toEquiv]
    exact (ten_one_small_common_core_elementary ctx middle hpath hsmall hmodel).2.2
  have hindex : (ZQ.subgroupOf U).index = 2 := by
    have hh := (ZQ.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQU).toEquiv,hZQcard,hUcard] at hh
    omega
  have hcomm : ⁅(⊤ : Subgroup Q),U⁆ ≤ ZQ := by
    intro x hx
    apply ten_one_small_middle_core_commutator_le_center ctx middle hpath hsmall hmodel
    rw [← Subgroup.map_subtype_commutator Q]
    apply Subgroup.mem_map_of_mem Q.subtype
    exact Subgroup.commutator_mono le_rfl le_top hx
  have hbound : (Subgroup.centralizer (U : Set Q)).index ≤ 4 := by
    rw [← hZQcard]
    exact Subgroup.centralizer_index_le_card_of_central_index_two_layer U ZQ
      hZQU hcenter.ge hindex hcomm
  have hcentralizer : Subgroup.centralizer (U : Set Q) = Wstar.subgroupOf Q := by
    apply le_antisymm
    · intro q hq
      refine ⟨q.property,?_⟩
      change (q:G) ∈ Subgroup.centralizer (W0 : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hq ⟨w,hW0Q hw⟩ hw)
    · intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hq.2 u hu
  rw [hcentralizer] at hbound
  change Wstar.relIndex Q ≤ 4 at hbound
  have hDQ : D ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt middle) ≤ ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hWstarD : Wstar ⊓ D = Z :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.2.2.1
  have hDcard : Nat.card D = 16 := by
    obtain ⟨equiv⟩ := ten_one_middle_residual_c4_square ctx middle hpath hsmall hmodel
    rw [Nat.card_congr equiv.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card]
  have hlocal : Wstar.relIndex D = 4 := by
    have hinterCard : Nat.card (Wstar ⊓ D : Subgroup G) = 4 := by rw [hWstarD,hZcard]
    have hh := ((Wstar ⊓ D).subgroupOf D).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Wstar ⊓ D ≤ D from inf_le_right)).toEquiv,
      hinterCard,hDcard] at hh
    change (Wstar ⊓ D).relIndex D * 4 = 16 at hh
    rw [Subgroup.inf_relIndex_right] at hh
    omega
  have hlower := Subgroup.relIndex_le_of_le_right (H:=Wstar) hDQ
    (show Wstar.relIndex Q ≠ 0 from (Wstar.subgroupOf Q).index_ne_zero_of_finite)
  have hidx : Wstar.relIndex Q = 4 := by omega
  have hh := (Wstar.subgroupOf Q).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Wstar ≤ Q from inf_le_left)).toEquiv] at hh
  change Wstar.relIndex Q * Nat.card Wstar = Nat.card Q at hh
  rw [hidx] at hh
  exact hh.symm


public theorem ten_one_small_middle_core_card_cases
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    (Wstar = W0 ∧ Nat.card (QAt ctx.Γ middle) = 32) ∨
      (Nat.card Wstar = 16 ∧ Nat.card (QAt ctx.Γ middle) = 64) := by
  let Q := QAt ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Q ⊓ Subgroup.centralizer (W0 : Set G)
  change (Wstar = W0 ∧ Nat.card Q = 32) ∨ (Nat.card Wstar = 16 ∧ Nat.card Q = 64)
  have hcard : Nat.card Q = 4 * Nat.card Wstar :=
    ten_one_small_middle_core_card ctx middle hpath hsmall hmodel
  have hcases : Nat.card Wstar = 8 ∨ Nat.card Wstar = 16 :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.2.1
  rcases hcases with height | hsixteen
  · left
    obtain ⟨_,hel,hW0card⟩ := ten_one_small_common_core_elementary ctx middle hpath hsmall hmodel
    let _ : IsElementaryAbelian 2 W0 := hel
    change Nat.card W0 = 8 at hW0card
    have hW0Q : W0 ≤ Q := inf_le_right.trans
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext
        (by change 2 < ctx.criticalPath.length; rw [ctx.critical_length]; decide) middle)
    have hW0C : W0 ≤ Wstar := le_inf hW0Q (Subgroup.le_centralizer W0)
    exact ⟨(Subgroup.eq_of_le_of_card_ge hW0C (by omega)).symm,by omega⟩
  · exact Or.inr ⟨hsixteen,by omega⟩

public theorem ten_one_small_middle_core_residual_centralizer_product
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    QAt ctx.Γ middle = twoCoreIn (EAt ctx.Γ middle) ⊔ Wstar := by
  let M := GAt ctx.Γ middle
  let Q := QAt ctx.Γ middle
  let E := EAt ctx.Γ middle
  let D := twoCoreIn E
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Q ⊓ Subgroup.centralizer (W0 : Set G)
  have hQM : Q ≤ M := by
    change ctx.Γ.twoCoreAt middle ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le M
  have hE : E = twoResidualIn M := ctx.Γ.twoResidualAt_def _
  have hEM : E ≤ M := hE ▸ twoResidualIn_le M
  have hDM : D ≤ M := (twoCoreIn_le E).trans hEM
  have hDN : (D.subgroupOf M).Normal := twoCoreIn_normal_of_normal E M hEM
    (hE ▸ twoResidualIn_normal M)
  have hMD : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mp hDN
  have hDQ : D ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt middle) ≤ ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hCnorm : Wstar ≤ Subgroup.normalizer (D : Set G) :=
    (show Wstar ≤ Q from inf_le_left).trans (hQM.trans hMD)
  have hcount := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes D Wstar hCnorm
  have hWstarD : Wstar ⊓ D = ZAt ctx.Γ middle :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.2.2.1
  have hDcard : Nat.card D = 16 := by
    obtain ⟨equiv⟩ := ten_one_middle_residual_c4_square ctx middle hpath hsmall hmodel
    rw [Nat.card_congr equiv.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card]
  have hZcard := (sectionTenOpeningData ctx middle hpath).center_card
  rw [inf_comm D Wstar,hWstarD,hDcard,hZcard] at hcount
  have hcard : Nat.card Q = 4 * Nat.card Wstar :=
    ten_one_small_middle_core_card ctx middle hpath hsmall hmodel
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge (sup_le hDQ inf_le_left)
  change Nat.card Q ≤ Nat.card (D ⊔ Wstar : Subgroup G)
  omega

end Stellmacher.SectionTen
