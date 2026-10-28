module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CoreCentrality
public import Theory.GroupTheory.CentralKernelSubgroupEmbedding
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# The two actual blocks in the full central quotient

The central quotient is faithful on both centerless natural blocks. Their
perfectness reflects containment through its central kernel, so their images
remain distinct and the original block remains proper. Both images retain
the full natural actions, two-cores and local-family membership for the same
mapped Sylow. Genuine Theorems A and C give SQTK and the complete carrier
catalogue for this literal quotient.

These are inputs to the remaining odd-degree projective recognition in
qt-d-10-nona5-moving-hall-three. The Hall consumer uses them before lifting
the recognized quotient with the ordinary center bound.
Source: Aschbacher–Smith A.3.12 and10.2.3(4), printed pp.47–48 and747.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.MovingHall
open ChapterC ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
private theorem center_transport {X Y : Type*} [Group X] [Group Y]
    (a : X ≃* Y) (h : center X = ⊥) : center Y = ⊥ := by
  apply bot_unique
  intro y hy
  have hh := (centerCongr a.symm ⟨y,hy⟩).property
  change a.symm y ∈ center X at hh
  rw [h,mem_bot] at hh
  exact mem_bot.mpr (a.symm.injective (hh.trans a.symm.map_one.symm))
private theorem core_transport {X Y : Type*} [Group X] [Group Y]
    (a : X ≃* Y) (h : pCore 2 X = blockU X) : pCore 2 Y = blockU Y := by
  rw [←pCore_map_iso 2 a,h,blockU,map_commutator,pCore_map_iso,
    map_top_of_surjective _ a.surjective,blockU]

/-- The literal images of both original natural blocks under the full central
quotient, with their local membership and unchanged field degree. -/
@[expose] def CenterQuotientBlockPair
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n) : Prop :=
    let C := c.overcomponent
    let q := QuotientGroup.mk' (center C)
    let J := (c.original.subgroupOf C).map q
    let K := ((c.comparison.map H.subtype).subgroupOf C).map q
    IsL2EvenBlock J n ∧ center J = ⊥ ∧ pCore 2 J = blockU J ∧
    IsL2EvenBlock K n ∧ center K = ⊥ ∧ pCore 2 K = blockU K ∧
    J ≠ K ∧ J ≠ ⊤ ∧
    ∃ S : Sylow 2 (C ⧸ center C),
      J ∈ localCComponents S ∧ K ∈ localCComponents S

/-- Both blocks survive faithfully and distinctly in the actual central quotient. -/
theorem CommonOvercomponent.center_quotient_pair
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) : CenterQuotientBlockPair c := by
  let C := c.overcomponent
  let q := QuotientGroup.mk' (center C)
  let J := c.original.subgroupOf C
  let K := (c.comparison.map H.subtype).subgroupOf C
  have hq : q.ker ≤ center C := (QuotientGroup.ker_mk' _).le
  let a : c.original ≃* J := (subgroupOfEquivOfLe c.original_lt.le).symm
  let b : c.comparison ≃* K :=
    (c.comparison.equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe c.comparison_le).symm
  have hzJ : center J = ⊥ := center_transport a c.original_center
  have hzK : center K = ⊥ := center_transport b c.comparison_center
  let eJ := a.trans (q.subgroupMapEquivOfKerLeCenter hq J hzJ)
  let eK := b.trans (q.subgroupMapEquivOfKerLeCenter hq K hzK)
  obtain ⟨P,_,hJ,hK⟩ := c.local_family
  let : Group.IsPerfect (J.subgroupOf (J ⊔ (P : Subgroup C))) := hJ.perfect
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show J ≤ J ⊔ (P : Subgroup C) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  let : Group.IsPerfect (K.subgroupOf (K ⊔ (P : Subgroup C))) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (P : Subgroup C) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  let : IsQuasisimple C := c.quasisimple hi
  let : Group.IsPerfect (⊤ : Subgroup C) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := C)).symm.toMonoidHom) (topEquiv (G := C)).symm.surjective
  have hne : J.map q ≠ K.map q := by
    intro he
    have he' : J = K := le_antisymm
      (perfect_le_of_map_le_of_central_kernel q hq J K he.le)
      (perfect_le_of_map_le_of_central_kernel q hq K J he.ge)
    apply c.distinct
    apply le_antisymm
    · intro x hx
      have hxJ : (⟨x,c.original_lt.le hx⟩ : C) ∈ J := hx
      rw [he'] at hxJ
      exact hxJ
    · intro x hx
      have hxK : (⟨x,c.comparison_le hx⟩ : C) ∈ K := hx
      rw [←he'] at hxK
      exact hxK
  have hnt : J.map q ≠ ⊤ := by
    intro he
    have hle : (⊤ : Subgroup C) ≤ J :=
      perfect_le_of_map_le_of_central_kernel q hq ⊤ J (by rw [he]; exact le_top)
    exact c.original_lt.ne (le_antisymm c.original_lt.le
      (subgroupOf_eq_top.mp (top_unique hle)))
  let : Group.IsSolvable q.ker := by
    rw [show q.ker = center C from QuotientGroup.ker_mk' _]
    exact Group.isSolvable_of_comm (fun a b =>
      Subtype.ext (mem_center_iff.mp a.property b).symm)
  refine ⟨c.original_natural.of_equiv eJ,center_transport eJ c.original_center,
    core_transport eJ c.original_core,c.comparison_natural.of_equiv eK,
    center_transport eK c.comparison_center,core_transport eK c.comparison_core,
    hne,hnt,P.mapSurjective (QuotientGroup.mk'_surjective _),?_,?_⟩
  · simpa only [Sylow.coe_mapSurjective] using Chapter1.Section02.localCComponents_map_of_solvable_ker hJ q
  · simpa only [Sylow.coe_mapSurjective] using Chapter1.Section02.localCComponents_map_of_solvable_ker hK q
/-- Genuine Theorems A and C classify the literal full central quotient. -/
theorem CommonOvercomponent.center_quotient_catalogue
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) :
    IsSQTK KnownSimple.IsKnownSimple (c.overcomponent ⧸ center c.overcomponent) ∧
      Chapter1.Section02.LocalModels.TheoremCModel
        (c.overcomponent ⧸ center c.overcomponent) := by
  let C := c.overcomponent
  let Q := C ⧸ center C
  let : IsQuasisimple C := c.quasisimple hi
  let : IsSimpleGroup Q := IsQuasisimple.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center C))
  have hz : center Q = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot C
  let : IsQuasisimple Q := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hC : IsSQTK KnownSimple.IsKnownSimple C := ⟨
    c.local_sqtk.stronglyQuasithin.of_injective (inclusion c.component.1)
      (inclusion_injective c.component.1),
    c.local_sqtk.isKGroup.of_injective (inclusion c.component.1)
      (inclusion_injective c.component.1)⟩
  have hsem : ChapterA.Section02.IsSemisimple Q := by
    apply top_unique
    exact le_sSup (show IsComponent Q ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hsec : ChapterA.Section02.IsSectionOf Q C :=
    .of_surjective (QuotientGroup.mk' (center C)) (QuotientGroup.mk'_surjective _)
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := ⟨
    (ChapterA.Section02.theoremA_knownSimple (G := C)).stronglyQuasithin_section
      hC.stronglyQuasithin hC.isKGroup hsec hsem,
    hC.isKGroup.quotient _⟩
  exact ⟨hQ,ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
    (Group.IsPerfect.not_isMulCommutative Q)
    (ChapterA.Section02.theoremC_knownSimple (G := Q) inferInstance
      (Group.IsPerfect.not_isMulCommutative Q) hQ.stronglyQuasithin hQ.isKGroup)⟩

end CFSG.Quasithin.Chapter10.MovingHall
