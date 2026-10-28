module
public import Stellmacher.SectionTen.TenOneSmallEdgeDihedral
public import Theory.GroupTheory.SpecificGroups.DihedralEightCommutingPoint

/-!
# Points centralized by terminal-edge actors outside the middle core

In the actual small Section Ten context, suppose a point a of Wstar
commutes with an element u of the terminal edge outside Qmiddle. Then a
lies in W0. Neither an order assumption on u nor a cardinality branch is
part of the statement.

The order32 branch has Wstar=W0. In the remaining branch, the literal
terminal edge modulo D=O2(Emiddle) is D8. The Qmiddle image has order4
from64/16. The W0 image is normal of order2 from8/4, since W0 is invariant
under the middle stabilizer and W0∩D=Zmiddle. The actor u stays outside
the Qmiddle image because D≤Qmiddle. The D8 commuting-point theorem
therefore puts the image of a in the W0 image. A lift differs from a by
an element of Wstar∩D=Zmiddle≤W0, proving the native containment.

Source: Stellmacher (10.1)(a3), printed p.62, assertion (11),
`refs/files/stellmacher-n-group.pdf`. The terminal edge, supplied quotient
map and its exact residual-core kernel are retained throughout; the
separate fusion arguments supply the actor used in the source.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_edge_commuting_point_mem_wzero
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a u : G) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    a ∈ Wstar → u ∈ GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a' →
      u ∉ QAt ctx.Γ middle → Commute u a → a ∈ W0 := by
  let Γ := ctx.Γ
  let Wnext := GeneratedNeighborhoodV Γ middle
  let W0 := NeighborhoodQIntersection Γ (Neighborhood Γ middle) ⊓ Wnext
  let Q := QAt Γ middle
  let Wstar := Q ⊓ centralizer (W0:Set G)
  let M := GAt Γ middle
  let edge := M ⊓ GAt Γ ctx.criticalPath.a'
  let D := twoCoreIn (EAt Γ middle)
  let Z := ZAt Γ middle
  change a∈Wstar → u∈edge → u∉Q → Commute u a → a∈W0
  intro ha hu huQ hcomm
  rcases ten_one_small_middle_core_card_cases ctx middle hpath hsmall hmodel with h32 | h64
  · exact (show Wstar=W0 from h32.1) ▸ ha
  have hQcard : Nat.card Q=64 := h64.2
  obtain ⟨f,hsurj,hker⟩ := ten_one_small_edge_dihedral ctx middle hpath hsmall hmodel h64.1
  change f.ker=D.subgroupOf edge at hker
  have hb : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hQedge : Q ≤ edge := by
    refine le_inf ?_ ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core middle
      ctx.criticalPath.a' ((mem_neighborhood_iff_adjacent Γ).mpr hterminal) default).2.2
    change Γ.twoCoreAt middle ≤ Γ.stabilizer middle
    rw [Γ.twoCoreAt_def]
    exact map_subtype_le _
  have hDQ : D ≤ Q := by
    change twoCoreIn (Γ.twoResidualAt middle) ≤ Γ.twoCoreAt middle
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hW0Q : W0 ≤ Q := inf_le_right.trans
    (nine_seven_neighborhood_le_own_core ctx.toLocalContext.toSectionNineLocalContext hb middle)
  have hZW0 : Z ≤ W0 := by
    refine le_inf ?_ ?_
    · apply le_sInf
      rintro R ⟨neighbor,hneighbor,rfl⟩
      exact (nine_seven_neighbor_center_le_module Γ
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hneighbor))).trans
          (neighbor_join_le_core_of_length_gt_one Γ ctx.criticalPath (by omega) neighbor)
    · exact (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hfirst)).trans
        (show VAt Γ ctx.criticalPath.firstStep ≤ Wnext from
          le_sSup ⟨_,(mem_neighborhood_iff_adjacent Γ).mpr hfirst,rfl⟩)
  obtain ⟨hMW0,hW0elem,hW0card⟩ := ten_one_small_common_core_elementary ctx middle hpath hsmall hmodel
  change M ≤ normalizer (W0:Set G) at hMW0
  change Nat.card W0=8 at hW0card
  let _ : IsElementaryAbelian 2 W0 := hW0elem
  have hW0star : W0 ≤ Wstar := le_inf hW0Q (Subgroup.le_centralizer W0)
  have hWD : Wstar ⊓ D=Z :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.2.2.1
  have hDcard : Nat.card D=16 := ten_one_middle_residual_core_card ctx middle hpath hsmall hmodel
  have hZcard : Nat.card Z=4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hDW0 : D.subgroupOf W0=Z.subgroupOf W0 := by
    ext w
    constructor
    · intro hw
      exact hWD.le ⟨hW0star w.property,hw⟩
    · intro hw
      exact (hWD.ge hw).2
  have hDindexQ : D.relIndex Q=4 := by
    have hh := (D.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hDQ).toEquiv,hDcard,hQcard] at hh
    change D.relIndex Q*16=64 at hh
    omega
  have hDindexW0 : D.relIndex W0=2 := by
    have hh := (D.subgroupOf W0).index_mul_card
    rw [hDW0,Nat.card_congr (subgroupOfEquivOfLe hZW0).toEquiv,hZcard,hW0card] at hh
    change (Z.subgroupOf W0).index*4=8 at hh
    change (D.subgroupOf W0).index=2
    rw [hDW0]
    omega
  let Qimage := (Q.subgroupOf edge).map f
  let Zimage := (W0.subgroupOf edge).map f
  have hW0edge : W0 ≤ edge := hW0Q.trans hQedge
  let _ : (W0.subgroupOf edge).Normal := normal_subgroupOf_of_le_normalizer
    ((show edge≤M from inf_le_left).trans hMW0)
  let _ : Zimage.Normal := (inferInstance : (W0.subgroupOf edge).Normal).map f hsurj
  have hQimageCard : Nat.card Qimage=4 := by
    rw [show Qimage=(Q.subgroupOf edge).map f from rfl,←relIndex_ker,hker,
      relIndex_subgroupOf hQedge]
    exact hDindexQ
  have hZimageCard : Nat.card Zimage=2 := by
    rw [show Zimage=(W0.subgroupOf edge).map f from rfl,←relIndex_ker,hker,
      relIndex_subgroupOf hW0edge]
    exact hDindexW0
  let aE : edge := ⟨a,hQedge ha.1⟩
  let uE : edge := ⟨u,hu⟩
  have haImage : f aE∈Qimage := mem_map_of_mem f (show aE∈Q.subgroupOf edge from ha.1)
  have huImage : f uE∉Qimage := by
    intro hh
    have hkerQ : f.ker≤Q.subgroupOf edge := by
      rw [hker]
      exact subgroupOf_mono edge hDQ
    have hpre : Qimage.comap f=Q.subgroupOf edge := by
      change ((Q.subgroupOf edge).map f).comap f=Q.subgroupOf edge
      rw [comap_map_eq,sup_eq_left.mpr hkerQ]
    have huPre : uE∈Qimage.comap f := hh
    rw [hpre] at huPre
    exact huQ huPre
  have hcommE : Commute uE aE := by
    change uE*aE=aE*uE
    exact Subtype.ext hcomm.eq
  have haZimage : f aE∈Zimage := DihedralGroup.mem_normal_two_of_commuting_outside_four
    Qimage Zimage hQimageCard hZimageCard (f aE) (f uE) haImage huImage (hcommE.map f)
  obtain ⟨w,hw,hwa⟩ := haZimage
  have hdiff : w⁻¹*aE ∈ f.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,hwa]
    simp
  have hdiffD : (w:G)⁻¹*a ∈ D := hker.le hdiff
  have hdiffStar : (w:G)⁻¹*a ∈ Wstar := Wstar.mul_mem
    (Wstar.inv_mem (hW0star hw)) ha
  have hdiffW0 : (w:G)⁻¹*a ∈ W0 := hZW0 (hWD.le ⟨hdiffStar,hdiffD⟩)
  simpa only [Subgroup.coe_subtype,←mul_assoc,mul_inv_cancel,one_mul] using W0.mul_mem hw hdiffW0

end Stellmacher.SectionTen

