module
public import Stellmacher.SectionTen.TenOneSmallCentralizerEdgeNoncentral
public import Theory.GroupTheory.SpecificGroups.DihedralEightRecognition

/-!
# The dihedral residual quotient of the small terminal edge

When Wstar has order sixteen in the actual small first-module case, the
terminal edge modulo the middle residual two-core is dihedral of order
eight. The companion theorem gives the source alternative Wstar=W0 or
this dihedral quotient, with no extra case hypothesis.

The edge has order128, and its normal middle residual core has order16.
The Wstar image in this literal quotient is elementary of order4 because
its kernel is the middle center of order4. If that image were central,
the edge commutator would lie in Wstar and in the residual core, contradicting
the proved terminal-edge noncentrality. The general order-eight recognition
then identifies the quotient with D8. Composing its equivalence with the
actual quotient projection preserves the required kernel exactly.

Source: Stellmacher (10.1)(a3), printed p.61, assertion (8),
`refs/files/stellmacher-n-group.pdf`. The edge is the literal
Gmiddle∩Gterminal introduced on that page.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_edge_dihedral
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    Nat.card Wstar=16 → QuotientIsModel
      (GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a')
      (twoCoreIn (EAt ctx.Γ middle)) (DihedralGroup 4) := by
  let M := GAt ctx.Γ middle
  let edge := M ⊓ GAt ctx.Γ ctx.criticalPath.a'
  let Q := QAt ctx.Γ middle
  let E := EAt ctx.Γ middle
  let D := twoCoreIn E
  let Z := ZAt ctx.Γ middle
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := Q ⊓ Subgroup.centralizer (W0 : Set G)
  change Nat.card Wstar=16 → QuotientIsModel edge D (DihedralGroup 4)
  intro hWcard
  obtain ⟨_,_,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hQM : Q ≤ M := by
    change ctx.Γ.twoCoreAt middle ≤ _
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQneighbor : Q ≤ GAt ctx.Γ ctx.criticalPath.a' :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core middle ctx.criticalPath.a'
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal) default).2.2
  have hQedge : Q ≤ edge := le_inf hQM hQneighbor
  have hDQ : D ≤ Q := by
    change twoCoreIn (ctx.Γ.twoResidualAt middle) ≤ ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hDedge : D ≤ edge := hDQ.trans hQedge
  have hE : E=twoResidualIn M := ctx.Γ.twoResidualAt_def middle
  have hEM : E ≤ M := hE ▸ twoResidualIn_le M
  have hDM : D ≤ M := (twoCoreIn_le E).trans hEM
  have hMD : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mp
      (twoCoreIn_normal_of_normal E M hEM (hE ▸ twoResidualIn_normal M))
  let N := D.subgroupOf edge
  let _ : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    ((inf_le_left : edge ≤ M).trans hMD)
  let V := edge ⧸ N
  let q : edge →* V := QuotientGroup.mk' N
  have hDcard : Nat.card D=16 := by
    obtain ⟨e⟩ := ten_one_middle_residual_c4_square ctx middle hpath hsmall hmodel
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card]
  have hQcard : Nat.card Q=64 := by
    have hh := ten_one_small_middle_core_card ctx middle hpath hsmall hmodel
    change Nat.card Q=4*Nat.card Wstar at hh
    omega
  have hedgecard : Nat.card edge=128 := by
    have hh : Nat.card edge=2*Nat.card Q :=
      (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle
        (sectionTenOpeningData ctx middle hpath).quotient_model).edge_card _ hterminal
    omega
  have hVcard : Nat.card V=8 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDedge).toEquiv,hDcard,hedgecard] at hh
    change 128=Nat.card V*16 at hh
    omega
  have hWedge : Wstar ≤ edge := (inf_le_left : Wstar ≤ Q).trans hQedge
  obtain ⟨hMW,hWelem,_,hWD,_⟩ :=
    ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel
  change Wstar ⊓ D=Z at hWD
  let _ : IsElementaryAbelian 2 Wstar := hWelem
  let _ : IsElementaryAbelian 2 (Wstar.subgroupOf edge) := IsElementaryAbelian.subgroupOf hWedge
  let U := (Wstar.subgroupOf edge).map q
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.map q
  have hZW : Z ≤ Wstar := by rw [← hWD]; exact inf_le_left
  have hZcard : Nat.card Z=4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hDW : D.subgroupOf Wstar=Z.subgroupOf Wstar := by
    ext w
    constructor
    · intro hw
      exact hWD.le ⟨w.property,hw⟩
    · intro hw
      exact (hWD.ge hw).2
  have hDWindex : (D.subgroupOf Wstar).index=4 := by
    have hh := (D.subgroupOf Wstar).index_mul_card
    rw [hDW,Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv,hZcard,hWcard] at hh
    rw [hDW]
    omega
  have hUcard : Nat.card U=4 := by
    change Nat.card ((Wstar.subgroupOf edge).map (QuotientGroup.mk' N))=4
    rw [← Subgroup.relIndex_ker,QuotientGroup.ker_mk']
    change (D.subgroupOf edge).relIndex (Wstar.subgroupOf edge)=4
    rw [Subgroup.relIndex_subgroupOf hWedge]
    exact hDWindex
  have hUnot : ¬ U ≤ Subgroup.center V := by
    intro hcentral
    have hcommD : ⁅Wstar,edge⁆ ≤ D := by
      apply Subgroup.commutator_le.mpr
      intro w hw t ht
      let wE : edge := ⟨w,hWedge hw⟩
      let tE : edge := ⟨t,ht⟩
      have hc : q wE ∈ Subgroup.center V :=
        hcentral (Subgroup.mem_map_of_mem q (show wE ∈ Wstar.subgroupOf edge from hw))
      have hq : q ⁅wE,tE⁆=1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_center_iff.mp hc (q tE)).symm
      have hh := (QuotientGroup.eq_one_iff ⁅wE,tE⁆).mp hq
      exact hh
    have hcommW : ⁅Wstar,edge⁆ ≤ Wstar :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp ((inf_le_left : edge ≤ M).trans hMW)
    exact ten_one_small_wstar_terminal_edge_commutator_not_le_center
      ctx middle hpath hsmall hmodel hWcard ((le_inf hcommW hcommD).trans_eq hWD)
  obtain ⟨e⟩ := dihedral_eight_of_noncentral_elementary_four hVcard U hUcard hUnot
  refine ⟨e.toMonoidHom.comp q,e.surjective.comp (QuotientGroup.mk'_surjective N),?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']

public theorem ten_one_small_wzero_or_edge_dihedral
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    Wstar=W0 ∨ QuotientIsModel (GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a')
      (twoCoreIn (EAt ctx.Γ middle)) (DihedralGroup 4) := by
  rcases ten_one_small_middle_core_card_cases ctx middle hpath hsmall hmodel with h32 | h64
  · exact Or.inl h32.1
  · exact Or.inr (ten_one_small_edge_dihedral ctx middle hpath hsmall hmodel h64.1)

end Stellmacher.SectionTen
