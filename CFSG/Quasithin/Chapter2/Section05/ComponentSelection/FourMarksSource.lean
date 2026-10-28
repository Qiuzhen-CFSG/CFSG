module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CentralCoreInvolutionSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MarkSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
public import Theory.GroupTheory.CenterPairMarks
public import Theory.GroupTheory.TwoGroupSquareChoice
public import Theory.ElementaryAbelian.Join
/-! # Recovering the original central four-group and marked center line
The central core factor is nontrivial and has a disjoint conjugate inside
the Sylow center. Its index-two complementary factor forces both factors
to have order two. The literal central-core involution and original z then
generate this four-group; the ambient Sylow center is exactly the z-line.
The source center-split producers discharge the sole preceding structural input.
Source: Aschbacher--Smith 2.5.11, printed p.557.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.center_four_of_center_split
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (A:Subgroup G)
    (hsplit:centerIn ((S:Subgroup H).map H.subtype)=
      A⊔(centerIn ((S:Subgroup H).map H.subtype)⊓twoCore H))
    (hdis:Disjoint A (centerIn ((S:Subgroup H).map H.subtype)⊓twoCore H))
    (hA:Nat.card A=2) :
    Nat.card (centerIn ((S:Subgroup H).map H.subtype))=4 ∧
      Nat.card (centerIn ((S:Subgroup H).map H.subtype)⊓twoCore H:Subgroup G)=2 := by
  let Y:=(S:Subgroup H).map H.subtype
  let C:=centerIn Y⊓twoCore H
  obtain ⟨t,ht,htC,htZ⟩:=MathieuSourceSetup.exists_central_core_involution c
  have hC:C≠⊥:=by
    intro he
    have ht1:t=1:=mem_bot.mp (he ▸ (show t∈C from ⟨htZ,htC⟩))
    rw [ht1,orderOf_one] at ht
    omega
  obtain ⟨x,hxT,hxS,hxN,hx2⟩:=exists_outside_normalizer_square_mem Y c.T c.T.isPGroup' c.sylow_lt
  have hd:Disjoint C (C.conjBy x⁻¹):=
    (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c) ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1.mono
      inf_le_right (map_mono (f:=(MulAut.conj x⁻¹).toMonoidHom) inf_le_right)
  obtain ⟨hC2,hZ4,_⟩:=center_pair_of_disjoint_factor Y A C hsplit hdis hA hC x⁻¹
    ((normalizer (Y:Set G)).inv_mem hxN) hd
  exact ⟨hZ4,hC2⟩

theorem MathieuSourceSetup.central_core_involution_not_mem_center_ambient
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (t:G) (ht:orderOf t=2) (htC:t∈twoCore H)
    (htZ:t∈centerIn ((S:Subgroup H).map H.subtype)) :
    t∉centerIn (c.T:Subgroup G) := by
  obtain ⟨_,_,⟨P,hP⟩,_,_⟩:=MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  intro htT
  let C:=centralizer ({t}:Set G)
  have hTC:(c.T:Subgroup G)≤C:=fun a ha=>mem_centralizer_singleton_iff.mpr (htT.2 a ha)
  have hPQ:(P:Subgroup C)≤(c.T:Subgroup G).subgroupOf C:=by
    intro a ha
    exact c.sylow_lt.le (hP ▸ mem_map_of_mem C.subtype ha)
  have he:P.toSubgroup=(c.T:Subgroup G).subgroupOf C:=
    (P.is_maximal' c.T.isPGroup'.comap_subtype hPQ).symm
  have hm:=congrArg (Subgroup.map C.subtype) he
  rw [hP,map_subgroupOf_eq_of_le hTC] at hm
  exact c.sylow_lt.ne hm

theorem MathieuSourceSetup.ambient_center_eq_mark_of_four
    (c:MathieuSourceSetup H L M S z)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hfour:Nat.card (centerIn ((S:Subgroup H).map H.subtype))=4) :
    centerIn (c.T:Subgroup G)=zpowers z := by
  obtain ⟨t,ht,htC,htZ⟩:=MathieuSourceSetup.exists_central_core_involution c
  apply center_eq_marked_line_of_four _ _ c.sylow_lt.le
    (by simpa only [centerIn_eq_map_center] using c.center_le) hfour z c.involution
    (by simpa only [centerIn_eq_map_center] using c.mem_center) t htZ
  exact MathieuSourceSetup.central_core_involution_not_mem_center_ambient c hgen t ht htC htZ
private theorem two_zpowers_cases (t:G) (ht:orderOf t=2) (a:G) (ha:a∈zpowers t) :
    a=1∨a=t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,ht] at ha
  obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp ha
  have hnlt:=Finset.mem_range.mp hn
  interval_cases n <;> simp

theorem MathieuSourceSetup.marked_center_pair_of_four
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hfour:Nat.card (centerIn ((S:Subgroup H).map H.subtype))=4)
    (hcorecenter:Nat.card (centerIn ((S:Subgroup H).map H.subtype)⊓twoCore H:Subgroup G)=2) :
    ∃t:G,orderOf t=2 ∧ t∈twoCore H ∧
      centerIn ((S:Subgroup H).map H.subtype)⊓twoCore H=zpowers t ∧
      centerIn ((S:Subgroup H).map H.subtype)=zpowers t⊔zpowers z ∧
      IsKleinFour (centerIn ((S:Subgroup H).map H.subtype)) ∧
      centerIn (c.T:Subgroup G)=zpowers z := by
  let Y:=(S:Subgroup H).map H.subtype
  let C:=centerIn Y⊓twoCore H
  obtain ⟨t,ht,htC⟩:=exists_involution_generator_of_card_two C hcorecenter
  have htmem:t∈C:=htC ▸ mem_zpowers t
  have hzmem:z∈centerIn Y:=by
    have h:=c.localSetup hG structural115Input localC129Input_knownSimple
    exact ⟨h.mem_sylow,h.central⟩
  have hznot:z∉C:=fun h=>MathieuSourceSetup.mark_not_mem_twoCore c hG
    localC129Input_knownSimple hempty hgen h.2
  have hdis:Disjoint C (zpowers z):=by
    apply disjoint_def.mpr
    intro a ha hb
    rcases two_zpowers_cases z c.involution a hb with hh|rfl
    · exact hh
    · exact (hznot ha).elim
  have hcY:C≤centerIn Y:=inf_le_left
  have hzY:zpowers z≤centerIn Y:=zpowers_le.mpr hzmem
  have hzc:zpowers z≤centralizer (C:Set G):=by
    intro a ha b hb
    exact (hzY ha).2 b (hcY hb).1
  have hspan:centerIn Y=C⊔zpowers z:=by
    apply (eq_of_le_of_card_ge (sup_le hcY hzY) ?_).symm
    rw [card_sup_eq_mul_of_normalizes_of_disjoint C (zpowers z)
      (hzc.trans (Subgroup.centralizer_le_normalizer _)) hdis,hcorecenter,
      Nat.card_zpowers,c.involution,hfour]
  have htz:z∈centralizer (zpowers t:Set G):=by
    rw [htC]
    exact hzc (mem_zpowers z)
  let : IsElementaryAbelian 2 (zpowers t):=IsElementaryAbelian.zpowers_of_pow_eq_one
    (ht ▸ pow_orderOf_eq_one t)
  let : IsElementaryAbelian 2 (zpowers z):=IsElementaryAbelian.zpowers_of_pow_eq_one
    (c.involution ▸ pow_orderOf_eq_one z)
  have hE:IsElementaryAbelian 2 (centerIn Y):=by
    rw [hspan,←htC]
    exact IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr htz)
  let :=hE
  let : Nontrivial (centerIn Y):=Finite.one_lt_card_iff_nontrivial.mp (by rw [hfour];decide)
  exact ⟨t,ht,htmem.2,htC.symm,by rw [hspan,htC],
    ⟨hfour,IsElementaryAbelian.exponent_eq_prime⟩,
    MathieuSourceSetup.ambient_center_eq_mark_of_four c hgen hfour⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
