module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.WeakClosure
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.LocalPlacement
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStarFull
public import Theory.GroupTheory.InvolutionFusionCover
public import Theory.GroupTheory.PGroup.UniqueInvolution

/-!
# Thompson transfer and the cyclic core center in 13.5.16

The original S₆ quotient gives |T|=256 and |T∩L|=128. Thompson transfer
therefore puts every ambient involution in the original point class.
Burnside fusion fixes that point in Z(Q_H), so its order-four center has a
unique involution and is cyclic. Its generators square to the original
point; distinct conjugates outside H are disjoint. The original M/L
quotient has order two, and each order-four center generator lies outside
L. These are the source inputs to the final abelian plane span.

Source: Aschbacher–Smith, Proposition 13.5.16, printed pp.921–922.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
  (b : CFSG.Quasithin.Chapter13.Section05.NormalBranch.Conclusions D M 6 g)
  (hS : Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)))

include d b hS in
theorem extension_sylow_card : Nat.card D.T = 256 := by
  have hV : Nat.card (pCore 2 M) = 16 := by
    have hc := congrArg (fun X : Subgroup G => Nat.card X) b.seven.2
    change Nat.card D.V = Nat.card ((pCore 2 M).map M.subtype) at hc
    rw [card_map_of_injective M.subtype_injective, ReturningPlane.module_card d] at hc
    exact hc.symm
  have hM : Nat.card M = 11520 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 M),hV,
      Nat.card_congr hS.some.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  have hTM : (D.T : Subgroup G) ≤ M := by
    rw [d.local_normalizer]
    exact d.normalizes_L
  let P := D.T.subtype hTM
  have hc : Nat.card P = 256 := by
    rw [P.card_eq_multiplicity,hM]
    decide +kernel
  have he : Nat.card P = Nat.card D.T := Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv
  exact he.symm.trans hc

include d h e hseed hn hU b hS in
theorem local_sylow_index_two : (D.L.subgroupOf (D.T : Subgroup G)).index = 2 := by
  have hQ : D.LT.pCoreIn 2 = D.V := by
    rw [←b.seven.1]
    exact b.seven.2.symm
  have hc := SourceStarFull.local_sylow_card d h e hseed hn hU hQ
  have hcard : Nat.card (D.L.subgroupOf (D.T : Subgroup G)) = 128 := by
    rw [←card_map_of_injective (K := D.L.subgroupOf (D.T : Subgroup G))
      (D.T : Subgroup G).subtype_injective,subgroupOf_map_subtype,inf_comm]
    exact hc
  have hmul := (D.L.subgroupOf (D.T : Subgroup G)).card_mul_index
  rw [hcard,extension_sylow_card d b hS] at hmul
  omega

include d h e hseed hn hU b hS in
theorem ambient_involutions_fused
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (x : G) (hx : orderOf x = 2) : IsConj z x := by
  let : IsSimpleGroup G := d.counterexample.qtke.simple
  obtain ⟨t,ht,hxt⟩ := D.T.exists_isConj_mem_of_index_two_ambient
    (index_ne_two_of_nonabelian_simple d.counterexample.qtke.nonabelian)
    (D.L.subgroupOf (D.T : Subgroup G))
    (local_sylow_index_two d h e hseed hn hU b hS) x hx
  have ht2 : orderOf (t : G) = 2 := by
    obtain ⟨a,ha⟩ := isConj_iff.mp hxt
    rw [←ha]
    exact ((MulAut.conj a).orderOf_eq x).trans hx
  exact (LocalPlacement.local_sylow_involutions_fused d h e hseed hn hU b
    z hz hz1 t ⟨t.property,ht⟩ ht2).trans hxt.symm

include d h e hseed hn hU b hS in
theorem core_center_cyclic :
    IsCyclic (center D.QH) := by
  obtain ⟨z,hz,hz1⟩ := D.V₁.bot_or_exists_ne_one.resolve_left (by
    intro he
    have hc := h.point_card
    simp [he] at hc)
  have hzQ : z ∈ D.QH := h.UH_le_QH (le_conjugateSpanBy _ _ (h.point_lt.le hz))
  have hzC : (⟨z,hzQ⟩ : D.QH) ∈ center D.QH := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (((h.H_centralizes (h.QH_le_T.trans h.T_le_H x.property)) z hz).symm)
  let zC : center D.QH := ⟨⟨z,hzQ⟩,hzC⟩
  have hz2 : orderOf zC = 2 := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
    exact (TypeU4.point_generator h z hz hz1).1
  have hc := extension_center_card d h e hseed hn hU b hS
  apply (IsPGroup.of_card (p := 2) (n := 2) (by simpa using hc)).isCyclic_of_unique_involution_of_isMulCommutative
  refine ⟨zC,hz2,?_⟩
  intro x hx
  apply Subtype.ext
  apply Subtype.ext
  exact point_fixed_in_core_center d h e hseed hn hU b hS hz (mem_map_of_mem D.QH.subtype x.property)
    (ambient_involutions_fused d h e hseed hn hU b hS z hz hz1 x.val.val (by rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe] at hx; exact hx))

include d h e hseed hn hU b hS in
theorem exists_center_generator
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1) :
    ∃ j : G, orderOf j = 4 ∧ j ^ 2 = z ∧
      (center D.QH).map D.QH.subtype = zpowers j := by
  have hc := core_center_cyclic d h e hseed hn hU b hS
  let : IsCyclic (center D.QH) := hc
  obtain ⟨j,hj⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hc
  rw [extension_center_card d h e hseed hn hU b hS] at hj
  have hzQ : z ∈ D.QH := h.UH_le_QH (le_conjugateSpanBy _ _ (h.point_lt.le hz))
  have hzC : (⟨z,hzQ⟩ : D.QH) ∈ center D.QH := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (((h.H_centralizes (h.QH_le_T.trans h.T_le_H x.property)) z hz).symm)
  let zC : center D.QH := ⟨⟨z,hzQ⟩,hzC⟩
  have hz2 : orderOf zC = 2 := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe]
    exact (TypeU4.point_generator h z hz hz1).1
  have hjs : orderOf (j ^ 2) = 2 := by rw [orderOf_pow,hj]; decide
  have hsq : j ^ 2 = zC := IsCyclic.eq_of_orderOf_eq_two hjs hz2
  have hjG : orderOf j.val.val = 4 := by
    rw [←Subgroup.orderOf_coe,←Subgroup.orderOf_coe] at hj
    exact hj
  refine ⟨j.val.val,hjG,congrArg (fun x : center D.QH => x.val.val) hsq,?_⟩
  apply (eq_of_le_of_card_ge (zpowers_le.mpr
    (mem_map_of_mem D.QH.subtype j.property)) ?_).symm
  rw [card_map_of_injective D.QH.subtype_injective,
    extension_center_card d h e hseed hn hU b hS,Nat.card_zpowers,
    orderOf_injective D.QH.subtype D.QH.subtype_injective,Subgroup.orderOf_coe,hj]



include d h e hseed hn hU b hS in
theorem center_conjugate_disjoint
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (y : G) (hy : y ∉ D.H) :
    Disjoint ((center D.QH).map D.QH.subtype)
      (((center D.QH).map D.QH.subtype).conjBy y) := by
  let C := (center D.QH).map D.QH.subtype
  have hc := core_center_cyclic d h e hseed hn hU b hS
  let : IsCyclic (center D.QH) := hc
  let a : center D.QH ≃* C := (center D.QH).equivMapOfInjective D.QH.subtype D.QH.subtype_injective
  let : IsCyclic C := a.isCyclic.mp hc
  have hQp : IsPGroup 2 D.QH := isPGroup_pCoreIn 2 D.H
  have hCp : IsPGroup 2 C := (hQp.to_subgroup (center D.QH)).of_equiv a
  have hzQ : z ∈ D.QH := h.UH_le_QH (le_conjugateSpanBy _ _ (h.point_lt.le hz))
  have hzC : z ∈ C := by
    refine mem_map_of_mem D.QH.subtype (show (⟨z,hzQ⟩ : D.QH) ∈ center D.QH from ?_)
    exact mem_center_iff.mpr (fun x => Subtype.ext
      (((h.H_centralizes (h.QH_le_T.trans h.T_le_H x.property)) z hz).symm))
  have hz2 := (TypeU4.point_generator h z hz hz1).1
  have hyz : MulAut.conj y z ≠ z := by
    intro he
    apply hy
    rw [←TypeU4.centralizer_eq h b z hz hz1]
    exact mem_centralizer_singleton_iff.mpr (by
      change y * z * y⁻¹ = z at he
      have hh := congrArg (fun x => x * y) he
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh)
  have hzout : z ∉ C.conjBy y := by
    intro hzCy
    let aY := C.equivMapOfInjective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective
    let : IsCyclic (C.conjBy y) := aY.isCyclic.mp inferInstance
    have hnew : MulAut.conj y z ∈ C.conjBy y := mem_map_of_mem _ hzC
    have he := IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨z,hzCy⟩ : C.conjBy y))
      (y := ⟨MulAut.conj y z,hnew⟩)
      (by simpa using hz2)
      (by rw [←Subgroup.orderOf_coe]; exact ((MulAut.conj y).orderOf_eq z).trans hz2)
    exact hyz (congrArg Subtype.val he).symm
  apply Subgroup.disjoint_def.mpr
  intro x hxC hxCy
  by_contra hx1
  have hJ : (C.conjBy y).subgroupOf C ≠ ⊥ := by
    intro hj
    have hm : (⟨x,hxC⟩ : C) ∈ (C.conjBy y).subgroupOf C := hxCy
    rw [hj,mem_bot] at hm
    exact hx1 (congrArg Subtype.val hm)
  exact hzout (hCp.involution_mem_subgroup_of_ne_bot
    (x := (⟨z,hzC⟩ : C)) (by simpa using hz2) _ hJ)



include d h e hseed hn hU b hS in
theorem local_index_two_in_maximal : (D.L.subgroupOf M).index = 2 := by
  have hQ : D.LT.pCoreIn 2 = D.V := by
    rw [←b.seven.1]
    exact b.seven.2.symm
  have hVL := SourceCoreIntersection.local_core_eq_module d h e hseed hn hU hQ
  have hLcore : Nat.card (pCore 2 D.L) = 16 := by
    have hc := congrArg (fun X : Subgroup G => Nat.card X) hVL
    change Nat.card ((pCore 2 D.L).map D.L.subtype) = Nat.card D.V at hc
    rw [card_map_of_injective D.L.subtype_injective,ReturningPlane.module_card d] at hc
    exact hc
  have hMcore : Nat.card (pCore 2 M) = 16 := by
    have hc := congrArg (fun X : Subgroup G => Nat.card X) b.seven.2
    change Nat.card D.V = Nat.card ((pCore 2 M).map M.subtype) at hc
    rw [card_map_of_injective M.subtype_injective,ReturningPlane.module_card d] at hc
    exact hc.symm
  have hL : Nat.card D.L = 5760 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D.L),hLcore,
      Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hM : Nat.card M = 11520 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 M),hMcore,
      Nat.card_congr hS.some.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  have hLM : D.L ≤ M := by rw [d.local_normalizer]; exact D.L.le_normalizer
  have hcard : Nat.card (D.L.subgroupOf M) = 5760 :=
    (Nat.card_congr (subgroupOfEquivOfLe hLM).toEquiv).trans hL
  have hi := (D.L.subgroupOf M).card_mul_index
  rw [hcard,hM] at hi
  omega

include d h e hseed hn hU b in
theorem center_order_four_not_mem_local (j : G)
    (hj : j ∈ (center D.QH).map D.QH.subtype) (hj4 : orderOf j = 4) : j ∉ D.L := by
  have hQ : D.LT.pCoreIn 2 = D.V := by
    rw [←b.seven.1]
    exact b.seven.2.symm
  intro hjL
  rw [core_center_image d h e hseed hn hU b] at hj
  have hjpoint := (SourceCoreIntersection.local_centralizer_inf_local
    d h e hseed hn hU hQ).le ⟨hj,hjL⟩
  have hd := D.V₁.orderOf_dvd_natCard hjpoint
  rw [hj4,h.point_card] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
