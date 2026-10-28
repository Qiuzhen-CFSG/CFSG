module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.CenterAction
public import Theory.GroupTheory.PGroup.ExtraspecialCentralizerDerived

/-!
# The center and class-two structure of the source root product

The ambient extraspecial double-centralizer theorem identifies the centralizer
of the first factor with E. It follows that Z(R)=E and C_G(R)=E. Mutual
normalization of the two factors puts cross commutators in E, while squares in
each factor lie in its original central line. The literal product formula then
puts every square of R in E. No rank or model input is added.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15(2–3) and45.3, pp.29–30,242–243.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

theorem centralizer_leftCore_eq_E (h : IsType z) :
    Subgroup.centralizer (P.leftCore : Set G) = P.E := by
  apply le_antisymm
  · intro x hx
    let H := centralizer z
    let Q := (core z).subgroupOf H
    have hQH : core z ≤ H := core_le_centralizer
    let e : Q ≃* core z := subgroupOfEquivOfLe hQH
    let : Q.Normal := (normal_subgroupOf_iff_le_normalizer hQH).mpr
      CentralizerHypothesis.centralizer_normalizes_core
    let : IsExtraspecial 2 Q := IsExtraspecial.of_mulEquiv e.symm
      h.toCentralizerHypothesis.core_extraspecial
    have hs : Subgroup.centralizer (Q : Set H) ≤ Q := by
      intro a ha
      have hg : (a:G) ∈ Subgroup.centralizer (core z : Set G) := by
        intro b hb
        exact congrArg Subtype.val (ha ⟨b,hQH hb⟩ hb)
      exact h.toCentralizerHypothesis.line_le_core (h.toCentralizerHypothesis.centralizer_core ▸ hg)
    let Z : H := ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩
    let U : H := ⟨P.u,hQH P.mem_core⟩
    have hZ : Z ∈ center H := mem_center_iff.mpr (fun a =>
      Subtype.ext (mem_centralizer_singleton_iff.mp a.property))
    have hd := IsExtraspecial.ambient_involution_double_centralizer_le Q hs Z U
      ((orderOf_coe Z).symm.trans h.involution) hZ P.mem_core
      ((orderOf_coe U).symm.trans (P.u_order h))
    have hxH : x ∈ H := mem_centralizer_singleton_iff.mpr
      (hx z (P.E_le_leftCore h P.z_mem_E)).symm
    have hxD : (⟨x,hxH⟩:H) ∈ Subgroup.centralizer
        (Q ⊓ Subgroup.centralizer ({U} : Set H) : Set H) := by
      intro q hq
      apply Subtype.ext
      exact hx q ⟨hq.1,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hq.2))⟩
    have hE : closure ({Z,U} : Set H) ≤ P.E.comap H.subtype := by
      apply (Subgroup.closure_le _).mpr
      rintro y (rfl | rfl)
      · exact P.z_mem_E
      · exact P.u_mem_E
    exact hE (hd hxD)
  · apply le_centralizer_iff.mpr
    apply le_trans (le_sup_left : P.leftCore ≤ P.R)
    exact (P.R_eq_centralizer_E h).le

theorem centralizer_R_eq_E (h : IsType z) :
    Subgroup.centralizer (P.R : Set G) = P.E := by
  apply le_antisymm
  · exact (Subgroup.centralizer_le (show (P.leftCore : Set G) ⊆ P.R from fun _ hx => mem_sup_left hx)).trans (P.centralizer_leftCore_eq_E h).le
  · exact le_centralizer_iff.mpr (P.R_eq_centralizer_E h).le

theorem R_center (h : IsType z) : (center P.R).map P.R.subtype = P.E := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    rw [← P.centralizer_R_eq_E h]
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  · intro x hx
    refine ⟨⟨x,P.E_le_R h hx⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext ((P.centralizer_R_eq_E h).ge hx y y.property)

omit [Finite G] in
theorem R_normalizes_leftCore (_h : IsType z) :
    P.R ≤ normalizer (P.leftCore : Set G) := by
  apply le_trans _ inf_normalizer_le_normalizer_inf
  apply le_inf
  · exact (P.R_le_double_centralizer.trans inf_le_left).trans
      CentralizerHypothesis.centralizer_normalizes_core
  · exact (P.R_le_double_centralizer.trans inf_le_right).trans (centralizer P.u).le_normalizer

theorem R_normalizes_rightCore (h : IsType z) :
    P.R ≤ normalizer (P.rightCore : Set G) := by
  apply le_trans _ inf_normalizer_le_normalizer_inf
  apply le_inf
  · rw [P.normalizer_conjugateCore h]
    exact P.R_le_double_centralizer.trans inf_le_right
  · exact (P.R_le_double_centralizer.trans inf_le_left).trans (centralizer z).le_normalizer

theorem cross_commutator_le_E (h : IsType z) : ⁅P.leftCore,P.rightCore⁆ ≤ P.E := by
  rw [← P.leftCore_inf_rightCore h]
  apply le_inf
  · exact le_normalizer_iff_commutator_le_left.mp
      (le_sup_right.trans (P.R_normalizes_leftCore h))
  · exact le_normalizer_iff_commutator_le_right.mp
      (le_sup_left.trans (P.R_normalizes_rightCore h))

theorem leftCore_square_mem_E (h : IsType z) (a : G) (ha : a ∈ P.leftCore) : a^2 ∈ P.E := by
  have hm : a^2 ∈ zpowers z := h.toCentralizerHypothesis.core_center ▸
    mem_map_of_mem (core z).subtype (h.toCentralizerHypothesis.coreData.square_mem_center ⟨a,ha.1⟩)
  exact (le_sup_left : zpowers z ≤ P.E) hm

theorem rightCore_square_mem_E (h : IsType z) (a : G) (ha : a ∈ P.rightCore) : a^2 ∈ P.E := by
  let : IsExtraspecial 2 P.conjugateCore := P.conjugateCore_extraspecial h
  have hm : a^2 ∈ zpowers P.u := P.conjugateCore_center h ▸
    mem_map_of_mem P.conjugateCore.subtype (IsExtraspecial.square_mem_center (⟨a,ha.1⟩:P.conjugateCore))
  exact (le_sup_right : zpowers P.u ≤ P.E) hm

/-- Every square in the source root product belongs to the marked central four. -/
theorem R_square_mem_E (h : IsType z) (r : G) (hr : r ∈ P.R) : r^2 ∈ P.E := by
  have hp : r ∈ (P.leftCore : Set G) * (P.rightCore : Set G) := P.R_coe h ▸ hr
  obtain ⟨a,ha,b,hb,rfl⟩ := hp
  have hc : ⁅b,a⁆ ∈ P.E := by
    have hh := commutator_mem_commutator hb ha
    rw [commutator_comm] at hh
    exact P.cross_commutator_le_E h hh
  have haN : a ∈ normalizer (P.E : Set G) := P.core_le_N h ha.1
  have he : (a*b)^2 = (a*⁅b,a⁆*a⁻¹)*(a^2)*(b^2) := by
    simp only [commutatorElement_def,pow_two]
    group
  rw [he]
  exact P.E.mul_mem (P.E.mul_mem ((mem_normalizer_iff.mp haN _).mp hc)
    (P.leftCore_square_mem_E h a ha)) (P.rightCore_square_mem_E h b hb)

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
