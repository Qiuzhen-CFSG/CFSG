module

public import Theory.GroupTheory.QuaternionCentralProductReflectedCubic
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.QuaternionRotation

/-!
# The original reflected cubic has two-core centralizer ⟨z⟩

The actual source reflection interchanges the two SL₂(3) quaternion cores.
Apply the paired cubic action to a nonidentity element of C_X(t).  The
reflected-cubic calculation identifies its fixed two-core with the common
central involution.  This is the local centralizer input to 45.7(1).

The two reflection interchange equalities are earlier45.3 source marks;
no U-line normalizer conclusion is used.
Source: Aschbacher, *Sporadic Groups* (1994),45.7(1),printed p.245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}

theorem reflected_line_core_centralizer (h : IsType z)
    (P : Sylow 3 (centralizer z))
    (m : CubicNormalizer.ReflectedMarking z
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype))
    (htB : h.toCentralizerHypothesis.factorData.leftCore.map
      (MulAut.conj m.t).toMonoidHom = h.toCentralizerHypothesis.factorData.rightCore)
    (htC : h.toCentralizerHypothesis.factorData.rightCore.map
      (MulAut.conj m.t).toMonoidHom = h.toCentralizerHypothesis.factorData.leftCore) :
    core z ⊓ Subgroup.centralizer
      (((P : Subgroup (centralizer z)).map (centralizer z).subtype ⊓
        Subgroup.centralizer ({m.t} : Set G) : Subgroup G) : Set G) = zpowers z := by
  let X := (P : Subgroup (centralizer z)).map (centralizer z).subtype
  let U := X ⊓ Subgroup.centralizer ({m.t} : Set G)
  let d := h.toCentralizerHypothesis.factorData
  have hB : Nonempty (d.leftCore ≃* QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC : Nonempty (d.rightCore ≃* QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi : Nat.card (d.leftCore ⊓ d.rightCore : Subgroup G)=2 := by
    rw [d.core_intersection h.involution,Nat.card_zpowers,h.involution]
  have hcomm : ∀b∈d.leftCore,∀c∈d.rightCore,b*c=c*b := fun b hb c hc =>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) c (pCoreIn_le 2 d.right hc)
  have hself : Subgroup.centralizer (d.leftCore⊔d.rightCore : Subgroup G) ≤ d.leftCore⊔d.rightCore := by
    rw [d.core_span h.involution,h.toCentralizerHypothesis.centralizer_core]
    exact h.toCentralizerHypothesis.line_le_core
  have hnormal : centralizer z ≤ normalizer (d.leftCore⊔d.rightCore : Subgroup G) := by
    rw [d.core_span h.involution]
    exact CentralizerHypothesis.centralizer_normalizes_core
  obtain ⟨actors,ha⟩ := independent_cubics_of_nine_subgroup d.leftCore d.rightCore X
    hB hC hi hcomm hself (h.cubic_sylow_image_card P) ((map_subtype_le _).trans hnormal)
  have hU : Nat.card U=3 := m.common_fixed_card
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G:=U) 3 (hU ▸ dvd_rfl)
  let a : actors.A := ⟨u,ha.symm ▸ u.property.1⟩
  have hane : a≠1 := by
    intro he
    have heG : (u:G)=1 := congrArg (fun a : actors.A => (a:G)) he
    have huone : u=1 := Subtype.ext heG
    simp only [huone,orderOf_one] at hu
    omega
  have htfix : m.t*(a:G)*m.t⁻¹=(a:G) :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp u.property.2).symm
  have hfix := actors.fixed_core_of_factor_swap hB hC hi hcomm m.t htB htC a hane htfix
  rw [d.core_span h.involution,d.core_intersection h.involution] at hfix
  change core z ⊓ Subgroup.centralizer (U : Set G) = zpowers z
  apply le_antisymm
  · rw [←hfix]
    exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr u.property))
  · refine le_inf h.toCentralizerHypothesis.line_le_core ?_
    apply le_centralizer_iff.mp
    apply le_trans (inf_le_left.trans (map_subtype_le _))
    rw [show zpowers z=closure ({z}:Set G) from zpowers_eq_closure z,centralizer_closure]
    exact le_rfl

end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
