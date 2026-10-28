module

public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.PGroup.ExtraspecialCentralizer
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct
public import Theory.GroupTheory.SpecificGroups.QuaternionEightInvolution

/-!
# Ambient commutators of quaternion subgroups in critical subgroups

In the central-four, no-normal-eight setting, ambient commutators with an
order-at-most-four element of a critical subgroup lie in the central first
omega. The square of the element is an ambient-central involution, so the
critical commutator identity makes the commutator itself an involution.

If a quaternion subgroup inside the critical subgroup is normal in the
ambient group, its ambient commutators lie both in that subgroup and in the
critical center, hence in its own center. Extraspecial commutator duality
then gives a centralizer supplement. Normality is an explicit hypothesis;
an arbitrary internal quaternion supplement need not be ambient-normal.

Source: the ambient splitting step of MacWilliams, Trans. AMS 150 (1970),
§3(iv), pp.367–368, together with Thompson's critical-subgroup conditions.
-/

open Subgroup
open scoped commutatorElement
open scoped IsMulCommutative

namespace IsCriticalPSubgroup

/-- Ambient displacement of a critical element of order dividing four lies in central first omega. -/
public theorem commutator_mem_omega_center_of_fourth_power_eq_one
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (g x : P) (hx : x ∈ C) (hx4 : x ^ 4 = 1) :
    ⁅g, x⁆ ∈ (omega₁ (center P) (p := 2)).map (center P).subtype := by
  have hx2 : x ^ 2 ∈ center P := by
    apply map_subtype_le (omega₁ (center P) (p := 2))
    apply hC.mem_omega_center_of_square_eq_one hno hZ (C.pow_mem hx 2)
    simpa only [← pow_mul] using hx4
  obtain ⟨z, hz, he⟩ := hC.commutator_le
    (commutator_mem_commutator (mem_top g) hx)
  have hcomm : x * ⁅g, x⁆ = ⁅g, x⁆ * x := by
    rw [← he]
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩)
  have hpow : ⁅g, x⁆ ^ 2 = 1 := by
    have hh : ⁅g, x ^ 2⁆ = ⁅g, x⁆ ^ 2 := by
      rw [pow_two, commutatorElement_mul_right_eq_mul_conj, mul_assoc _ x, hcomm,
        ← mul_assoc, mul_inv_cancel_right, pow_two]
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx2 g)] at hh
    exact hh.symm
  exact hC.mem_omega_center_of_square_eq_one hno hZ (he ▸ z.property) hpow

/-- A normal extraspecial binary subgroup inside a critical subgroup has a centralizer supplement. -/
public theorem sup_centralizer_eq_top_of_normal_extraspecial
    {P : Type*} [Group P] {p : ℕ} {C : Subgroup P}
    (hC : IsCriticalPSubgroup p C) (Q : Subgroup P) [Finite Q]
    [Q.Normal] [IsExtraspecial 2 Q] (hQC : Q ≤ C) :
    Q ⊔ centralizer (Q : Set P) = ⊤ := by
  apply sup_centralizer_eq_top_of_extraspecial_two Q
  rw [map_center_subtype_eq_inf_centralizer]
  refine le_inf (commutator_le_right ⊤ Q) ?_
  have hCZ : (center C).map C.subtype ≤ centralizer (C : Set P) := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  exact (commutator_mono le_rfl hQC).trans
    (hC.commutator_le.trans (hCZ.trans (centralizer_le hQC)))

/-- A normal quaternion eight inside a critical subgroup has a centralizer supplement. -/
public theorem sup_centralizer_eq_top_of_normal_quaternion
    {P : Type*} [Group P] [Finite P] {C : Subgroup P}
    (hC : IsCriticalPSubgroup 2 C) (Q : Subgroup P) [Q.Normal]
    (hQC : Q ≤ C) (e : Q ≃* QuaternionGroup 2) :
    Q ⊔ centralizer (Q : Set P) = ⊤ := by
  have hcard : Nat.card Q = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hn : ¬ IsMulCommutative Q := by
    intro hc
    let : IsMulCommutative Q := hc
    have hh := mul_comm (e.symm (QuaternionGroup.a 1)) (e.symm (QuaternionGroup.xa 0))
    have ht := congrArg e hh
    simp only [map_mul, e.apply_symm_apply] at ht
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1) ht
  let : IsExtraspecial 2 Q := IsExtraspecial.of_noncommutative_card_eight hcard hn
  exact hC.sup_centralizer_eq_top_of_normal_extraspecial Q hQC

end IsCriticalPSubgroup
