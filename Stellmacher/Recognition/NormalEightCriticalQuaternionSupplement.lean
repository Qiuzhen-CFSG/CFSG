module

public import Theory.GroupTheory.PGroup.CriticalQuaternionCentralizer
public import Theory.GroupAction.CoprimeCommutatorContainment
public import Theory.GroupTheory.PGroup.CriticalQuaternionCubicContainment
public import Theory.GroupTheory.PGroup.CriticalQuaternionCubicAction
public import Theory.GroupTheory.PGroup.QuaternionCentralProductCubicCommutator
public import Theory.GroupTheory.SylowPGroupAutomizer
public import Mathlib.GroupTheory.Sylow

/-!
# Assembly of an ambient quaternion supplement

An internal quaternion supplement to a nonelementary critical center gives
an ambient quaternion subgroup whose product with its centralizer is the
full Sylow subgroup. The nontrivial normalizer action detects a cubic
automorphism fixing the critical center. The centralizer of that center has
relative index at most two over the critical subgroup, which puts the full
cubic commutator in the critical subgroup. Its intrinsic commutator is
quaternion; coprime commutator idempotence makes its ambient image normal.
Extraspecial commutator duality then supplies the centralizer supplement.

The first two adapters retain their original interfaces for an explicit
normal quaternion witness or an explicitly contained coprime commutator.
The final theorem discharges these obligations from the internal witness.
Source: MacWilliams, Trans. AMS 150 (1970), §3(iv), pp.367–368.
-/

open Subgroup

namespace Sylow

/-- A normal quaternion witness inside a critical subgroup supplies the
ambient centralizer supplement. -/
public theorem quaternion_supplement_of_normal_internal
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C)
    (R : Subgroup C) (eR : R ≃* QuaternionGroup 2)
    (hRn : (R.map C.subtype).Normal) :
    ∃ Q : Subgroup S, Q ≤ C ∧ Nonempty (Q ≃* QuaternionGroup 2) ∧
      Q ⊔ centralizer (Q : Set S) = ⊤ := by
  let Q := R.map C.subtype
  let : Q.Normal := hRn
  let e : Q ≃* QuaternionGroup 2 :=
    (R.equivMapOfInjective C.subtype C.subtype_injective).symm.trans eR
  exact ⟨Q, map_subtype_le R, ⟨e⟩,
    hC.sup_centralizer_eq_top_of_normal_quaternion Q (map_subtype_le R) e⟩

/-- A quaternion internal action commutator supplies the ambient supplement
once the full coprime commutator is contained in the critical subgroup. -/
public theorem quaternion_supplement_of_coprime_commutator
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C)
    {A : Type*} [Group A] [Finite A] [MulDistribMulAction A S]
    [IsInvariant A S C]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card S))
    (hcontain : commutatorAction A S ≤ C)
    (e : commutatorAction A C ≃* QuaternionGroup 2) :
    ∃ Q : Subgroup S, Q ≤ C ∧ Nonempty (Q ≃* QuaternionGroup 2) ∧
      Q ⊔ centralizer (Q : Set S) = ⊤ := by
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  exact S.quaternion_supplement_of_normal_internal hC (commutatorAction A C) e
    (commutatorAction_map_normal_of_coprime_of_le C inferInstance hcop hcontain)

/-- An internal quaternion supplement to a nonelementary critical center
extends to a quaternion centralizer supplement in the full Sylow subgroup. -/
public theorem quaternion_supplement_of_internal
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    {C : Subgroup S} (hC : IsCriticalPSubgroup 2 C)
    (hCnonab : ¬ IsMulCommutative C)
    (hbad : ¬ IsElementaryAbelian 2 (center C))
    (R : Subgroup C) (eR : R ≃* QuaternionGroup 2)
    (hRgen : R ⊔ center C = ⊤) :
    ∃ Q : Subgroup S, Q ≤ C ∧ Nonempty (Q ≃* QuaternionGroup 2) ∧
      Q ⊔ centralizer (Q : Set S) = ⊤ := by
  obtain ⟨a, ha, hfix, c, hc⟩ :=
    hC.exists_order_three_fixing_center_of_quaternion_supplement S.isPGroup'
      (S.not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer hnorm)
      hno hZ hbad R eR hRgen
  let A := zpowers a
  let : C.Characteristic := hC.characteristic
  let : IsInvariant A S C := isInvariant_of_characteristic C
  have hA : Nat.card A = 3 := (Nat.card_zpowers a).trans ha
  have hfixA : ∀ b : A, ∀ z ∈ (center C).map C.subtype, b • z = z := by
    intro b z hz
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp b.property
    change (b : MulAut S) • z = z
    rw [← hn]
    exact MulAction.mem_fixedBy_zpow (MulAction.mem_fixedBy.mpr (hfix z hz)) n
  have hfixC : ∀ b : A, ∀ z : center C, b • (z : C) = (z : C) := by
    intro b z
    apply Subtype.ext
    exact hfixA b z (mem_map_of_mem C.subtype z.property)
  have hmove : ∃ b : A, ∃ x : C, (b • x) * x⁻¹ ∉ center C := by
    refine ⟨⟨a, mem_zpowers a⟩, c, ?_⟩
    intro hh
    exact hc (mem_map_of_mem C.subtype hh)
  obtain ⟨e⟩ := (S.isPGroup'.to_subgroup C).nonempty_commutatorAction_equiv_quaternion_of_quaternion_supplement
      R eR hRgen hA hfixC hmove
  have hcontain : commutatorAction A S ≤ C :=
    hC.commutatorAction_le_of_quaternion_supplement S.isPGroup' hno hZ
      hCnonab hbad R eR hRgen a ha hfix
  have hcop : Nat.Coprime (Nat.card A) (Nat.card S) := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hA, hn]
    exact Nat.Coprime.pow_right n (by decide)
  exact S.quaternion_supplement_of_coprime_commutator hC hcop hcontain e

end Sylow
