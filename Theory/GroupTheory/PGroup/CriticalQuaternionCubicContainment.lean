module

public import Theory.GroupTheory.PGroup.CriticalQuaternionCenterCentralizer
public import Theory.GroupAction.CoprimeSmallQuotient
public import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Ambient containment for a cubic critical-quaternion action

The centralizer M of the critical center contains C with index at most two.
An automorphism fixing that center pointwise has all its displacements in M.
The induced action on M/C is trivial; coprime commutator idempotence therefore
puts the ambient action commutator in C.

Source: MacWilliams, Trans. AMS 150 (1970), §3(ii)–(iv), pp.366–368.
-/

open Subgroup

namespace IsCriticalPSubgroup

/-- A cubic automorphism fixing the center of a critical quaternion extension
has its entire ambient action commutator in the critical subgroup. -/
public theorem commutatorAction_le_of_quaternion_supplement
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    {C : Subgroup P} (hC : IsCriticalPSubgroup 2 C)
    (hnonab : ¬ IsMulCommutative C)
    (hbad : ¬ IsElementaryAbelian 2 (center C))
    (R : Subgroup C) (eR : R ≃* QuaternionGroup 2)
    (hRgen : R ⊔ center C = ⊤)
    (a : MulAut P) (ha : orderOf a = 3)
    (hfix : ∀ z ∈ (center C).map C.subtype, a z = z) :
    commutatorAction (zpowers a) P ≤ C := by
  let A := zpowers a
  let Z := (center C).map C.subtype
  let M := centralizer (Z : Set P)
  let : C.Characteristic := hC.characteristic
  let : Z.Characteristic := inferInstance
  let : M.Characteristic := inferInstance
  let : IsInvariant A P C := isInvariant_of_characteristic C
  let : IsInvariant A P M := isInvariant_of_characteristic M
  have hfixA : ∀ b : A, ∀ z ∈ Z, b • z = z := by
    intro b z hz
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp b.property
    change (b : MulAut P) • z = z
    rw [← hn]
    exact MulAction.mem_fixedBy_zpow (MulAction.mem_fixedBy.mpr (hfix z hz)) n
  have hcontain : commutatorAction A P ≤ M :=
    commutatorAction_le_centralizer_of_fixed_normal Z hfixA
  have hindex : C.relIndex M ≤ 2 :=
    hC.relIndex_center_centralizer_le_two_of_quaternion_supplement
      hP hno hZ hnonab hbad R eR hRgen
  have hcop : Nat.Coprime (Nat.card A) (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [show Nat.card A = 3 from (Nat.card_zpowers a).trans ha, hn]
    exact Nat.Coprime.pow_right n (by decide)
  let : Group.IsNilpotent P := hP.isNilpotent
  exact commutatorAction_le_of_coprime_of_relIndex_le_two C M
    inferInstance hcop hindex hcontain

end IsCriticalPSubgroup
