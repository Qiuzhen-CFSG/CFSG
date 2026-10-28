module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The actual commutator pairing of a group of class two

When the central quotient is abelian, commutators descend to a multiplicative
pairing on the central quotient with values in the original center. The
pairing is alternating and nondegenerate. No basis or generator of the center
is chosen, so group equivalences and similitudes retain their literal maps.

This is the standard commutator-space construction for extraspecial groups,
used in Aschbacher, *Sporadic Groups* (1994), 45.8 and 45.11, pp.246–248.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory.CentralQuotient
variable {D : Type*} [Group D] [IsMulCommutative (D ⧸ center D)]

theorem commutator_mem_center (x y : D) : ⁅x,y⁆ ∈ center D := by
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (center D)) ⁅x,y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private def row (x : D) : D →* center D where
  toFun y := ⟨⁅x,y⁆,commutator_mem_center x y⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅x,a*b⁆ = ⁅x,a⁆*⁅x,b⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅x,a⁆ a ⁅x,b⁆,mem_center_iff.mp (commutator_mem_center x b) a]
    simp only [←mul_assoc,mul_inv_cancel_right]

private theorem center_le_ker_row (x : D) : center D ≤ (row x).ker := by
  intro c hc
  apply Subtype.ext
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hc x)

private def quotientRow : D →* ((D ⧸ center D) →* center D) where
  toFun x := QuotientGroup.lift (center D) (row x) (center_le_ker_row x)
  map_one' := by
    apply MonoidHom.ext
    intro q
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center D) q
    apply Subtype.ext
    change ⁅(1:D),y⁆=1
    simp
  map_mul' x y := by
    apply MonoidHom.ext
    intro q
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (center D) q
    apply Subtype.ext
    change ⁅x*y,z⁆ = ⁅x,z⁆*⁅y,z⁆
    rw [commutatorElement_mul_left_eq_conj_mul,
      mem_center_iff.mp (commutator_mem_center y z) x]
    simp only [mul_inv_cancel_right]
    exact (mem_center_iff.mp (commutator_mem_center y z) ⁅x,z⁆).symm

def pairing : (D ⧸ center D) →* ((D ⧸ center D) →* center D) :=
  QuotientGroup.lift (center D) quotientRow (by
    intro x hx
    apply MonoidHom.ext
    intro q
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center D) q
    apply Subtype.ext
    change ⁅x,y⁆=1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx y).symm)

@[simp] theorem pairing_mk_mk (x y : D) :
    (pairing (QuotientGroup.mk' (center D) x) (QuotientGroup.mk' (center D) y) : D) = ⁅x,y⁆ := by rfl

theorem pairing_self (q : D ⧸ center D) : pairing q q = 1 := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center D) q
  apply Subtype.ext
  change (pairing (QuotientGroup.mk' (center D) x) (QuotientGroup.mk' (center D) x) : D)=1
  rw [pairing_mk_mk]
  simp

theorem pairing_nondegenerate (q : D ⧸ center D) (hq : ∀ r, pairing q r = 1) : q = 1 := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center D) q
  apply (QuotientGroup.eq_one_iff _).mpr
  apply mem_center_iff.mpr
  intro y
  have hh := congrArg Subtype.val (hq (QuotientGroup.mk' (center D) y))
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
end Theory.GroupTheory.CentralQuotient

