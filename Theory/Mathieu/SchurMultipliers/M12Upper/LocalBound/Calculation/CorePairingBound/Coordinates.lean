module

public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore

/-!
# Coordinates for the first M₁₂ core pairing

The four marked quaternion generators generate the literal embedded core.
We certify the actions of the cubic actor and the second swap on them, and
express the two marked commuting elements in these generators. These finite
permutation equalities are the coordinate input to the invariant pairing
calculation, not a presentation assumption.

Source: the local M₁₂ geometry of Aschbacher–Smith 14.2.21, printed p.988,
used for the upper bound in I.1.3(1), printed p.407.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace Sporadic.Mathieu.SchurMultipliers.M12Upper.CorePairingBound
open M12SmallPair
noncomputable section

def li : core := ⟨leftI, (show leftFactor ≤ core from le_sup_left)
  ⟨QuaternionGroup.a 1, by decide +kernel⟩⟩
def lj : core := ⟨leftJ, (show leftFactor ≤ core from le_sup_left)
  ⟨QuaternionGroup.xa 0, by decide +kernel⟩⟩
def ri : core := ⟨rightI, (show rightFactor ≤ core from le_sup_right)
  ⟨QuaternionGroup.a 1, by decide +kernel⟩⟩
def rj : core := ⟨rightJ, (show rightFactor ≤ core from le_sup_right)
  ⟨QuaternionGroup.xa 0, by decide +kernel⟩⟩
def zz : core := ⟨z, z_mem_core⟩
def vv : core := ⟨v, natural_le_core v_mem_natural⟩
def tt : core := ⟨third, elementary_le_core (subset_closure (by simp))⟩

theorem zz_eq : zz = li ^ 2 := by apply Subtype.ext; decide +kernel
theorem vv_eq : vv = zz * lj * rj := by apply Subtype.ext; decide +kernel
theorem tt_eq : tt = li * lj * ri := by apply Subtype.ext; decide +kernel

theorem cubic_li : firstParabolicCoreAction ⟨cubicActor,cubicActor_mem⟩ li = zz * lj := by
  apply Subtype.ext; decide +kernel
theorem cubic_lj : firstParabolicCoreAction ⟨cubicActor,cubicActor_mem⟩ lj = li * lj := by
  apply Subtype.ext; decide +kernel
theorem cubic_ri : firstParabolicCoreAction ⟨cubicActor,cubicActor_mem⟩ ri = zz * rj := by
  apply Subtype.ext; decide +kernel
theorem cubic_rj : firstParabolicCoreAction ⟨cubicActor,cubicActor_mem⟩ rj = ri * rj := by
  apply Subtype.ext; decide +kernel
theorem swap_li : firstParabolicCoreAction ⟨FirstCore.secondSwap,FirstCore.secondSwap_mem⟩ li = lj := by
  apply Subtype.ext; decide +kernel
theorem swap_lj : firstParabolicCoreAction ⟨FirstCore.secondSwap,FirstCore.secondSwap_mem⟩ lj = zz * li := by
  apply Subtype.ext; decide +kernel
theorem swap_ri : firstParabolicCoreAction ⟨FirstCore.secondSwap,FirstCore.secondSwap_mem⟩ ri = rj := by
  apply Subtype.ext; decide +kernel
theorem swap_rj : firstParabolicCoreAction ⟨FirstCore.secondSwap,FirstCore.secondSwap_mem⟩ rj = zz * ri := by
  apply Subtype.ext; decide +kernel

theorem comm_li_lj : (⁅li,lj⁆ : core) = zz := by
  apply Subtype.ext; decide +kernel
theorem comm_li_rj : (⁅li,rj⁆ : core) = 1 := by
  apply Subtype.ext; decide +kernel
theorem z_ne_one : z ≠ 1 := by decide +kernel

/-- Subgroup generation by the four actual quaternion generators. -/

theorem generators (N : Subgroup core) (hli : li ∈ N) (hlj : lj ∈ N)
    (hri : ri ∈ N) (hrj : rj ∈ N) (x : core) : x ∈ N := by
  obtain ⟨a,b,h⟩ := (mem_core x).mp x.property
  have hl (a : QuaternionGroup 2) : ∃ y : core, y ∈ N ∧ (y : M12) = leftEmbedding a := by
    cases a with
    | a n => exact ⟨li ^ n.val, N.pow_mem hli _, rfl⟩
    | xa n => exact ⟨lj * li ^ n.val, N.mul_mem hlj (N.pow_mem hli _), rfl⟩
  have hr (b : QuaternionGroup 2) : ∃ y : core, y ∈ N ∧ (y : M12) = rightEmbedding b := by
    cases b with
    | a n => exact ⟨ri ^ n.val, N.pow_mem hri _, rfl⟩
    | xa n => exact ⟨rj * ri ^ n.val, N.mul_mem hrj (N.pow_mem hri _), rfl⟩
  obtain ⟨y,hy,hey⟩ := hl a
  obtain ⟨w,hw,hew⟩ := hr b
  have he : y*w = x := Subtype.ext (by change (y : M12)*(w : M12) = x; rw [hey,hew,h])
  rw [← he]
  exact N.mul_mem hy hw

end
end Sporadic.Mathieu.SchurMultipliers.M12Upper.CorePairingBound
