module

public import Theory.GroupAction.BinaryFixedLineQuotient
public import Mathlib.GroupTheory.Index

/-!
# The kernel fixing a complete binary flag is a two-group

An automorphism preserving a chain with successive indices two has a
power of two fixing each term pointwise. Inductively, its 2ⁱ-th power fixes
the i-th term; index two puts each displacement in that term, so squaring
fixes the next. This intrinsic proof requires no flag coordinates.

Source application: Aschbacher–Smith, 12.8.9(1), printed p.853.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace BinaryFlagPlaneAction
variable {D : Type*} [Group D] [IsElementaryAbelian 2 D]

theorem flag_power_fixes (F : ℕ → Subgroup D) (hm : Monotone F)
    (n : ℕ) (hc : ∀ i, i ≤ n → Nat.card (F i) = 2 ^ i)
    (a : MulAut D) (ha : ∀ i v, a v ∈ F i ↔ v ∈ F i) :
    ∀ i, i ≤ n → ∀ v ∈ F i, (a ^ (2 ^ i)) v = v := by
  have hp (k i : ℕ) (v : D) : (a ^ k) v ∈ F i ↔ v ∈ F i := by
    induction k with
    | zero => rfl
    | succ k hk => simpa only [pow_succ', MulAut.mul_apply, ha] using hk
  intro i
  induction i with
  | zero =>
    intro _ v hv
    have hf : F 0 = ⊥ := Subgroup.card_eq_one.mp (by simpa using hc 0 (Nat.zero_le n))
    have hv1 : v = 1 := by simpa [hf] using hv
    simp [hv1]
  | succ i ih =>
    intro hin v hv
    have hle : F i ≤ F (i+1) := hm (by omega)
    have hcard : Nat.card ((F i).subgroupOf (F (i+1))) = 2 ^ i :=
      (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans (hc i (by omega))
    have hindex : ((F i).subgroupOf (F (i+1))).index = 2 := by
      have h := ((F i).subgroupOf (F (i+1))).card_mul_index
      rw [hcard, hc (i+1) hin, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^i) h
    let b := a ^ (2 ^ i)
    have hbv : b v ∈ F (i+1) := (hp _ _ _).mpr hv
    have hd : b v * v ∈ F i :=
      (Subgroup.mul_mem_iff_of_index_two hindex
        (a := (⟨b v, hbv⟩ : F (i+1))) (b := ⟨v,hv⟩)).mpr (hp _ _ _)
    have hfix := ih (by omega) _ hd
    change b (b v * v) = b v * v at hfix
    rw [map_mul] at hfix
    have hbb : b (b v) = v := mul_right_cancel (hfix.trans (mul_comm _ _))
    rw [pow_succ, pow_mul, pow_two]
    exact hbb

theorem fullFlag_isPGroup (F : ℕ → Subgroup D) (hm : Monotone F)
    (n : ℕ) (hc : ∀ i, i ≤ n → Nat.card (F i) = 2 ^ i) (hlast : F n = ⊤)
    (A : Subgroup (MulAut D)) (hA : ∀ a ∈ A, ∀ i v, a v ∈ F i ↔ v ∈ F i) :
    IsPGroup 2 A := by
  intro a
  refine ⟨n, ?_⟩
  apply Subtype.ext
  ext v
  exact flag_power_fixes F hm n hc a (hA a a.property) n le_rfl v (by simp [hlast])
end BinaryFlagPlaneAction
