module
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Elementary two-subgroups moved inside odd-by-SL₂ groups

In odd characteristic every involution of SL₂ is scalar. Hence an elementary
two-subgroup equal to its commutator with another subgroup maps trivially to
SL₂. If the map has an odd-prime-group kernel, the elementary subgroup is
trivial. Neither a splitting nor a faithful action on the odd kernel is needed.

Source application: the Ξ₇ alternative in Aschbacher--Smith 12.5.8(1), p.820.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]

theorem elementary_two_le_center (hF : (2 : F) ≠ 0)
    (A : Subgroup SL(2,F)) [IsElementaryAbelian 2 A] : A ≤ center SL(2,F) := by
  intro x hx
  have hs : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) x hx
  have hdet : (toGL x).det = 1 := by apply Units.ext; exact x.property
  rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF
      (toGL x) (by rw [← map_pow, hs, map_one]) hdet with he | he
  · have hx1 : x = 1 := toGL_injective (by simpa using he)
    exact hx1 ▸ (center SL(2,F)).one_mem
  · have hxn : x = -1 := Subtype.ext (congrArg Units.val he)
    subst x
    exact Subgroup.mem_center_iff.mpr fun y => by simp

variable {Q : Type*} [Group Q]

theorem elementary_fully_moved_eq_bot_of_odd_prime_kernel
    (hF : (2 : F) ≠ 0) {p : ℕ} (hp : Nat.Coprime 2 p)
    (f : Q →* SL(2,F)) (hk : IsPGroup p f.ker)
    (A B : Subgroup Q) [IsElementaryAbelian 2 A] (hm : ⁅A,B⁆ = A) : A = ⊥ := by
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hc : ⁅A.map f, B.map f⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (elementary_two_le_center hF (A.map f)).trans
      (center_le_centralizer (B.map f : Set SL(2,F)))
  rw [← map_commutator, hm, Subgroup.map_eq_bot_iff] at hc
  exact le_bot_iff.mp (fun x hx =>
    disjoint_def.mp ((IsElementaryAbelian.isPGroup 2 A).disjoint_of_coprime hk hp) hx (hc hx))

end Matrix.SpecialLinearGroup
