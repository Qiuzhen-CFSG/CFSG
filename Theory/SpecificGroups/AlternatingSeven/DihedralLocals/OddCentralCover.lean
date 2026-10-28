module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# Excluding dihedral twenty-four vertices in odd central covers of A₇

A seven-point permutation of order twelve has cycle type (3,4), so it is
odd. A dihedral group of order twenty-four has central elements of square
one. Consequently its intersection with an odd ambient center is trivial,
and its rotation would retain order twelve in the central quotient A₇.

Source: the A₇ local inspection in Aschbacher--Smith F.6.18, printed p.310.
The cycle-type list below follows inductively from the seven-point bound.
-/

public section
open Equiv Subgroup
namespace AlternatingSeven.DihedralLocals

private def smallTypes : Finset (Multiset ℕ) :=
  {0, {2}, {3}, {4}, {6}, {2, 2}, {2, 3}, {2, 4}, {3, 3}, {3, 4}, {2, 2, 2}, {2, 2, 3}}
private theorem small_types (m : Multiset ℕ) (hs : m.sum ≤ 7)
    (hm : ∀ n ∈ m, 2 ≤ n ∧ n ∣ 12) : m ∈ smallTypes := by
  induction m using Multiset.induction_on with
  | empty => decide
  | @cons a m ih =>
    have ha := hm a (by simp)
    have hb : a + m.sum ≤ 7 := by simpa using hs
    have h := ih (by omega) (fun n hn => hm n (by simp [hn]))
    have ha' : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 6 := by
      have ha7 : a ≤ 7 := by omega
      interval_cases a <;> norm_num at *
    simp only [smallTypes, Finset.mem_insert, Finset.mem_singleton] at h
    rcases ha' with rfl | rfl | rfl | rfl <;>
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hb
    all_goals decide +kernel
/-- No even permutation on seven points has order twelve. -/
theorem orderOf_ne_twelve (g : alternatingGroup (Fin 7)) : orderOf g ≠ 12 := by
  intro ho
  have hc : orderOf (g : Perm (Fin 7)) = 12 := (Subgroup.orderOf_coe g).trans ho
  have hs := small_types (g : Perm (Fin 7)).cycleType
    (by simpa using (g : Perm (Fin 7)).sum_cycleType_le)
    (fun n hn => ⟨Perm.two_le_of_mem_cycleType hn, hc ▸ Perm.dvd_of_mem_cycleType hn⟩)
  have hl : (g : Perm (Fin 7)).cycleType.lcm = 12 := (g : Perm (Fin 7)).lcm_cycleType.trans hc
  have he := Perm.mem_alternatingGroup.mp g.property
  rw [Perm.sign_of_cycleType] at he
  simp only [smallTypes, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs <;>
    simp only [hs] at hl he <;> norm_num [lcm_eq_nat_lcm] at *

private theorem central_dihedral_square_one (x : DihedralGroup 12)
    (hx : ∀ y, y * x = x * y) : x ^ 2 = 1 := by
  have hall : ∀ x : DihedralGroup 12, (∀ y, y * x = x * y) → x ^ 2 = 1 := by
    decide +kernel
  exact hall x hx

/-- A D₂₄ subgroup cannot occur in an odd central cover of the actual A₇. -/
theorem not_dihedralTwentyFour_subgroup_of_odd_center
    {G : Type*} [Group G] [Finite G]
    (eQ : (G ⧸ center G) ≃* alternatingGroup (Fin 7))
    (hZ : Odd (Nat.card (center G))) (H : Subgroup G)
    (eH : H ≃* DihedralGroup 12) : False := by
  let f := eQ.toMonoidHom.comp ((QuotientGroup.mk' (center G)).comp H.subtype)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hcx : (x : G) ∈ center G := by
      apply (QuotientGroup.eq_one_iff (x : G)).mp
      exact eQ.injective (hx.trans (map_one eQ).symm)
    have hd : (eH x) ^ 2 = 1 := central_dihedral_square_one _ (by
      intro y
      obtain ⟨z, rfl⟩ := eH.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg eH (Subtype.ext ((mem_center_iff.mp hcx) z)))
    have hx2 : x ^ 2 = 1 := eH.injective (by simpa using hd)
    let z : center G := ⟨x, hcx⟩
    have hz2 : z ^ 2 = 1 := Subtype.ext (congrArg H.subtype hx2)
    have hz1 : z = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hZ.coprime_two_left
        (orderOf_dvd_of_pow_eq_one hz2) (orderOf_dvd_natCard z))
    exact Subtype.ext (congrArg (center G).subtype hz1)
  let x : H := eH.symm (DihedralGroup.r 1)
  apply orderOf_ne_twelve (f x)
  rw [orderOf_injective f hf, ← eH.orderOf_eq x]
  simp [x, DihedralGroup.orderOf_r_one]

end AlternatingSeven.DihedralLocals
