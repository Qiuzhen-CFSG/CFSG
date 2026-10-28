module
public import Theory.SpecificGroups.BabyMonster.Presentation
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Prime-to-three images of the Baby Monster presentation

In a finite group of order prime to three, the cubic Coxeter relations make
adjacent involutions equal. The remaining Coxeter relations make them commute.
The generated carrier is therefore abelian, hence solvable. This uses only the
actual Y₄₃₃ presentation of Breuer–Magaard–Wilson (2019), §3.1, and does not
require an order or simplicity certificate for that presentation.
-/

public section
namespace BabyMonster

theorem solvable_of_coprime_three [Finite Carrier]
    (h3 : Nat.Coprime 3 (Nat.card Carrier)) : Group.IsSolvable Carrier := by
  have hpair (i j : Generator) : generator i * generator j = generator j * generator i := by
    wlog hij : i < j generalizing i j
    · rcases lt_trichotomy i j with h | rfl | h
      · exact this i j h
      · rfl
      · exact (this j i h).symm
    by_cases he : (i, j) ∈ edges
    · have hp : (generator i * generator j) ^ 3 = 1 := by
        simpa only [coxeterExponent, if_pos he] using generator_pair i j hij
      have hid : generator i * generator j = 1 := by
        apply (powCoprime h3.symm).injective
        change (generator i * generator j) ^ 3 = 1 ^ 3
        simpa only [one_pow] using hp
      exact (mul_eq_one_iff_eq_inv.mp hid).symm ▸ (by simp)
    · have hp : (generator i * generator j) ^ 2 = 1 := by
        simpa only [coxeterExponent, if_neg he] using generator_pair i j hij
      have hi := generator_sq i
      have hj := generator_sq j
      have hinv : (generator i)⁻¹ = generator i := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hi)
      have hjinv : (generator j)⁻¹ = generator j := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hj)
      calc
        generator i * generator j = (generator i * generator j)⁻¹ :=
          (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)).symm
        _ = generator j * generator i := by rw [mul_inv_rev, hinv, hjinv]
  let hc : IsMulCommutative (Subgroup.closure (Set.range generator)) :=
    Subgroup.isMulCommutative_closure (by
      rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
      exact hpair i j)
  have ht : IsMulCommutative (⊤ : Subgroup Carrier) := closure_range_generator ▸ hc
  exact Group.isSolvable_of_comm (fun x y => congrArg Subtype.val
    (ht.is_comm.comm (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup Carrier))
      (⟨y, Subgroup.mem_top y⟩ : (⊤ : Subgroup Carrier))))
end BabyMonster
