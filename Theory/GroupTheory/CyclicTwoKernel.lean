module
public import Theory.GroupTheory.PGroup.AbelianOmega
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# A cyclic quotient with a kernel of order two

A finite two-group mapping to a cyclic group with kernel of order two is
cyclic when that kernel contains every involution. The central kernel first
forces commutativity; the bound on its first omega subgroup then gives cyclicity.
-/

public section
open Subgroup
namespace IsPGroup
variable {P C : Type*} [Group P] [Finite P] [Group C] [IsCyclic C]
/-- A cyclic image with kernel of order two forces a finite two-group to be
cyclic if every involution lies in that kernel. -/
theorem isCyclic_of_involutions_in_two_kernel
    (hP : IsPGroup 2 P) (f : P →* C) (hk : Nat.card f.ker = 2)
    (hi : ∀ t : P, orderOf t = 2 → f t = 1) : IsCyclic P := by
  let : IsMulCommutative P := f.isMulCommutative_of_isCyclic_of_ker_le_center
    (central_of_normal_card_two f.ker hk)
  apply hP.isCyclic_of_card_omega_one_le_two
  have hO : omega₁ P (p := 2) ≤ f.ker := by
    apply (closure_le f.ker).mpr
    intro t ht
    have ht2 : t^2=1 := by
      change t^(2^1)=1 at ht
      simpa only [pow_one] using ht
    by_cases he : t=1
    · subst t
      exact f.ker.one_mem
    · exact hi t (orderOf_eq_prime ht2 he)
  exact (card_le_of_le hO).trans_eq hk
end IsPGroup

