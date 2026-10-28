module

public import Theory.SpecificGroups.SymmetricFourSmallQuotient

/-!
# The surviving kernel test for the S₄ Coxeter presentation

The normal Klein four of `S₄` lies in every nontrivial normal subgroup.  Its
standard double transposition is the product of the two end transpositions in
an `A₃` chain.  Consequently a homomorphism kills no such product precisely
when it has trivial kernel.  This is the small-degree kernel step used by the
`A₃` recognition, where the corresponding degree-at-least-five theorem is not
available.
-/

public section
namespace Theory.SpecificGroups.SymmetricFourKernel

open Theory.SpecificGroups.SymmetricFour
open Theory.SpecificGroups.SymmetricSix.DuadCalculation

variable {G : Type*} [Group G]

/-- Distinct images of the two disjoint endpoint swaps force an `S₄` map to be
injective. -/
public theorem injective_of_swap_ne (f : Equiv.Perm (Fin 4) →* G)
    (h : f (Equiv.swap 0 1) ≠ f (Equiv.swap 2 3)) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  by_contra hk
  have hcore : pCore 2 Four ≤ f.ker :=
    twoCore_le_normal_of_ne_bot f.ker hk
  have hdouble : Equiv.swap 0 1 * Equiv.swap 2 3 ∈ pCore 2 Four := by
    rw [← core_eq]
    apply (core_mem_iff _).2
    constructor <;> decide +kernel
  have hz : f (Equiv.swap 0 1 * Equiv.swap 2 3) = 1 := by
    exact hcore hdouble
  have hz' : f (Equiv.swap 0 1) * f (Equiv.swap 2 3) = 1 := by
    simpa only [map_mul] using hz
  have hb : f (Equiv.swap 2 3) * f (Equiv.swap 2 3) = 1 := by
    rw [← map_mul]
    norm_num
  apply h
  calc
    f (Equiv.swap 0 1) = f (Equiv.swap 0 1) * 1 := (mul_one _).symm
    _ = f (Equiv.swap 0 1) *
        (f (Equiv.swap 2 3) * f (Equiv.swap 2 3)) := by rw [hb]
    _ = (f (Equiv.swap 0 1) * f (Equiv.swap 2 3)) *
        f (Equiv.swap 2 3) := by ac_rfl
    _ = 1 * f (Equiv.swap 2 3) := by rw [hz']
    _ = f (Equiv.swap 2 3) := one_mul _

end Theory.SpecificGroups.SymmetricFourKernel
