module

public import Theory.GroupAction.FourGroupCoreAction.Kernel.ActionQuotient
public import Theory.GroupTheory.ConjugateInvolutionGenerators

/-!
# Trivial center of the fixed-core quotient

The two point-core images in the literal quotient `Y/P` have order two,
generate the quotient, and are conjugate inside it. The quotient acts onto
the group of order six induced on the original four-group, so its order is
greater than two. The conjugate-involution argument therefore kills its
center, discharging the dihedral premise in the four-group kernel formula.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.1.14(1), printed p.23.
-/

public section

open Subgroup
namespace FourGroupCorePair
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} {v₁ v₂ : G}

/-- The original fixed-core quotient has trivial center. -/
theorem kernelQuotient_center_eq_bot (h : FourGroupCorePair V v₁ v₂) :
    center h.KernelQuotient = ⊥ := by
  exact Subgroup.center_eq_bot_of_conjugate_order_two_generators
    h.firstQuotientCore h.secondQuotientCore
    h.firstQuotientCore_card h.secondQuotientCore_card
    h.quotientCore_sup h.quotientCores_conjugate
    (lt_of_lt_of_le (by decide : 2 < 6) h.six_le_card_kernelQuotient)

end FourGroupCorePair
