module

public import Theory.SpecificGroups.G2.MultiplierThree.PrimeSupport

/-!
# Recognizing the exceptional G₂(3) multiplier from independent bounds

An upper bound of three and a matching lower bound identify the literal
universal kernel with the cyclic group of order three. The lower bound may
be supplied by a central derived element of order three in any extension,
or by a nonsplit central triple extension. The imported reduction proves
that these witnesses give divisibility of the canonical kernel order.
Transfer already excludes every prime except two and three; the upper
bound thus reduces to excluding divisibility by two and by nine.

These are conditional assembly theorems for Aschbacher–Smith I.1.4(2),
printed p.408 (PDF p.419), and the G₂(3) row of GLS3 Tables 6.1.2–6.1.3.
The upper-bound proof and construction of an extension witness are still
required before the unconditional multiplier row can be asserted.
-/

namespace Atlas.G2.FiniteCover.MultiplierThree

/-- Prime order determines the group structure of the canonical kernel. -/
public theorem kernel_equiv_three_of_bounds
    (hupper : Nat.card (Kernel (ZMod 3)) ≤ 3)
    (hlower : 3 ≤ Nat.card (Kernel (ZMod 3))) :
    Nonempty (Kernel (ZMod 3) ≃* Multiplicative (ZMod 3)) :=
  ⟨mulEquivOfPrimeCardEq (Nat.le_antisymm hupper hlower) (by simp)⟩

/-- Combine the two outstanding primary exclusions with a cubic lower bound. -/
public theorem kernel_equiv_three_of_primary_bounds
    (h2 : ¬ 2 ∣ Nat.card (Kernel (ZMod 3)))
    (h9 : ¬ 9 ∣ Nat.card (Kernel (ZMod 3)))
    (h3 : 3 ∣ Nat.card (Kernel (ZMod 3))) :
    Nonempty (Kernel (ZMod 3) ≃* Multiplicative (ZMod 3)) :=
  kernel_equiv_three_of_bounds (kernel_card_le_three_of_not_two_not_nine h2 h9)
    (Nat.le_of_dvd Nat.card_pos h3)

universe u
variable {E : Type u} [Group E]

/-- Apply the order-three derived-kernel witness to the actual octonion base.
The proposed extension need not itself be perfect or universal. -/
public theorem kernel_equiv_three_of_central_extension
    (π : E →* Model (ZMod 3)) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (z : E)
    (hz : z ∈ π.ker) (hd : z ∈ commutator E) (ho : orderOf z = 3)
    (hupper : Nat.card (Kernel (ZMod 3)) ≤ 3) :
    Nonempty (Kernel (ZMod 3) ≃* Multiplicative (ZMod 3)) :=
  kernel_equiv_three_of_bounds hupper (Nat.le_of_dvd Nat.card_pos
    (three_dvd_kernel_card_of_central_extension π hπ hc z hz hd ho))

/-- Apply a nonsplit triple extension to the same canonical universal kernel.
The independent upper bound remains explicit. -/
public theorem kernel_equiv_three_of_nonsplit_extension
    (π : E →* Model (ZMod 3)) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (hk : Nat.card π.ker = 3)
    (hns : ¬ ∃ s : Model (ZMod 3) →* E, π.comp s = MonoidHom.id _)
    (hupper : Nat.card (Kernel (ZMod 3)) ≤ 3) :
    Nonempty (Kernel (ZMod 3) ≃* Multiplicative (ZMod 3)) :=
  kernel_equiv_three_of_bounds hupper (Nat.le_of_dvd Nat.card_pos
    (three_dvd_kernel_card_of_nonsplit_extension π hπ hc hk hns))

end Atlas.G2.FiniteCover.MultiplierThree
