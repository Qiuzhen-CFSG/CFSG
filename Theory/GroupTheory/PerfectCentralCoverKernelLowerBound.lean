module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.CoveringKernelCard
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Lower bounds on the universal central kernel

A perfect central cover is a quotient of the canonical universal cover. The
universal lift is surjective because its image, together with the central
kernel downstairs, generates a perfect group. Restriction to the kernels
therefore gives divisibility of their orders. An independently proved upper
bound attaining the order of an explicit cover determines the universal
kernel order; at prime order it determines the kernel group as well.

This is the upper/lower-bound assembly used in Aschbacher--Smith I.1.1--I.1.4,
printed pp.407--408. The J₃ application is in
`Theory.SpecificGroups.Janko3.Multiplier.Assembly`; its concrete upper bound
and triple-cover construction remain separate obligations.
-/

namespace PerfectCentralCovering

open Theory.GroupTheory

universe u v

variable {G : Type u} {E : Type v} [Group G] [Group E]
variable [Group.IsPerfect G]

/-- The kernel of every perfect central cover is a quotient of the canonical
universal kernel, so its order divides the universal kernel order. -/
public theorem Cover.kernel_card_dvd_universal (c : Cover E G) :
    Nat.card c.toMonoidHom.ker ∣ Nat.card (universalProjection G).ker := by
  let : Group.IsPerfect E := c.isPerfect
  obtain ⟨h, hh, _⟩ := universalProjection_existsUnique_lift
    c.toMonoidHom c.surjective c.ker_le_center
  have hs : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      c.toMonoidHom h (hh ▸ universalProjection_surjective G) c.ker_le_center
  exact kernel_card_dvd_of_surjective_factor (universalProjection G)
    c.toMonoidHom h hs hh

variable [Finite G]

/-- A perfect central cover attaining an independent upper bound determines
the order of the canonical universal kernel. -/
public theorem Cover.universal_kernel_card_eq_of_bound (c : Cover E G)
    {n : ℕ} (hc : Nat.card c.toMonoidHom.ker = n)
    (hbound : Nat.card (universalProjection G).ker ≤ n) :
    Nat.card (universalProjection G).ker = n := by
  have hd := c.kernel_card_dvd_universal
  rw [hc] at hd
  exact le_antisymm hbound (Nat.le_of_dvd Nat.card_pos hd)

/-- At prime order the upper/lower-bound argument identifies the full kernel
group, without assuming that the proposed cover is universal. -/
public theorem Cover.universal_kernel_equiv_of_prime_bound (c : Cover E G)
    {p : ℕ} [Fact p.Prime] (hc : Nat.card c.toMonoidHom.ker = p)
    (hbound : Nat.card (universalProjection G).ker ≤ p) :
    Nonempty ((universalProjection G).ker ≃* Multiplicative (ZMod p)) := by
  exact ⟨mulEquivOfPrimeCardEq (c.universal_kernel_card_eq_of_bound hc hbound)
    (by simp)⟩

end PerfectCentralCovering
