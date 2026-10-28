module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer
public import Theory.GroupTheory.CoveringComparisonKernelCard

/-!
# Local splitting modulo a central defect subgroup

Quotient a finite perfect central cover by a subgroup D of its kernel. The
result is again a perfect central cover, with the same marked base map, and
the original kernel order is |D| times the new kernel order.

If the quotient cover splits over a subgroup of index prime to p, transfer
excludes p from its kernel. Consequently every p-power divides the original
kernel order exactly when it divides |D|. This does not require either kernel
to be a p-group and does not discard any odd central torsion by assumption.

This is the local-to-global step used in the G₂(4) multiplier calculation of
Aschbacher–Smith I.1.3(1), printed p.407 (PDF p.418), citing GLS III §6.1.
The construction of the local section and its defect subgroup is separate.
-/

@[expose] public section

open Subgroup
namespace PerfectCentralCovering
variable {E G : Type*} [Group E] [Group G]

/-- Quotient by a subgroup of the actual central kernel. -/
def Cover.quotientKernelSubgroup (c : Cover E G) (D : Subgroup E) [D.Normal]
    (hD : D ≤ c.toMonoidHom.ker) : Cover (E ⧸ D) G where
  toMonoidHom := QuotientGroup.lift D c.toMonoidHom hD
  surjective := by
    intro g
    obtain ⟨x, hx⟩ := c.surjective g
    exact ⟨QuotientGroup.mk x, hx⟩
  isPerfect := by
    let : Group.IsPerfect E := c.isPerfect
    infer_instance
  ker_le_center := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D x
    have hy : y ∈ c.toMonoidHom.ker := hx
    rw [mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective D z
    exact congrArg (QuotientGroup.mk' D) (mem_center_iff.mp (c.ker_le_center hy) w)

/-- The quotient covering retains the original projection. -/
theorem Cover.quotientKernelSubgroup_comp (c : Cover E G) (D : Subgroup E) [D.Normal]
    (hD : D ≤ c.toMonoidHom.ker) :
    (c.quotientKernelSubgroup D hD).toMonoidHom.comp (QuotientGroup.mk' D) =
      c.toMonoidHom := by
  ext
  rfl

/-- Exact kernel cardinality, including every prime divisor. -/
theorem Cover.card_kernel_quotientKernelSubgroup [Finite E] [Finite G]
    (c : Cover E G) (D : Subgroup E) [D.Normal] (hD : D ≤ c.toMonoidHom.ker) :
    Nat.card c.toMonoidHom.ker = Nat.card D *
      Nat.card (c.quotientKernelSubgroup D hD).toMonoidHom.ker := by
  simpa only [QuotientGroup.ker_mk'] using
    Theory.GroupTheory.kernel_card_eq_mul_of_surjective_factor c.toMonoidHom
      (c.quotientKernelSubgroup D hD).toMonoidHom (QuotientGroup.mk' D)
      (c.quotientKernelSubgroup D hD).surjective (QuotientGroup.mk'_surjective D)
      (c.quotientKernelSubgroup_comp D hD)

/-- A local section modulo D detects every primary divisor of the kernel. -/
theorem Cover.prime_pow_dvd_kernel_iff_of_quotient_section [Finite E] [Finite G]
    (c : Cover E G) (D : Subgroup E) [D.Normal] (hD : D ≤ c.toMonoidHom.ker)
    {p : ℕ} [Fact p.Prime] (P : Subgroup G) (hp : ¬ p ∣ P.index)
    (s : P →* E ⧸ D)
    (hs : (c.quotientKernelSubgroup D hD).toMonoidHom.comp s = P.subtype) (n : ℕ) :
    p ^ n ∣ Nat.card c.toMonoidHom.ker ↔ p ^ n ∣ Nat.card D := by
  have hc := not_dvd_card_kernel_of_section (c.quotientKernelSubgroup D hD) P hp s hs
  have hcop : (p ^ n).Coprime
      (Nat.card (c.quotientKernelSubgroup D hD).toMonoidHom.ker) :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hc).pow_left n
  rw [c.card_kernel_quotientKernelSubgroup D hD]
  exact hcop.dvd_mul_right

end PerfectCentralCovering

end
