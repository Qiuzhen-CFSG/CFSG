module

public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.DerivedDetection.Quotient
public import Theory.Mathieu.SchurMultipliers.M12Upper.LocalBound.Calculation.DerivedDetection.Transfer

/-!
# Derived-kernel detection in the first M₁₂ parabolic

For every finite central two-extension of the actual first parabolic, its
central derived kernel lies in the derived subgroup of the quaternion-core
preimage. No commuting-lift or perfectness premise is required.

Factor out that core-derived subgroup. The literal matching map descends to
S₃ and has an abelian two-group kernel. Quaternion coordinates show that the
cubic actor's fixed elements in this kernel are central. The cubic norm gives
an ambient normal complement to its central part, and central Sylow transfer
in the resulting central S₃ extension kills the remaining derived kernel.
Pulling back proves the claimed containment.

Source: the local upper-bound calculation for Aschbacher–Smith I.1.3(1),
printed p.407, using the actual parabolic geometry of 14.2.21, printed p.988.
This is detection only; the separate invariant-pairing calculation supplies
the required kernel-size bound.
-/

namespace Sporadic.Mathieu.SchurMultipliers.M12Upper
open Subgroup M12SmallPair
open scoped IsMulCommutative
universe u

/-- The actual M₁₂ application of cubic transfer. Every geometric, quotient,
normality and two-group premise is discharged here; transfer is the explicit
input to this reusable reduction. -/
public theorem firstParabolicCoreDerivedDetection_of_cubic_transfer
    (htransfer : ∀ (E : Type u) [Group E] [Finite E]
      (f : E →* Equiv.Perm (Fin 3)), Function.Surjective f →
      IsMulCommutative f.ker → IsPGroup 2 f.ker →
      ∀ t : E, f t = List.formPerm [0,2,1] →
      (∀ x ∈ f.ker, Commute t x → x ∈ center E) →
      (center E ⊓ _root_.commutator E) ⊓ f.ker ≤ ⊥) :
    FirstParabolicCoreDerivedDetection.{u} := by
  intro D _ _ q hq hk hp
  let π := QuotientGroup.mk' (coreDerived q)
  obtain ⟨t,ht⟩ := hq ⟨FirstCore.secondCycle,FirstCore.secondCycle_mem⟩
  have hvanish := htransfer (D ⧸ coreDerived q) (matchingAfterCoreDerived q)
    (matchingAfterCoreDerived_surjective q hq)
    (matchingAfterCoreDerived_kernel_abelian q)
    (matchingAfterCoreDerived_kernel_isPGroup q hp) (π t)
    (by rw [matchingAfterCoreDerived_mk, ht]; exact FirstCore.cycle_image)
    (matchingAfterCoreDerived_fixed_central q hq hk t ht)
  intro x hx
  have hc : π x ∈ center (D ⧸ coreDerived q) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (coreDerived q) y
    exact congrArg π (mem_center_iff.mp (hk hx.1) a)
  have hd : π x ∈ _root_.commutator (D ⧸ coreDerived q) := by
    have hm : (_root_.commutator D).map π ≤ _root_.commutator (D ⧸ coreDerived q) := by
      rw [map_commutator_eq]
      exact commutator_mono le_top le_top
    exact hm ⟨x,hx.2,rfl⟩
  have hn : π x ∈ (matchingAfterCoreDerived q).ker := by
    change FirstCore.matchingQuotient (q x) = 1
    rw [MonoidHom.mem_ker.mp hx.1, map_one]
  exact (QuotientGroup.eq_one_iff _).mp (hvanish ⟨⟨hc,hd⟩,hn⟩)

/-- The full central derived two-kernel is detected in the literal lifted
quaternion core, uniformly in the universe of the covering group. -/
public theorem firstParabolicCoreDerivedDetection :
    FirstParabolicCoreDerivedDetection.{u} :=
  firstParabolicCoreDerivedDetection_of_cubic_transfer
    (fun _ _ _ => center_inf_derived_inf_two_kernel_of_cubic_fixed_central)

end Sporadic.Mathieu.SchurMultipliers.M12Upper
