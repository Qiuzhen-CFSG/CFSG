module

public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.CoveringKernelCard

/-!
# Recognizing nontrivial double covers from a multiplier bound

If the universal kernel has order at most two, every covering with a
nontrivial kernel is universal and its kernel is cyclic of order two.
The universal lifting map surjects on kernels, so the proposed kernel order
divides the universal kernel order. Finiteness and nontriviality force equality.

This separates the upper-bound calculation from construction of a nontrivial
cover in Aschbacher–Smith I.1.3(1). It also applies directly to the given
quasisimple groups with nontrivial center in I.2.2(5).
-/

namespace Theory.GroupTheory.Covering

open PerfectCentralCovering

universe u w

variable {G L : Type u} [Group G] [Finite G] [IsQuasisimple G]
variable [Group L] [Finite L] [IsQuasisimple L]

/-- A nontrivial covering attains an upper bound of two for the universal
kernel. Both its universality and its kernel's group structure follow. -/
public theorem isUniversal_and_kernel_equiv_two_of_bound
    (f : Covering L G) (hne : f.toMonoidHom.ker ≠ ⊥)
    (hbound : Nat.card (universalProjection G).ker ≤ 2) :
    IsUniversal.{u, u, w} f ∧
      Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 2)) := by
  let c := universalQuasisimpleCover G
  have hc : IsUniversal.{u, u, u} c := universalQuasisimpleCover_isUniversal G
  have hdvd : Nat.card f.toMonoidHom.ker ∣ Nat.card (universalProjection G).ker :=
    kernel_card_dvd_of_surjective_factor c.toMonoidHom f.toMonoidHom
      (hc.lift f).toMonoidHom (hc.lift f).surjective
      (congrArg Covering.toMonoidHom (hc.lift_fac f))
  have hle : Nat.card f.toMonoidHom.ker ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans hbound
  have hne' : Nat.card f.toMonoidHom.ker ≠ 1 :=
    fun hn => hne (Subgroup.card_eq_one.mp hn)
  have hpos : 0 < Nat.card f.toMonoidHom.ker := Nat.card_pos
  have hcard : Nat.card f.toMonoidHom.ker = 2 := by omega
  refine ⟨isUniversal_of_kernel_card_le f (hcard ▸ hbound), ?_⟩
  exact ⟨mulEquivOfPrimeCardEq hcard (by simp)⟩

end Theory.GroupTheory.Covering
