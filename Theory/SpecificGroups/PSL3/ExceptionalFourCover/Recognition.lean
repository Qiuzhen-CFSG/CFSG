module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.Basic

/-!
# Assembling the exceptional kernel from an extension and a bound

A perfect central extension with kernel C₄ × C₄ × C₃ gives the lower
bound on the universal kernel. An independent upper bound of 48 then
makes the universal comparison map an isomorphism. We retain that map
on kernels, so this proves the group structure, not just its order.
The resulting isomorphism transports to every field of order four.

Both mathematical inputs remain explicit here. Their construction is the
outstanding calculation in Aschbacher–Smith I.1.3(6), printed p.407,
and GLS98, §6.1, Tables 6.1.2–6.1.3 and Theorem 6.1.4.
-/

@[expose] public section

open Theory.GroupTheory

namespace Matrix.PSL3.ExceptionalFourCover

universe w

variable {L : Type} [Group L] [Finite L] [IsQuasisimple L]

/-- The upper bound certifies the independently constructed extension as universal. -/
theorem isUniversal_of_cover_and_bound
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) :
    Covering.IsUniversal.{0, 0, w} f := by
  apply Covering.isUniversal_of_kernel_card_le f
  change Nat.card cover.toMonoidHom.ker ≤ Nat.card f.toMonoidHom.ker
  rw [Nat.card_congr e.toEquiv, card_multiplier]
  exact hbound

/-- Conditional assembly of the actual universal kernel, retaining its group structure. -/
noncomputable def kernelEquivOfCoverAndBound
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) :
    cover.toMonoidHom.ker ≃* Multiplier :=
  (Covering.IsUniversal.kerMulEquiv cover_isUniversal
    (isUniversal_of_cover_and_bound f e hbound) (MulEquiv.refl PSL3Four.PSL)).trans e

/-- The literal canonical free-central projection used by the diagonal-action consumers. -/
noncomputable def canonicalKernelEquivOfCoverAndBound
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) :
    (PerfectCentralCovering.universalProjection PSL3Four.PSL).ker ≃* Multiplier :=
  kernelEquivOfCoverAndBound f e hbound

/-- Over a simple base, the identified kernel is the whole center of the covering group. -/
noncomputable def centerEquivOfCoverAndBound
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) :
    Subgroup.center CoverGroup ≃* Multiplier :=
  (MulEquiv.subgroupCongr cover_ker_eq_center.symm).trans
    (kernelEquivOfCoverAndBound f e hbound)

/-- The same kernel calculation for the actual projection over any field of order four. -/
noncomputable def coverOverKernelEquivOfCoverAndBound
    (K : Type*) [Field K] [Finite K] (hK : Nat.card K = 4)
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) :
    (coverOver K hK).toMonoidHom.ker ≃* Multiplier :=
  (MulEquiv.subgroupCongr (coverOver_ker K hK)).trans
    (kernelEquivOfCoverAndBound f e hbound)

/-- The order forced by the actual base group and the identified kernel. -/
theorem card_coverGroup_of_cover_and_bound
    (f : Covering L PSL3Four.PSL) (e : f.toMonoidHom.ker ≃* Multiplier)
    (hbound : Nat.card cover.toMonoidHom.ker ≤ 48) :
    Nat.card CoverGroup = 967680 := by
  have h := cover.toMonoidHom.ker.card_mul_index
  rw [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      cover.toMonoidHom cover.surjective).toEquiv,
    Nat.card_congr (kernelEquivOfCoverAndBound f e hbound).toEquiv,
    card_multiplier, PSL3Four.card_PSL] at h
  exact h.symm

end Matrix.PSL3.ExceptionalFourCover
