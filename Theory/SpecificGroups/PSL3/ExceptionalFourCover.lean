module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.Recognition
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization

/-!
# The exceptional universal cover of PSL₃(4)

The finite quasisimple group and its universal projection are constructed in
`Basic`, including transport to every field of order four. The independent
`KernelBound` and `KernelRealization` calculations now identify its kernel
with C₄ × C₄ × C₃: the universal comparison onto the concrete extension
is an isomorphism because its kernel already attains the upper bound 48.
The concrete permutation-matrix extension is consequently universal as well.

This proves the multiplier formula of Aschbacher–Smith I.1.3(6), printed
p.407 (PDF p.418), citing GLS98 §6.1 and ATLAS pp.xv–xvi. The kernel is the
whole center and the covering group has order 967680. The field-transported
projection retains this literal kernel subgroup and the universal property.
-/

public section

open Theory.GroupTheory

namespace Matrix.PSL3.ExceptionalFourCover

universe u w

/-- The concrete permutation-matrix extension is the exceptional universal cover. -/
theorem realization_isUniversal : Covering.IsUniversal.{0, 0, w} realization :=
  isUniversal_of_cover realization realizationKernelEquiv

/-- The full exceptional kernel of the constructed universal covering of PSL₃(4). -/
noncomputable def kernelEquiv : cover.toMonoidHom.ker ≃* Multiplier :=
  kernelEquivOfCover realization realizationKernelEquiv

/-- The same isomorphism on the literal canonical projection used by consumers. -/
noncomputable def canonicalKernelEquiv :
    (PerfectCentralCovering.universalProjection PSL3Four.PSL).ker ≃* Multiplier :=
  kernelEquiv

/-- The full center of the universal covering group is C₄ × C₄ × C₃. -/
noncomputable def centerEquiv : Subgroup.center CoverGroup ≃* Multiplier :=
  (MulEquiv.subgroupCongr cover_ker_eq_center.symm).trans kernelEquiv

theorem card_kernel : Nat.card cover.toMonoidHom.ker = 48 :=
  (Nat.card_congr kernelEquiv.toEquiv).trans card_multiplier

theorem card_center : Nat.card (Subgroup.center CoverGroup) = 48 :=
  (Nat.card_congr centerEquiv.toEquiv).trans card_multiplier

/-- The actual universal covering group has order 48 · 20160. -/
theorem card_coverGroup : Nat.card CoverGroup = 967680 :=
  card_coverGroup_of_cover_and_bound realization realizationKernelEquiv kernel_card_le

variable (F : Type u) [Field F] [Finite F] (hF : Nat.card F = 4)

/-- I.1.3(6) over any finite field of order four, for the actual universal projection. -/
noncomputable def coverOverKernelEquiv :
    (coverOver F hF).toMonoidHom.ker ≃* Multiplier :=
  (MulEquiv.subgroupCongr (coverOver_ker F hF)).trans kernelEquiv

theorem card_coverOver_kernel : Nat.card (coverOver F hF).toMonoidHom.ker = 48 :=
  (Nat.card_congr (coverOverKernelEquiv F hF).toEquiv).trans card_multiplier

end Matrix.PSL3.ExceptionalFourCover
