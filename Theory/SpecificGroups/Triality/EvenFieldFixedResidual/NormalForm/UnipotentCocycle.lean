module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.UnipotentCocycle.Descent
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.UnipotentCocycle.SplitPositive
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.SylowReduction

/-!
# Canonical triality cocycles from the split positive calculation

For `n = 2*m` with `m > 0`, every cocycle for coefficient Frobenius to the
power `3*m` is a coboundary in the genuine triality carrier. A cocycle in its
original unipotent subgroup has a solution in that same subgroup.

The actual positive-root filtration and scalar trace equations give a solution
in the split positive subgroup. Descend it along the order-three defining
twist, then apply the genuine Sylow-two reduction to solve cocycles in the
whole carrier. Both steps retain the literal coefficient Frobenius and the
equation `g = h⁻¹ * sigma(h)`, including `m = 1`. The new local and global
results have no remaining cocycle-solvability premise. They supply the inputs
to field-automorphism normalization, whose assembly is separate.

Sources: Aschbacher–Smith 16.1.3 and 16.1.4(4), printed p.1171,
`refs/quasithin.pdf`; GLS3 §§2.1, 2.3–2.5, especially 2.5.13 and 2.5.17,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace Triality.Standard.EvenField.NormalForm
open OuterOdd Parabolics

namespace UnipotentCocycle

/-- Every canonical coefficient cocycle in the genuine triality unipotent
subgroup is a coboundary in that subgroup, including `m = 1`. -/
theorem unipotent_cocycle_solutions
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (u : BinaryCarrier n hn) (hu : u ∈ unipotent (binaryParameters n hn))
    (huc : u * coefficientAction (binaryParameters n hn)
      (coefficientFrobenius n hn (3*m)) u = 1) :
    ∃ v : BinaryCarrier n hn, v ∈ unipotent (binaryParameters n hn) ∧
      u = v⁻¹ * coefficientAction (binaryParameters n hn)
        (coefficientFrobenius n hn (3*m)) v := by
  exact unipotent_cocycle_of_splitPositive n hn _
    (splitPositive_cocycle_solutions n hn m hm hnm) u hu huc

end UnipotentCocycle

/-- Solvability in the split positive subgroup supplies the local Sylow premise
and hence global canonical cocycle solvability in the original triality carrier. -/
theorem canonical_cocycle_solutions_of_splitPositive
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (hsol : ∀ u : SplitGroup (binaryParameters n hn),
      u ∈ positiveSubgroup (binaryParameters n hn) →
      u * coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) u = 1 →
      ∃ v : SplitGroup (binaryParameters n hn), v ∈ positiveSubgroup (binaryParameters n hn) ∧
        u = v⁻¹ * coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) v)
    (g : BinaryCarrier n hn)
    (hg : g * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) g = 1) :
    ∃ h : BinaryCarrier n hn,
      g = h⁻¹ * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) h := by
  exact canonical_cocycle_solutions_of_unipotent n hn m hm hnm
    (UnipotentCocycle.unipotent_cocycle_of_splitPositive n hn _ hsol) g hg

/-- Every canonical coefficient cocycle in the genuine triality carrier is a
coboundary. The proved unipotent theorem discharges the Sylow reduction's
local premise, supplying the cocycle input for field normalization. -/
theorem canonical_cocycle_solutions
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (g : BinaryCarrier n hn)
    (hg : g * coefficientAction (binaryParameters n hn)
      (coefficientFrobenius n hn (3*m)) g = 1) :
    ∃ h : BinaryCarrier n hn,
      g = h⁻¹ * coefficientAction (binaryParameters n hn)
        (coefficientFrobenius n hn (3*m)) h := by
  exact canonical_cocycle_solutions_of_unipotent n hn m hm hnm
    (UnipotentCocycle.unipotent_cocycle_solutions n hn m hm hnm) g hg

end Triality.Standard.EvenField.NormalForm
