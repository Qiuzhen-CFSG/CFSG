module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderCheck
public import Theory.GroupTheory.GeneratorCosetCoverIndex

/-!
# Interfaces for the intrinsic Rudvalis Sylow certificate

The fixed four words are checked in the original degree-4060 model. A
stabilizer chain for their subgroup proves that it is a two-group. A separate
coset calculation inside the fourth ATLAS subgroup proves its odd index.
Neither calculation uses the order of the ambient Rudvalis group.

The finite witnesses use the ATLAS programs attributed in
`SylowOvergroups.Definitions`; the application is Aschbacher--Smith, printed
p.511 (PDF p.528), and GLS3, Table 5.3r.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow

/-- Reverse a positive Schreier transition to obtain its inverse transition. -/
public theorem reverse_step {G : Type*} [Group G] {a b c d : G}
    (h : a * b = c * d) : a⁻¹ * c = b * d⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).2
  rw [mul_assoc, ← h, inv_mul_cancel_left]

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow
