module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearSetup
public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.MatrixCertificates
import Mathlib.Algebra.Group.Conj

/-!
# Short relations for the lifted local generators

The local generators are conjugates of the original linear generators, hence
satisfy x² = y⁴ = 1 in GL(45,7). These relations can simplify candidate
transition words before the remaining full-matrix checks. The power identities
for the original matrices are already kernel-certified in `MatrixGenerators`
and `ProjectiveSimplicity/MatrixCertificates`.

Sources and attribution are in `refs/original/onan/` and
`ProjectiveOrder/source/`.
-/

namespace ONan.OrderCertificate

public theorem linearLocalA_pow_two : linearLocalA ^ 2 = 1 := by
  have ha : linearA ^ 2 = 1 := by
    apply Units.ext
    exact (pow_two matrixA).trans matrixA_mul_self
  have h := @conj_pow _ _ 2 linearB⁻¹ linearA
  simpa only [linearLocalA, inv_inv, ha, mul_one, inv_mul_cancel] using h

public theorem linearLocalB_pow_four : linearLocalB ^ 4 = 1 := by
  have hb : linearB ^ 4 = 1 := Units.ext ONan.Simplicity.matrixB_pow_four
  have h := @conj_pow _ _ 4 ((linearA * linearB ^ 2) ^ 2)⁻¹ linearB
  simpa only [linearLocalB, inv_inv, hb, mul_one, inv_mul_cancel] using h

end ONan.OrderCertificate
