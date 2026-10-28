module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.LiftMatrices
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation

/-!
# The five ATLAS relations in the actual sign quotient

The first and third words lift to the central negative sign; the other three
lift to the identity. The faithful quaternion matrices certify these facts in
the Hermitian lattice stabilizer, and the literal quotient map kills its two
central signs. No presentation-exactness or comparison premise is used.

Source: ATLAS `J2G1-P2`, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J2G1-P2.
The concrete icosian roots retain Gerald Höhn's ATLAS attribution and license
through the imported construction.
-/

public section
namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Atlas.Conway RelatorMatrices
open G2FourModule.Embedding.InnerRealization

theorem xLift_square : xLift ^ 2 = icosianCentralSign := by
  apply matrixHom_injective
  rw [map_pow, matrixHom_xLift, matrixHom_centralSign, pow_two]
  exact xx_mul

theorem yLift_cube : yLift ^ 3 = 1 := by
  apply matrixHom_injective
  rw [map_pow, matrixHom_yLift, map_one]
  calc
    my ^ 3 = (my * my) * my := by noncomm_ring
    _ = 1 := by rw [yy_mul, yyy_mul]

theorem productLift_seventh : (xLift * yLift) ^ 7 = icosianCentralSign := by
  apply matrixHom_injective
  rw [map_pow, map_mul, matrixHom_xLift, matrixHom_yLift, matrixHom_centralSign, xy_mul]
  calc
    xy ^ 7 = (xy ^ 2) ^ 2 * xy ^ 2 * xy := by noncomm_ring
    _ = -1 := by simp only [pow_two, xy2_mul, xy4_mul, xy6_mul, xy7_mul]

theorem commutatorLift_twelfth : (xLift⁻¹ * yLift⁻¹ * xLift * yLift) ^ 12 = 1 := by
  apply matrixHom_injective
  simp only [map_pow, map_mul, matrixHom_xLift_inv, matrixHom_yLift_inv,
    matrixHom_xLift, matrixHom_yLift, map_one, c0_mul, c1_mul, comm_mul]
  calc
    comm ^ 12 = ((comm ^ 2) ^ 2) ^ 2 * (comm ^ 2) ^ 2 := by noncomm_ring
    _ = 1 := by simp only [pow_two, comm2_mul, comm4_mul, comm8_mul, comm12_mul]

theorem longWordLift_sixth : Presentation.longWord xLift yLift ^ 6 = 1 := by
  apply matrixHom_injective
  simp only [Presentation.longWord, map_pow, map_mul, matrixHom_yLift_inv, matrixHom_xLift, matrixHom_yLift, map_one,
    long0_mul, long1_mul, long2_mul, long3_mul, long4_mul, long5_mul,
    long6_mul, long7_mul, long8_mul]
  calc
    long8 ^ 6 = (long8 ^ 2) ^ 2 * long8 ^ 2 := by noncomm_ring
    _ = 1 := by simp only [pow_two, long2p_mul, long4p_mul, long6p_mul]

private theorem projection_centralSign : icosianProjectiveProjection icosianCentralSign = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)

/-- All five literal ATLAS relators hold for the concrete projective pair. -/
theorem relations : Presentation.Relations x y := by
  intro i
  have hx : x ^ 2 = 1 := by
    rw [x, ← map_pow, xLift_square, projection_centralSign]
  have hy : y ^ 3 = 1 := by
    rw [y, ← map_pow, yLift_cube, map_one]
  have hxy : (x * y) ^ 7 = 1 := by
    rw [x, y, ← map_mul, ← map_pow, productLift_seventh, projection_centralSign]
  have hc : (x⁻¹ * y⁻¹ * x * y) ^ 12 = 1 := by
    rw [x, y, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      ← map_pow, commutatorLift_twelfth, map_one]
  have hl : Presentation.longWord x y ^ 6 = 1 := by
    rw [x, y, ← Presentation.map_longWord, ← map_pow, longWordLift_sixth, map_one]
  fin_cases i
  · exact hx
  · exact hy
  · exact hxy
  · exact hc
  · exact hl

end Sporadic.LeechRelated.J2.IcosianComparison.Generators
