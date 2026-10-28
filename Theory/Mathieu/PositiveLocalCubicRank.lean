module
public import Theory.Quasithin.PositiveLocalRank
public import Theory.Quasithin.LocalRankEmbedding
public import Theory.SpecificGroups.Alternating.PositiveLocalCubicRank
public import Theory.Mathieu.M11.Properties.Centralizer
public import Theory.Mathieu.M12.Properties.PointStabilizer
public import Theory.Mathieu.M22.TripleCoverLocalRank
public import Theory.Mathieu.M23.Properties.Simplicity

/-!
# Positive two-local cubic rank in the five Mathieu groups

The certified centralizer of the standard M₁₁ involution has order 48,
so it supplies a local cubic witness. The actual point-stabilizer embedding
transfers this witness to M₁₂. In M₂₂ the checked hexad section embeds A₆;
its A₄ four-group supplies a two-local witness. The literal point-stabilizer
embeddings then transfer this witness to M₂₃ and M₂₄.

Source: Aschbacher--Smith A.1.34 and A.3.8, printed pp.29--30 and45--46,
for the nonnormal-component local-rank obstruction; GLS3 Tables 5.3a--e
and the intrinsic Witt-design certificates imported below.
-/

public section
namespace Sporadic.Mathieu
open Subgroup Theory.Quasithin

theorem m11_one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 M11 := by
  apply one_le_twoLocalPrimeRank_of_dvd_involution_centralizer m11GeneratorAInM11
  · exact (Subgroup.orderOf_coe m11GeneratorAInM11).symm.trans m11GeneratorA_order
  · change 3 ∣ Nat.card m11InvolutionCentralizer
    rw [m11_involutionCentralizer_card]
    decide

theorem m12_one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 M12 := by
  exact m11_one_le_twoLocalPrimeRank_three.trans
    ((twoLocalPrimeRank_le_of_injective 3 m11ToM12PointStabilizer
      m11ToM12PointStabilizer_injective).trans
      (twoLocalPrimeRank_le_of_injective 3 _
        (MulAction.stabilizer M12 (12 : Fin 12)).subtype_injective))

theorem m22_one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 M22 :=
  (alternating_one_le_twoLocalPrimeRank (by decide : 4 ≤ 6)).trans
    (twoLocalPrimeRank_le_of_injective 3 hexadAlternatingSixEmbedding
      hexadAlternatingSixEmbedding_injective)

theorem m23_one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 M23 :=
  m22_one_le_twoLocalPrimeRank_three.trans
    ((twoLocalPrimeRank_le_of_injective 3 m23EquivM22PointStabilizer.toMonoidHom
      m23EquivM22PointStabilizer.injective).trans
      (twoLocalPrimeRank_le_of_injective 3 _
        (MulAction.stabilizer M23 (9 : Fin 23)).subtype_injective))

theorem m24_one_le_twoLocalPrimeRank_three : 1 ≤ twoLocalPrimeRank 3 M24 :=
  m23_one_le_twoLocalPrimeRank_three.trans
    ((twoLocalPrimeRank_le_of_injective 3 m23EquivM24PointStabilizer.toMonoidHom
      m23EquivM24PointStabilizer.injective).trans
      (twoLocalPrimeRank_le_of_injective 3 _
        (MulAction.stabilizer M24 (24 : Fin 24)).subtype_injective))

end Sporadic.Mathieu
