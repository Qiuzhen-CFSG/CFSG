module

public import Theory.GroupTheory.PerfectCentralCoverSylowNine.OddInversion
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates

/-!
# Eleven-primary kernels over the concrete Janko4 carrier

The certified order makes the existing subgroup of order 1331 a Sylow
subgroup. A thirteen-letter word in its certified coordinate normalizer
inverts both generators and fixes their commutator. Transport through the
faithful coordinate embedding supplies the literal simultaneous-inversion
hypotheses, which exclude eleven from every finite perfect central kernel.

Source: Aschbacher–Smith I.1.3, printed p.407; the ATLAS J4G1-max7W1
normalizer words and certificates in `Simplicity.PrimeCoverage.Elevens`.
-/

open Subgroup
open scoped commutatorElement
namespace Janko4.OddPrimary
open Simplicity.Elevens Simplicity.Elevens.LocalCoordinates

private def inversionWord : List (Fin 4) := [1, 2, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1]

private theorem inversion_X : wordHom inversionWord X = X⁻¹ := by decide
private theorem inversion_Y : wordHom inversionWord Y = Y⁻¹ := by decide
private theorem inversion_Z : wordHom inversionWord Z = Z := by decide

public theorem exists_eleven_configuration :
    ∃ (Q : Sylow 11 Model) (x y r : Model),
      closure ({x, y} : Set Model) = (Q : Subgroup Model) ∧
      x ^ 11 = 1 ∧ y ^ 11 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute x ⁅x, y⁆ ∧ Commute y ⁅x, y⁆ ∧
      r * x * r⁻¹ = x⁻¹ ∧ r * y * r⁻¹ = y⁻¹ ∧ Commute r ⁅x, y⁆ := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let hA := matrixA_mul_self
  let hB := matrixB_pow_four
  let x := localX (Simplicity.a hA) (Simplicity.b hB)
  let y := localY (Simplicity.a hA) (Simplicity.b hB)
  let z := localZ (Simplicity.a hA) (Simplicity.b hB)
  obtain ⟨f, hf, hX, hY, hZ⟩ := coordinate_embedding_of_relations x y z
    (matrix_elevenRelations hA hB)
  obtain ⟨r, hr⟩ := realize_words f
    (realize_actions f _ _ x y z hX hY hZ (matrix_elevenNormalizerRelations hA hB))
    inversionWord
  have hxy : ⁅x, y⁆ = f Z := by
    rw [← hX, ← hY, ← map_commutatorElement]
    congr 1
  have hcard := local_card hA hB
  have hp : IsPGroup 11 (localSubgroup hA hB) := IsPGroup.of_card (n := 3) hcard
  have hi : ¬11 ∣ (localSubgroup hA hB).index := by
    intro hi
    have hd : 11 ^ 4 ∣ Nat.card Model := by
      rw [← (localSubgroup hA hB).card_mul_index, hcard]
      exact Nat.mul_dvd_mul_left 1331 hi
    rw [Cardinality.Thompson.model_card] at hd
    norm_num at hd
  let Q : Sylow 11 Model := hp.toSylow hi
  refine ⟨Q, x, y, r, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hX, ← map_pow, pow_eleven, map_one]
  · rw [← hY, ← map_pow, pow_eleven, map_one]
  · rw [hxy]
    intro hh
    have := hf (hh.trans f.map_one.symm)
    exact (by decide : Z ≠ (1 : Coord)) this
  · rw [hxy, ← hX]
    exact (show Commute X Z by change X * Z = Z * X; decide).map f
  · rw [hxy, ← hY]
    exact (show Commute Y Z by change Y * Z = Z * Y; decide).map f
  · rw [← hX, ← hr, inversion_X, map_inv]
  · rw [← hY, ← hr, inversion_Y, map_inv]
  · have hz : r * f Z * r⁻¹ = f Z := by rw [← hr, inversion_Z]
    rw [hxy]
    exact mul_inv_eq_iff_eq_mul.mp hz

public theorem not_eleven_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬11 ∣ Nat.card f.ker := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨Q, x, y, r, hQ, hx, hy, hz, hxz, hyz, hrx, hry, hrz⟩ := exists_eleven_configuration
  exact PerfectCentralCovering.not_dvd_card_kernel_of_simultaneous_inversion_of_ne_two
    f hf hk (by decide : 11 ≠ 2) Q x y r hQ hx hy hz hxz hyz hrx hry hrz

end Janko4.OddPrimary
