module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank
import all Theory.AtlasPort.LinearGroups.G2.BinaryThreeRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryFieldEmbedding
public import Theory.AtlasPort.LinearGroups.G2.OrderChecks

/-!
# The inverted Sylow three-subgroup of G₂(4)

The existing binary Heisenberg subgroup has order 27. The root element E(1)
inverts both of its specified generators and fixes their commutator. Three
small binary matrix identities check these additional relations. Extending
coefficients embeds this subgroup in the actual field-four octonion group;
its order is the full three-part of that group's checked order.

The internal import deliberately reuses the binary Heisenberg coordinates
and their proved order, without changing the original public interface.
Octonion coordinates and field transport use the licensed ATLAS port of
Gerald Höhn and the ATLAS contributors (LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff). This supplies the three-local input for
Aschbacher–Smith I.1.3(1), GLS III §6.1.
-/

namespace Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary

open Subgroup Atlas.G2.BinaryThreeRank Atlas.SplitOctonion
open scoped commutatorElement

private theorem binary_inverts_x :
    rootE 1 * x * (rootE 1)⁻¹ = x⁻¹ := by
  apply model_ext
  exact (by decide +kernel : ∀ i j,
    (rootE 1 * x * (rootE 1)⁻¹).val (basisVector i) j =
      x⁻¹.val (basisVector i) j)

private theorem binary_inverts_y :
    rootE 1 * y * (rootE 1)⁻¹ = y⁻¹ := by
  apply model_ext
  exact (by decide +kernel : ∀ i j,
    (rootE 1 * y * (rootE 1)⁻¹).val (basisVector i) j =
      y⁻¹.val (basisVector i) j)

private theorem binary_fixes_z : Commute (rootE 1) z := by
  apply model_ext
  exact (by decide +kernel : ∀ i j,
    (rootE 1 * z).val (basisVector i) j = (z * rootE 1).val (basisVector i) j)

private theorem binary_pair_generates : closure ({x, y} : Set (Model (ZMod 2))) =
    embedding.range := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨⟨1, 0, 0⟩, by change x ^ 1 * y ^ 0 * z ^ 0 = x; simp⟩
    · obtain rfl := hg
      exact ⟨⟨0, 1, 0⟩, by change x ^ 0 * y ^ 1 * z ^ 0 = y; simp⟩
  · have hx : x ∈ closure ({x, y} : Set (Model (ZMod 2))) := subset_closure (by simp)
    have hy : y ∈ closure ({x, y} : Set (Model (ZMod 2))) := subset_closure (by simp)
    have hz : z ∈ closure ({x, y} : Set (Model (ZMod 2))) :=
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    rintro g ⟨a, rfl⟩
    exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (pow_mem hz _)

/-- The literal field-four group has a nonabelian cubic Sylow pair and an
ambient simultaneous inverter fixing its commutator. -/
public theorem exists_three_configuration :
    ∃ (Q : Sylow 3 FourBase) (x y r : FourBase),
      closure ({x, y} : Set FourBase) = (Q : Subgroup FourBase) ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute x ⁅x, y⁆ ∧ Commute y ⁅x, y⁆ ∧
      r * x * r⁻¹ = x⁻¹ ∧ r * y * r⁻¹ = y⁻¹ ∧ Commute r ⁅x, y⁆ := by
  let j := binaryFieldEmbedding (F := FourField)
  let S : Subgroup FourBase := embedding.range.map j
  have hS : Nat.card S = 27 := by
    dsimp [S]
    rw [card_map_of_injective (binaryFieldEmbedding_injective (F := FourField)), card_image]
  have hindex : S.index = 9318400 := by
    have h := S.card_mul_index
    rw [hS, OrderChecks.four_order] at h
    omega
  let Q : Sylow 3 FourBase := (IsPGroup.of_card (show Nat.card S = 3^3 from hS)).toSylow
    (by rw [hindex]; decide)
  refine ⟨Q, j x, j y, j (rootE 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change closure ({j x, j y} : Set FourBase) = S
    dsimp [S]
    rw [← binary_pair_generates]
    simp only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  · rw [← map_pow, show x ^ 3 = 1 from BinaryCore.movingActor_cube, map_one]
  · rw [← map_pow, y_cube, map_one]
  · intro h
    apply x_y_ne
    apply commutatorElement_eq_one_iff_mul_comm.mp
    apply (binaryFieldEmbedding_injective (F := FourField))
    simpa only [map_commutatorElement, map_one] using h
  · rw [← map_commutatorElement]
    exact (show Commute x ⁅x, y⁆ from x_z).map j
  · rw [← map_commutatorElement]
    exact (show Commute y ⁅x, y⁆ from y_z).map j
  · simpa only [map_mul, map_inv] using congrArg j binary_inverts_x
  · simpa only [map_mul, map_inv] using congrArg j binary_inverts_y
  · rw [← map_commutatorElement]
    exact binary_fixes_z.map j

end Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary
