module

public import Theory.SpecificGroups.G2.MultiplierFourBound.OddPrimary.ThreeLocal
import all Theory.SpecificGroups.G2.MultiplierFourBound.OddPrimary.ThreeLocal
public import Theory.GroupTheory.PerfectCentralCoverSylowNine.PartialInversion

/-!
# The nonsplit G₂ three-primary calculation at valuation one

If three divides q + 1 but nine does not, the binary Heisenberg subgroup
embeds as a full Sylow three-subgroup in the actual octonion model over F.
The exact group order, reduced modulo 81, proves that its index is prime
to three. Its ambient simultaneous inverter then removes three from the
kernel of every finite perfect central cover.

The internal import reuses the binary generator relations already proved
for the G₂(4) calculation. This module restricts that argument to the precise
range in which order 27 is sufficient; it makes no assertion for G₂(8).
The canonical-cover consumer is `Nondefining.ThreePrimary`.
Source: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
The binary octonion matrices are licensed ATLAS ports; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

open Subgroup Atlas.G2.BinaryThreeRank Atlas.SplitOctonion
open scoped commutatorElement

namespace Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
variable {F : Type*} [Field F] [Finite F]

private theorem not_eightyOne_dvd_card_model
    (hthree : 3 ∣ Nat.card F + 1) (hnine : ¬ 9 ∣ Nat.card F + 1) :
    ¬ 81 ∣ Nat.card (Model F) := by
  rw [card_Model]
  intro h
  have hzero := (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mpr h
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hq),
    Nat.cast_sub (Nat.one_le_pow _ _ hq)] at hzero
  simp only [Nat.cast_pow, Nat.cast_one] at hzero
  let a : Fin 81 := ⟨Nat.card F % 81, Nat.mod_lt _ (by decide)⟩
  have ha : (Nat.card F : ZMod 81) = a := rfl
  rw [ha] at hzero
  have ha3 : (a.val + 1) % 3 = 0 := by
    dsimp [a]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 81)]
    simpa [Nat.add_mod] using Nat.dvd_iff_mod_eq_zero.mp hthree
  have ha9 : (a.val + 1) % 9 ≠ 0 := by
    dsimp [a]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (by decide : 9 ∣ 81)]
    simpa [Nat.add_mod] using (Nat.dvd_iff_mod_eq_zero.not.mp hnine)
  have hcalc : ∀ a : Fin 81, (a.val + 1) % 3 = 0 → (a.val + 1) % 9 ≠ 0 →
      (a : ZMod 81)^6 * ((a : ZMod 81)^6 - 1) * ((a : ZMod 81)^2 - 1) ≠ 0 :=
    by decide +kernel
  exact hcalc a ha3 ha9 hzero

variable [CharP F 2]

private theorem exists_valuation_one_configuration
    (hthree : 3 ∣ Nat.card F + 1) (hnine : ¬ 9 ∣ Nat.card F + 1) :
    ∃ (Q : Sylow 3 (Model F)) (x y r : Model F),
      closure ({x, y} : Set (Model F)) = (Q : Subgroup (Model F)) ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧
      Commute x ⁅x, y⁆ ∧ Commute y ⁅x, y⁆ ∧
      r * x * r⁻¹ = x⁻¹ ∧ r * y * r⁻¹ = y⁻¹ ∧ Commute r ⁅x, y⁆ := by
  let j := binaryFieldEmbedding (F := F)
  let S : Subgroup (Model F) := embedding.range.map j
  have hS : Nat.card S = 27 := by
    dsimp [S]
    rw [card_map_of_injective (binaryFieldEmbedding_injective (F := F)), card_image]
  have hindex : ¬ 3 ∣ S.index := by
    intro hi
    apply not_eightyOne_dvd_card_model hthree hnine
    rw [← S.card_mul_index, hS]
    exact Nat.mul_dvd_mul_left 27 hi
  let Q : Sylow 3 (Model F) :=
    (IsPGroup.of_card (show Nat.card S = 3^3 from hS)).toSylow hindex
  refine ⟨Q, j x, j y, j (rootE 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change closure ({j x, j y} : Set (Model F)) = S
    dsimp [S]
    rw [← FiniteCover.MultiplierFourBound.OddPrimary.binary_pair_generates]
    simp only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  · rw [← map_pow, show x ^ 3 = 1 from BinaryCore.movingActor_cube, map_one]
  · rw [← map_pow, y_cube, map_one]
  · intro h
    apply x_y_ne
    apply commutatorElement_eq_one_iff_mul_comm.mp
    apply binaryFieldEmbedding_injective (F := F)
    simpa only [map_commutatorElement, map_one] using h
  · rw [← map_commutatorElement]
    exact (show Commute x ⁅x, y⁆ from x_z).map j
  · rw [← map_commutatorElement]
    exact (show Commute y ⁅x, y⁆ from y_z).map j
  · simpa only [map_mul, map_inv] using
      congrArg j FiniteCover.MultiplierFourBound.OddPrimary.binary_inverts_x
  · simpa only [map_mul, map_inv] using
      congrArg j FiniteCover.MultiplierFourBound.OddPrimary.binary_inverts_y
  · rw [← map_commutatorElement]
    exact FiniteCover.MultiplierFourBound.OddPrimary.binary_fixes_z.map j

/-- The actual binary Sylow subgroup excludes three at nonsplit valuation one. -/
public theorem not_three_dvd_kernel_of_valuation_one
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model F) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (hthree : 3 ∣ Nat.card F + 1) (hnine : ¬ 9 ∣ Nat.card F + 1) :
    ¬ 3 ∣ Nat.card f.ker := by
  obtain ⟨Q, x, y, r, hQ, hx, hy, hz, hxz, hyz, hrx, hry, hrz⟩ :=
    exists_valuation_one_configuration hthree hnine
  exact PerfectCentralCovering.not_three_dvd_card_kernel_of_simultaneous_inversion
    f hf hk Q x y r hQ hx hy hz hxz hyz hrx hry hrz

end Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
