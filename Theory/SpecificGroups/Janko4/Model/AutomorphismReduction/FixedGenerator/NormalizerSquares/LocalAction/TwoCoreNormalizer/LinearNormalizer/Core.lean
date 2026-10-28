module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearModel
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The commutator subgroup of the binary local model

We use the literal ambient commutator subgroup, with generators `C * D` and
`D²` lying in it. Their membership follows from the certified relations
`C² = D⁴ = (CD)¹¹ = 1`, by passing to the abelianization.
No perfectness or recognition of this subgroup is assumed here.

The matrix data are derived from the ATLAS files retained in
`../LinearModel/source/`; see `LinearModel` for attribution and conventions.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- The actual commutator subgroup, as an ambient matrix subgroup. -/
def derivedGroup : Subgroup Matrix12ˣ := ⁅actionGroup, actionGroup⁆

/-- Two even words used to constrain the commutator subgroup's centralizer. -/
def coreA : Matrix12ˣ := unitC * unitD

def coreB : Matrix12ˣ := unitD ^ 2

/-- Packed matrices for the two even words. -/
def matrixA : Matrix12 := fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]

def matrixB : Matrix12 := fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]

theorem coe_coreA : (coreA : Matrix12) = matrixA := by
  change matrixC * matrixD = matrixA
  decide +kernel

theorem coe_coreB : (coreB : Matrix12) = matrixB := by
  change matrixD ^ 2 = matrixB
  decide +kernel

private def powerA2 : Matrix12 := fromRows ![128, 28, 412, 2976, 1639, 4, 400, 2891, 2823, 1513, 1412, 1499]

private def powerA4 : Matrix12 := fromRows ![2891, 3163, 3095, 122, 249, 412, 1579, 409, 2613, 3964, 1108, 2307]

private def powerA8 : Matrix12 := fromRows ![3339, 3311, 1705, 2927, 3558, 1848, 3550, 100, 70, 829, 3729, 1062]

theorem coreA_pow_eleven : coreA ^ 11 = 1 := by
  apply Units.ext
  change (coreA : Matrix12) ^ 11 = 1
  rw [coe_coreA]
  have h2 : matrixA ^ 2 = powerA2 := by decide +kernel
  have h4 : powerA2 * powerA2 = powerA4 := by decide +kernel
  have h8 : powerA4 * powerA4 = powerA8 := by decide +kernel
  have h11 : powerA8 * powerA2 * matrixA = 1 := by decide +kernel
  calc
    matrixA ^ 11 = matrixA ^ 8 * matrixA ^ 2 * matrixA := by
      rw [← pow_add, ← pow_succ]
    _ = powerA8 * powerA2 * matrixA := by
      rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add,
        show (4 : ℕ) = 2 + 2 from rfl, pow_add, h2, h4, h8]
    _ = 1 := h11

theorem unitC_pow_two : unitC ^ 2 = 1 := by
  apply Units.ext
  exact (pow_two matrixC).trans matrixC_mul_self

theorem unitD_pow_four : unitD ^ 4 = 1 := by
  have hB : matrixB * matrixB = 1 := by decide +kernel
  apply Units.ext
  change matrixD ^ 4 = 1
  calc
    matrixD ^ 4 = matrixD ^ 2 * matrixD ^ 2 := (pow_add _ 2 2)
    _ = matrixB * matrixB := by rw [← coe_coreB]; rfl
    _ = 1 := hB

theorem derivedGroup_le_actionGroup : derivedGroup ≤ actionGroup :=
  Subgroup.commutator_le_self actionGroup

theorem normalizer_actionGroup_le_normalizer_derivedGroup :
    Subgroup.normalizer (actionGroup : Set Matrix12ˣ) ≤
      Subgroup.normalizer (derivedGroup : Set Matrix12ˣ) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (⁅actionGroup, actionGroup⁆).map _ = ⁅actionGroup, actionGroup⁆
  rw [Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg]

private def c : actionGroup := ⟨unitC, unitC_mem_actionGroup⟩
private def d : actionGroup := ⟨unitD, unitD_mem_actionGroup⟩

private theorem abelianization_cd : Abelianization.of (c * d) = 1 := by
  let f : actionGroup →* Abelianization actionGroup := Abelianization.of
  have hc : c ^ 2 = 1 := Subtype.ext unitC_pow_two
  have hd : d ^ 4 = 1 := Subtype.ext unitD_pow_four
  have hcd : (c * d) ^ 11 = 1 := Subtype.ext coreA_pow_eleven
  have h4 : f (c * d) ^ 4 = 1 := by
    rw [map_mul, mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      ← map_pow, hc, map_one, one_pow, one_mul, ← map_pow, hd, map_one]
  have h11 : f (c * d) ^ 11 = 1 := by rw [← map_pow, hcd, map_one]
  have h12 : f (c * d) ^ 12 = 1 := by
    calc
      f (c * d) ^ 12 = (f (c * d) ^ 4) ^ 3 := pow_mul _ 4 3
      _ = 1 := by rw [h4, one_pow]
  change f (c * d) ^ (11 + 1) = 1 at h12
  rw [pow_add, h11, pow_one, one_mul] at h12
  exact h12

theorem coreA_mem_derivedGroup : coreA ∈ derivedGroup := by
  rw [derivedGroup, ← Subgroup.map_subtype_commutator]
  refine Subgroup.mem_map.mpr ⟨c * d, ?_, rfl⟩
  rw [← Abelianization.ker_of]
  exact abelianization_cd

theorem coreB_mem_derivedGroup : coreB ∈ derivedGroup := by
  rw [derivedGroup, ← Subgroup.map_subtype_commutator]
  refine Subgroup.mem_map.mpr ⟨d ^ 2, ?_, rfl⟩
  rw [← Abelianization.ker_of]
  change Abelianization.of (d ^ 2) = 1
  have hdc : Abelianization.of d = (Abelianization.of c)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by simpa only [map_mul] using abelianization_cd)
  rw [map_pow, hdc, inv_pow, ← map_pow,
    show c ^ 2 = 1 from Subtype.ext unitC_pow_two, map_one, inv_one]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
