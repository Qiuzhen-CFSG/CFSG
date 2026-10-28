module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-!
# Fixed vectors of A₆ involutions on the natural binary module

Every fixed vector of an involution in the natural four-dimensional module is
a displacement.  The canonical double transposition is checked directly in
the duad coordinates; all other involutions are transported to it by the
single involution class of A₆.

This is the finite model input used to correct involution lifts through the
binary conjugation section in the six-component source branch.
-/

@[expose] public section

open Subgroup BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.InvolutionFree

abbrev Ω := Fin 6
abbrev V := natural Ω

private def lineA : S := swap01 * swap23

private theorem lineA_fixed :
    LinearMap.ker (naturalRepresentation Ω lineA - LinearMap.id) = canonicalPlane := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rcases vector_cases v with rfl | ⟨d, rfl⟩
  · simp
  · change naturalRepresentation Ω lineA (pairVector d.val.1 d.val.2) =
      pairVector d.val.1 d.val.2 ↔ pairVector d.val.1 d.val.2 ∈ canonicalPlane
    rw [pairVector_map, pairVector_eq_iff (lineA.injective.ne (ne_of_lt d.property))
      (ne_of_lt d.property), pairVector_mem_plane_iff (ne_of_lt d.property)]
    have cert : ∀ i j : Ω, i < j →
        (pair (lineA i) (lineA j) = pair i j ↔ pair i j ∈ baseSyntheme) := by
      decide +kernel
    exact cert d.val.1 d.val.2 d.property

private theorem lineA_range :
    LinearMap.range (naturalRepresentation Ω lineA - LinearMap.id) = canonicalPlane := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, rfl⟩
    rw [← lineA_fixed]
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, map_sub]
    have hs : lineA * lineA = 1 := by decide
    rw [← Module.End.mul_apply, ← map_mul, hs, map_one, Module.End.one_apply]
    simp only [ZModModule.sub_eq_add, add_comm]
  · have h := (naturalRepresentation Ω lineA - LinearMap.id).finrank_range_add_finrank_ker
    rw [lineA_fixed, canonicalPlane_finrank,
      finrank_natural_even Ω (by decide)] at h
    change _ + 2 = 4 at h
    rw [canonicalPlane_finrank]
    exact Nat.add_right_cancel h

private theorem lineA_free (v : V) (hv : naturalRepresentation Ω lineA v = v) :
    ∃ w : V, naturalRepresentation Ω lineA w + w = v := by
  have hvk : v ∈ LinearMap.ker (naturalRepresentation Ω lineA - LinearMap.id) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact hv
  rw [lineA_fixed, ← lineA_range] at hvk
  rcases hvk with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  change naturalRepresentation Ω lineA w - w = v at hw
  simpa only [ZModModule.sub_eq_add] using hw

private theorem lineA_order : orderOf (⟨lineA, by decide⟩ : alternatingGroup Ω) = 2 := by
  exact orderOf_eq_prime (by decide) (by decide)

theorem fixed_is_displacement (a : alternatingGroup Ω) (ha : orderOf a = 2)
    (v : V) (hv : naturalRepresentation Ω a.val v = v) :
    ∃ w : V, naturalRepresentation Ω a.val w + w = v := by
  let a₀ : alternatingGroup Ω := ⟨lineA, by decide⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj a a₀ ha lineA_order)
  have hgs : (g : S) * a.val * (g : S)⁻¹ = a₀.val := congrArg Subtype.val hg
  have hfix : naturalRepresentation Ω a₀.val (naturalRepresentation Ω (g : S) v) =
      naturalRepresentation Ω (g : S) v := by
    rw [← hgs, ← Module.End.mul_apply, ← map_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one, map_mul, Module.End.mul_apply, hv]
  obtain ⟨w₀, hw₀⟩ := lineA_free (naturalRepresentation Ω (g : S) v) hfix
  have hmove : a.val * (g : S)⁻¹ = (g : S)⁻¹ * a₀.val := by
    calc
      a.val * (g : S)⁻¹ = (g : S)⁻¹ * ((g : S) * a.val * (g : S)⁻¹) := by group
      _ = (g : S)⁻¹ * a₀.val := by rw [hgs]
  refine ⟨naturalRepresentation Ω (g : S)⁻¹ w₀, ?_⟩
  calc
    naturalRepresentation Ω a.val (naturalRepresentation Ω (g : S)⁻¹ w₀) +
        naturalRepresentation Ω (g : S)⁻¹ w₀ =
      naturalRepresentation Ω (g : S)⁻¹ (naturalRepresentation Ω a₀.val w₀) +
        naturalRepresentation Ω (g : S)⁻¹ w₀ := by
          rw [← Module.End.mul_apply, ← map_mul, hmove, map_mul, Module.End.mul_apply]
    _ = naturalRepresentation Ω (g : S)⁻¹
        (naturalRepresentation Ω a₀.val w₀ + w₀) := by rw [map_add]
    _ = naturalRepresentation Ω (g : S)⁻¹ (naturalRepresentation Ω (g : S) v) := by
      rw [hw₀]
    _ = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.InvolutionFree
