module
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.Representation.ScalarCoinvariants

/-!
# Fixed and moved planes in the mutual-action comparison

The actual symmetric-matrix plane radical acts quadratically. The symplectic
perpendicular identity forces a sufficiently large actor's moved and fixed
spaces to coincide. Over the field of four elements both have binary dimension
four, and the fixed quotient has dimension four as well.

Source: Aschbacher--Smith, 11.4.1(2), printed p.776. This is the symplectic
model calculation; it does not assume either conflicting automizer rank.
-/

public noncomputable section
open Subgroup Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
variable {F : Type*} [Field F]

private theorem radical_quadratic
    (x : Sp F) (hx : x ∈ Plane.radical.map planeLocal.subtype)
    (y : Sp F) (hy : y ∈ Plane.radical.map planeLocal.subtype) (v : Vector F) :
    x • (y • v - v) = y • v - v := by
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  have hxm := Plane.radical_matrix (⟨x, hx⟩ : Plane.radical)
  have hym := Plane.radical_matrix (⟨y, hy⟩ : Plane.radical)
  change x.val.val *ᵥ (y.val.val *ᵥ v - v) = y.val.val *ᵥ v - v
  rw [hxm, hym]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks, Matrix.one_apply]

/-- A large actor in the plane radical has a fixed and moved binary four-space. -/
theorem plane_fixed_moved [Finite F] [Algebra (ZMod 2) F]
    (hF : Nat.card F = 4) (B : Subgroup (Sp F))
    (hB : B ≤ Plane.radical.map planeLocal.subtype) (hlarge : 4 < Nat.card B) :
    subspaceCommutator (restrictScalars (k := ZMod 2) (symplecticNatural 2)) ⊤ B =
      fixedSpace (restrictScalars (k := ZMod 2) (symplecticNatural 2)) B ∧
    Module.finrank (ZMod 2)
      (fixedSpace (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) B) = 4 ∧
    fixedCodim (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) B = 4 := by
  have hq := fun x hx y hy v => radical_quadratic x (hB hx) y (hB hy) v
  have he := large_quadratic_displacement_self_orthogonal B hq (hF ▸ hlarge)
  have hfix : TwoLocalCover.fixedSpace B = displacementSpace B := by
    rw [← orthogonal_displacementSpace, he]
  have hd : Module.finrank F (displacementSpace B) = 2 := by
    have hh := congrArg (fun W : Submodule F (Vector F) => Module.finrank F W) he
    rw [LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate] at hh
    have hv : Module.finrank F (Vector F) = 4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    have hl := (displacementSpace B).finrank_le
    rw [hv] at hh hl
    omega
  have hf : Module.finrank (ZMod 2) F = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    simpa [Nat.card_zmod, hF] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm
  have hb : fixedSpace (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) B =
      (TwoLocalCover.fixedSpace B).restrictScalars (ZMod 2) := by
    ext v
    exact ⟨fun h g hg => h ⟨g,hg⟩, fun h g => h g.val g.property⟩
  have hbd : Module.finrank (ZMod 2)
      (fixedSpace (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) B) = 4 := by
    rw [hb, hfix]
    change Module.finrank (ZMod 2) (displacementSpace B) = 4
    rw [← Module.finrank_mul_finrank (ZMod 2) F, hf, hd]
  refine ⟨?_, hbd, ?_⟩
  · rw [subspaceCommutator_top_eq_coinvariants]
    change Coinvariants.ker (restrictScalars (k := ZMod 2)
      ((symplecticNatural 2).comp B.subtype)) = _
    rw [coinvariantsKer_restrictScalars, hb, hfix]
  · have hh := fixedCodim_add_finrank
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) B
    have hv : Module.finrank (ZMod 2) (Vector F) = 8 := by
      rw [← Module.finrank_mul_finrank (ZMod 2) F, hf]
      simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hbd, hv] at hh
    omega
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
