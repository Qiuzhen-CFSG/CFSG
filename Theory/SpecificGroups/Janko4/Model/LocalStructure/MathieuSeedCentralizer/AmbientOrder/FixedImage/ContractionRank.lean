module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage.Invariants

/-!
# Exterior contraction rank on the literal seed fixed space

Evaluation of restricted exterior forms at a fixed vector gives a subspace of
linear functionals (represented here as functions). An automorphism preserving
the restricted exterior space identifies these evaluation spaces by precomposition.
Their dimensions are therefore invariant under the entire ambient centralizer.

This is the restriction construction for the max1 seed, not the homology
construction for the first ambient involution. The matrix certificates and source
provenance are those of `FixedImage.Invariants`. No finite rank fibre or orbit
identification is asserted here.
-/

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage

/-- Contract the restricted forms with a fixed column. -/
def evaluation (u : fixedVectors) :
    exteriorSpace →ₗ[ZMod 2] (fixedVectors → ZMod 2) where
  toFun R := R.val u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The subspace of functions obtained by contraction. -/
def contractionSpace (u : fixedVectors) : Submodule (ZMod 2) (fixedVectors → ZMod 2) :=
  (evaluation u).range

/-- Dimension of the contraction space, independent of coordinates. -/
noncomputable def contractionRank (u : fixedVectors) : ℕ :=
  Module.finrank (ZMod 2) (contractionSpace u)

private def pullbackLinear (g : invariantStabilizer) : exteriorSpace →ₗ[ZMod 2] exteriorSpace where
  toFun R := ⟨pullback g.val R, (g.property.2 R).mpr R.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem pullbackLinear_surjective (g : invariantStabilizer) :
    Function.Surjective (pullbackLinear g) := by
  intro R
  refine ⟨pullbackLinear g⁻¹ R, ?_⟩
  apply Subtype.ext
  change pullback g.val (pullback (g⁻¹).val R.val) = R.val
  rw [← pullback_mul]
  simp only [Subgroup.coe_inv, inv_mul_cancel, pullback_one]

private def rowEquiv (g : Actor) :
    (fixedVectors → ZMod 2) ≃ₗ[ZMod 2] (fixedVectors → ZMod 2) where
  toFun f v := f (g.val v)
  invFun f v := f (g⁻¹.val v)
  left_inv f := by
    funext v
    change f ((g * g⁻¹).val v) = f v
    rw [mul_inv_cancel]
    rfl
  right_inv f := by
    funext v
    change f ((g⁻¹ * g).val v) = f v
    rw [inv_mul_cancel]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evaluation_transport (g : invariantStabilizer) (u : fixedVectors) :
    (rowEquiv g.val).toLinearMap.comp (evaluation (g.val.val u)) =
      (evaluation u).comp (pullbackLinear g) := rfl

private theorem contractionSpace_transport (g : invariantStabilizer) (u : fixedVectors) :
    (contractionSpace (g.val.val u)).map (rowEquiv g.val).toLinearMap =
      contractionSpace u := by
  change (evaluation (g.val.val u)).range.map _ = (evaluation u).range
  rw [← LinearMap.range_comp, evaluation_transport]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (pullbackLinear_surjective g))

/-- Every automorphism preserving the restricted exterior space preserves rank. -/
theorem contractionRank_invariant (g : invariantStabilizer) (u : fixedVectors) :
    contractionRank (g.val.val u) = contractionRank u := by
  exact ((rowEquiv g.val).finrank_map_eq (contractionSpace (g.val.val u))).symm.trans
    (congrArg (fun P : Submodule (ZMod 2) (fixedVectors → ZMod 2) =>
      Module.finrank (ZMod 2) P) (contractionSpace_transport g u))

/-- Rank invariance for all actors of the full ambient seed centralizer. -/
theorem contractionRank_fixedAction (c : Centralizer) (u : fixedVectors) :
    contractionRank ((fixedAction c).val u) = contractionRank u :=
  contractionRank_invariant
    ⟨fixedAction c, fixedAction_range_le_invariantStabilizer ⟨c, rfl⟩⟩ u

end Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage
