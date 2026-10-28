module
public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Separation.FixedRows
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# A certified three-point set for the concrete Thompson action

The fixed matrix carrier acts on row vectors by right inverse multiplication
and on sets by images. The six identities in `FixedRows` prove that both exact
subgroup words fix the set of three nonzero rows of the displayed binary plane.
Orbit-stabilizer then bounds its actual orbit cardinality by the subgroup index.
No orbit cardinality or group order is assumed or asserted.

The row data, certificate producer, and ATLAS provenance are documented in
`Separation/source/README.md`.
-/

namespace Thompson.OrderCertificate.Separation
open scoped Pointwise

/-- Rows with the contragredient action of the fixed Thompson matrix carrier. -/
@[ext] public structure RowVector where
  entries : Fin 248 → ZMod 2

public instance : Finite RowVector :=
  Finite.of_injective RowVector.entries (fun _ _ h => RowVector.ext h)

public instance rowMulAction : MulAction Model RowVector where
  smul g v := ⟨Matrix.vecMul v.entries (matrixHom g⁻¹)⟩
  one_smul v := by
    apply RowVector.ext
    change Matrix.vecMul v.entries (matrixHom (1 : Model)⁻¹) = v.entries
    simp
  mul_smul g h v := by
    apply RowVector.ext
    change Matrix.vecMul v.entries (matrixHom (g * h)⁻¹) =
      Matrix.vecMul (Matrix.vecMul v.entries (matrixHom h⁻¹)) (matrixHom g⁻¹)
    rw [mul_inv_rev, map_mul, Matrix.vecMul_vecMul]

public theorem inv_smul_row (g : Model) (v : Fin 248 → ZMod 2) :
    g⁻¹ • RowVector.mk v = RowVector.mk (Matrix.vecMul v (matrixHom g)) := by
  change RowVector.mk (Matrix.vecMul v (matrixHom (g⁻¹)⁻¹)) = _
  rw [inv_inv]

@[expose] public def fixedTriple : Set RowVector :=
  {⟨fixedRow0⟩, ⟨fixedRow1⟩, ⟨fixedRow2⟩}

public theorem localA_fixedTriple : localA • fixedTriple = fixedTriple := by
  suffices h : localA⁻¹ • fixedTriple = fixedTriple from (inv_smul_eq_iff.mp h).symm
  change (fun v : RowVector => localA⁻¹ • v) '' fixedTriple = fixedTriple
  simp only [fixedTriple, Set.image_insert_eq, Set.image_singleton, inv_smul_row,
    fixedRow0_localA, fixedRow1_localA, fixedRow2_localA]

public theorem localB_fixedTriple : localB • fixedTriple = fixedTriple := by
  suffices h : localB⁻¹ • fixedTriple = fixedTriple from (inv_smul_eq_iff.mp h).symm
  change (fun v : RowVector => localB⁻¹ • v) '' fixedTriple = fixedTriple
  simp only [fixedTriple, Set.image_insert_eq, Set.image_singleton, inv_smul_row,
    fixedRow0_localB, fixedRow1_localB, fixedRow2_localB]
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

public theorem fixedTriple_ncard : fixedTriple.ncard = 3 := by
  have h01 : (RowVector.mk fixedRow0) ≠ ⟨fixedRow1⟩ := by
    intro h
    have he := congrArg (fun v : RowVector => v.entries 0) h
    exact (by decide +kernel : fixedRow0 0 ≠ fixedRow1 0) he
  have h02 : (RowVector.mk fixedRow0) ≠ ⟨fixedRow2⟩ := by
    intro h
    have he := congrArg (fun v : RowVector => v.entries 1) h
    exact (by decide +kernel : fixedRow0 1 ≠ fixedRow2 1) he
  have h12 : (RowVector.mk fixedRow1) ≠ ⟨fixedRow2⟩ := by
    intro h
    have he := congrArg (fun v : RowVector => v.entries 0) h
    exact (by decide +kernel : fixedRow1 0 ≠ fixedRow2 0) he
  rw [fixedTriple, Set.ncard_insert_of_notMem, Set.ncard_pair h12]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨h01, h02⟩

public theorem fixedTriple_orbit_card_le_index :
    (MulAction.orbit Model fixedTriple).ncard ≤ localSubgroup.index :=
  localSubgroup_orbit_card_le_index fixedTriple localA_fixedTriple localB_fixedTriple

end Thompson.OrderCertificate.Separation
