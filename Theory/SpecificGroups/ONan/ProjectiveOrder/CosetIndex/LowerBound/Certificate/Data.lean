module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.LowerBound.Certificate.Data.Table

/-!
# The concrete fixed-plane orbit input

The 122760 literal nodes retain the breadth-first order of the untrusted
`LowerBound/source/GenerateOrbit.py` output. Bounded kernel checks certify
canonical first rows, reduced row bases and decreasing parents. The root is
checked against `fixedPlaneRows` itself. Balanced lookup makes the same exact
rows and coefficients available to the independent edge and distinctness
certificates. See `Data/source/README.md` for reproduction and source attribution.
-/

@[expose] public section

namespace ONan.OrderCertificate
open ReducedData

/-- The shared numerical input for the fixed-plane orbit certificate. -/
def fixedPlaneOrbitData : PackedOrbitData where
  rowCode i := (table i.val).row
  coefficientCode i := (table i.val).coeff
  pivot i := (table i.val).pattern.pivot
  parent i := ⟨(table i.val).parent % 122760, Nat.mod_lt _ (by decide)⟩
  letter i := (table i.val).letter

/-- The initial numerical basis is the previously specified fixed plane. -/
theorem fixedPlaneOrbitData_root : fixedPlaneOrbitData.rows 0 = fixedPlaneRows := by
  apply Matrix.ext
  intro r j
  revert r j
  exact @of_decide_eq_true _ (
    @Nat.decidableForallFin 8 _ (fun r =>
      @Nat.decidableForallFin 45 _ (fun j =>
        ZMod.decidableEq 7 (fixedPlaneOrbitData.rows 0 r j) (fixedPlaneRows r j)))) rfl

/-- Every nonroot parent occurs earlier in the enumeration. -/
theorem fixedPlaneOrbitData_parent_lt : ∀ i, i ≠ 0 → fixedPlaneOrbitData.parent i < i := by
  intro i hi
  have h := check_parent (table_checked i.val (Nat.zero_le _) i.isLt)
    (by simpa only [ne_eq, Fin.ext_iff, Fin.val_zero] using hi)
  change (table i.val).parent % 122760 < i.val
  rw [Nat.mod_eq_of_lt (lt_trans h i.isLt)]
  exact h

/-- Each stored matrix is a reduced basis with its stored pivot pattern. -/
theorem fixedPlaneOrbitData_reduced : ∀ i,
    Matrix.IsReducedRowBasis (fixedPlaneOrbitData.rows i) (fixedPlaneOrbitData.pivot i) :=
  fun i => check_reduced (table_checked i.val (Nat.zero_le _) i.isLt)

/-- First-row codes have bounded length and canonical field digits. -/
theorem fixedPlaneOrbitData_valid_first_rows : ∀ i,
    ValidOrbitRowCode 45 (fixedPlaneOrbitData.rowCode i 0) :=
  fun i => check_valid (table_checked i.val (Nat.zero_le _) i.isLt)

end ONan.OrderCertificate
