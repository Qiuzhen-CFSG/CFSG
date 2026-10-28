module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks.ColumnRange11
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks.BlockChecks

/-!
# Assembly of all columns and diagonal blocks

Kernel-checked packed arithmetic on the unchanged published witnesses.
The import chain keeps expensive range compilations sequential and
retains completed ranges in the artifact cache. Each local batch checks
ten columns, without increasing any resource limit.

Source: James, J. Algebra 27 (1973), 57–111; witness conventions in
`PointSimpleDegrees/source/README.md`. Regenerate with `source/generate.py`.
-/

set_option Elab.async false

public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks
open Data

/-- The inverse and both actions on every published column. -/
theorem all_columns (j : Fin 720) : columnCertificate j.val := by
  have all (b : Fin 12) (k : Fin 60) : columnCertificate (60 * b.val + k.val) := by
    fin_cases b
    · exact columnRange00 k
    · exact columnRange01 k
    · exact columnRange02 k
    · exact columnRange03 k
    · exact columnRange04 k
    · exact columnRange05 k
    · exact columnRange06 k
    · exact columnRange07 k
    · exact columnRange08 k
    · exact columnRange09 k
    · exact columnRange10 k
    · exact columnRange11 k
  have h := all ⟨j.val / 60, by omega⟩ ⟨j.val % 60, Nat.mod_lt _ (by decide)⟩
  change columnCertificate (60 * (j.val / 60) + j.val % 60) at h
  rwa [show 60 * (j.val / 60) + j.val % 60 = j.val by omega] at h

/-- The zero tails and canonical diagonal slices for all 33 layers. -/
theorem all_blocks (t : Factor) : blockCertificate t := BlockChecks.all_blocks t

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks
