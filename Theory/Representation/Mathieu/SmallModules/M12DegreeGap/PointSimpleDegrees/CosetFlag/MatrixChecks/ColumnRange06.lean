module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks.ColumnRange05

/-!
# Inverse and action columns 360 through 419

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

private theorem columns0 : ∀ k : Fin 10, columnCertificate (360 + k.val) := by
  unfold columnCertificate
  decide +kernel

private theorem columns1 : ∀ k : Fin 10, columnCertificate (370 + k.val) := by
  unfold columnCertificate
  decide +kernel

private theorem columns2 : ∀ k : Fin 10, columnCertificate (380 + k.val) := by
  unfold columnCertificate
  decide +kernel

private theorem columns3 : ∀ k : Fin 10, columnCertificate (390 + k.val) := by
  unfold columnCertificate
  decide +kernel

private theorem columns4 : ∀ k : Fin 10, columnCertificate (400 + k.val) := by
  unfold columnCertificate
  decide +kernel

private theorem columns5 : ∀ k : Fin 10, columnCertificate (410 + k.val) := by
  unfold columnCertificate
  decide +kernel

theorem columnRange06 (j : Fin 60) : columnCertificate (360 + j.val) := by
  have all (b : Fin 6) (k : Fin 10) : columnCertificate (360 + 10 * b.val + k.val) := by
    fin_cases b
    · exact columns0 k
    · exact columns1 k
    · exact columns2 k
    · exact columns3 k
    · exact columns4 k
    · exact columns5 k
  have h := all ⟨j.val / 10, by omega⟩ ⟨j.val % 10, Nat.mod_lt _ (by decide)⟩
  change columnCertificate (360 + 10 * (j.val / 10) + j.val % 10) at h
  rwa [show 360 + 10 * (j.val / 10) + j.val % 10 = 360 + j.val by omega] at h

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.MatrixChecks
