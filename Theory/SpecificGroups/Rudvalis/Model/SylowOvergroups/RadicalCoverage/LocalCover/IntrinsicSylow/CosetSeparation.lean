module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.CosetData
import Mathlib.Tactic.FinCases

/-!
# Point separation for the twenty-one intrinsic cosets

Witnesses from `source/GenerateCosets.g` and `source/GenerateCosets.py`.
The computation uses the unchanged ATLAS max4 and local words; see
`SylowOvergroups.Definitions` for attribution. GAP output is not trusted: all
permutation identities and separating points are checked by Lean.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Cosets
open Theory.GroupTheory Rudvalis.OrderCertificate
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem generator_preserves : ∀ (i : Fin 8) (x : Fin 4060),
    x ∈ points → P.L0.gen i x ∈ points := by
  apply allFin₂
  decide +kernel

public theorem preserves (g : Equiv.Perm (Fin 4060)) (hg : g ∈ P.L0.subgroup)
    (x : Fin 4060) (hx : x ∈ points) : g x ∈ points := by
  obtain ⟨w, rfl⟩ := hg
  induction w with
  | nil => exact hx
  | cons i w ih => exact generator_preserves i _ ih

private theorem point_mem : ∀ k, point k ∈ points := by decide +kernel

set_option maxRecDepth 30000 in
private theorem separate : ∀ i j : Fin 21, i ≠ j →
    (rep i * (rep j)⁻¹) (point (sep i j)) ∉ points := by
  decide +kernel

/-- Distinct representative words belong to distinct right cosets. -/
public theorem separation (i j : Fin 21)
    (h : rep i * (rep j)⁻¹ ∈ P.L0.subgroup) : i = j := by
  by_contra hij
  exact separate i j hij (preserves _ h _ (point_mem _))

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Cosets
