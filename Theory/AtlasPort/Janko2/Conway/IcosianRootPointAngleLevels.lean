/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianRootPointAngleLevels.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointAngles
public import Theory.AtlasPort.Janko2.Conway.IcosianRootNormLevelCounts
public import Theory.AtlasPort.Janko2.Conway.IcosianPointNormalizations

/-!
# IcosianRootPointAngleLevels

The six normalized Hermitian angles exhaust the root-line geometry and have
cardinalities 1, 10, 160, 80, 32, and 32. Transport to a coordinate axis uses the proved norm-level counts.

Source: Gerald Höhn, `Atlas/Conway/IcosianRootPointAngleLevels.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped Matrix

abbrev IcosianRootPointAngleLevel (p : IcosianRootPoint) (a : GoldenRational) :=
  {q : IcosianRootPoint // icosianRootPointAngle p q = a}

def icosianRootPointAngleValues (k : Fin 6) : GoldenRational :=
  goldenIntegerToRational (icosianRootCoordinateLevels k) / 4

theorem icosianRootPointAngleValues_injective : Function.Injective icosianRootPointAngleValues := by
  intro i j h
  apply icosianRootCoordinateLevels_injective
  apply goldenIntegerToRational_injective
  exact (div_left_inj' (by decide +kernel : (4 : GoldenRational) ≠ 0)).mp h

theorem icosianRootPointAngle_axis_level (q : IcosianRootPoint) (k : Fin 6) :
    icosianRootPointAngle (icosianRootAxisPoint 0) q = icosianRootPointAngleValues k ↔
      icosianRootPointNormWord q 0 = icosianRootCoordinateLevels k := by
  rw [icosianRootPointAngle_axis]
  change _ / 4 = _ / 4 ↔ _
  rw [div_left_inj' (by decide +kernel : (4 : GoldenRational) ≠ 0)]
  exact goldenIntegerToRational_injective.eq_iff

def icosianRootPointAngleLevelEquiv (p : IcosianRootPoint)
    (g : icosianHermitianGroup) (hg : g • icosianRootAxisPoint 0 = p) (k : Fin 6) :
    IcosianRootPointAngleLevel p (icosianRootPointAngleValues k) ≃
      IcosianRootPointNormLevel 0 (icosianRootCoordinateLevels k) where
  toFun q := ⟨g⁻¹ • q.val, by
    apply (icosianRootPointAngle_axis_level _ k).mp
    have h := icosianRootPointAngle_smul g (icosianRootAxisPoint 0) (g⁻¹ • q.val)
    rw [hg,smul_inv_smul] at h
    exact h.symm.trans q.property⟩
  invFun q := ⟨g • q.val, by
    rw [← hg,icosianRootPointAngle_smul]
    exact (icosianRootPointAngle_axis_level _ k).mpr q.property⟩
  left_inv q := Subtype.ext (smul_inv_smul g q.val)
  right_inv q := Subtype.ext (inv_smul_smul g q.val)

theorem icosianRootPointAngleLevel_card (p : IcosianRootPoint) (k : Fin 6) :
    Nat.card (IcosianRootPointAngleLevel p (icosianRootPointAngleValues k)) =
      ![1,10,160,80,32,32] k := by
  obtain ⟨g,hg⟩ := icosianRootPoint_normalizers p
  rw [Nat.card_congr (icosianRootPointAngleLevelEquiv p g hg k),
    icosianRootPointNormLevel_six_card]

theorem icosianRootPointAngle_exhaustive (p q : IcosianRootPoint) :
    ∃ k : Fin 6, icosianRootPointAngle p q = icosianRootPointAngleValues k := by
  obtain ⟨g,hg⟩ := icosianRootPoint_normalizers p
  obtain ⟨k,hk⟩ := icosianRootPointNormLevel_exhaustive (g⁻¹ • q) 0
  refine ⟨k,?_⟩
  have h := icosianRootPointAngle_smul g (icosianRootAxisPoint 0) (g⁻¹ • q)
  rw [hg,smul_inv_smul] at h
  exact h.trans ((icosianRootPointAngle_axis_level _ k).mpr hk)

end Atlas.Conway
