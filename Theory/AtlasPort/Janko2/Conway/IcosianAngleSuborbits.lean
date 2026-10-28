/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianAngleSuborbits.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveAngles
public import Theory.AtlasPort.Janko2.Conway.IcosianSixSuborbits

/-!
# IcosianAngleSuborbits

The six intrinsic Hermitian angle levels are the full point-stabilizer orbits.
Transport to a coordinate axis reduces the assertion to the proved six coordinate-norm suborbits.

Source: Gerald Höhn, `Atlas/Conway/IcosianAngleSuborbits.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open MulAction

theorem icosianRootPointAngle_axis_eq_iff (q r : IcosianRootPoint) :
    icosianRootPointAngle (icosianRootAxisPoint 0) q =
      icosianRootPointAngle (icosianRootAxisPoint 0) r ↔
      icosianRootPointNormWord q 0 = icosianRootPointNormWord r 0 := by
  rw [icosianRootPointAngle_axis,icosianRootPointAngle_axis,
    div_left_inj' (by decide +kernel : (4 : GoldenRational) ≠ 0)]
  exact goldenIntegerToRational_injective.eq_iff

/-- Every level of the intrinsic angle is a genuine full stabilizer orbit,
for every base line of the actual quaternionic Leech geometry. -/
theorem icosianRootPointAngle_stabilizer_orbit (p q : IcosianRootPoint) :
    orbit (stabilizer icosianHermitianGroup p) q =
      {r : IcosianRootPoint | icosianRootPointAngle p r = icosianRootPointAngle p q} := by
  ext r
  constructor
  · rintro ⟨h,rfl⟩
    have he := icosianRootPointAngle_smul h.val p q
    rw [h.property] at he
    exact he
  · intro hr
    obtain ⟨g,hg⟩ := icosianRootPoint_normalizers p
    have hn : icosianRootPointNormWord (g⁻¹ • r) 0 =
        icosianRootPointNormWord (g⁻¹ • q) 0 := by
      apply (icosianRootPointAngle_axis_eq_iff _ _).mp
      have hq := icosianRootPointAngle_smul g (icosianRootAxisPoint 0) (g⁻¹ • q)
      have ht := icosianRootPointAngle_smul g (icosianRootAxisPoint 0) (g⁻¹ • r)
      rw [hg,smul_inv_smul] at hq ht
      exact ht.symm.trans (hr.trans hq)
    have ho : g⁻¹ • r ∈ orbit icosianFullAxisStabilizer (g⁻¹ • q) := by
      rw [icosianFullAxisStabilizer_orbit]
      exact hn
    obtain ⟨h,hh⟩ := ho
    change h.val • (g⁻¹ • q) = g⁻¹ • r at hh
    have hm : g*h.val*g⁻¹ ∈ stabilizer icosianHermitianGroup p := by
      change (g*h.val*g⁻¹) • p = p
      rw [mul_smul,mul_smul,← hg,inv_smul_smul,h.property]
    refine ⟨⟨g*h.val*g⁻¹,hm⟩,?_⟩
    change (g*h.val*g⁻¹) • q = r
    rw [mul_smul,mul_smul,hh,smul_inv_smul]

theorem icosianRootPointAngle_projective_stabilizer_orbit (p q : IcosianRootPoint) :
    orbit (stabilizer IcosianProjectiveModel p) q =
      {r : IcosianRootPoint | icosianRootPointAngle p r = icosianRootPointAngle p q} := by
  rw [icosianProjectiveStabilizer_orbit,icosianRootPointAngle_stabilizer_orbit]

theorem icosianRootPointAngle_projective_orbit_card (p q : IcosianRootPoint) (k : Fin 6)
    (hk : icosianRootPointAngle p q = icosianRootPointAngleValues k) :
    Nat.card (orbit (stabilizer IcosianProjectiveModel p) q) = ![1,10,160,80,32,32] k := by
  rw [Nat.card_congr (Equiv.setCongr (icosianRootPointAngle_projective_stabilizer_orbit p q)),hk]
  exact icosianRootPointAngleLevel_card p k

end Atlas.Conway
