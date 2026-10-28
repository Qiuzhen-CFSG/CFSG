/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionOrders.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianIwasawa

/-!
# IcosianReflectionOrders

Every projective root reflection has order two, and its cyclic subgroup is central
in the full point stabilizer. Conjugacy with an axis reflection proves nontriviality; covariance proves centrality.

Source: Gerald Höhn, `Atlas/Conway/IcosianReflectionOrders.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

public section

noncomputable section
namespace Atlas.Conway

/-- Every actual projective root reflection is nontrivial, by conjugacy with an axis reflection. -/
theorem icosianProjectiveReflection_ne_one (p : IcosianRootPoint) :
    icosianProjectiveReflection p ≠ 1 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq IcosianProjectiveModel (icosianRootAxisPoint 0) p
  intro hp
  have he := icosianProjectiveReflection_conjugate g (icosianRootAxisPoint 0)
  rw [hg,hp] at he
  have hh := congrArg (fun x : IcosianProjectiveModel => g⁻¹*x*g) he
  simp only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] at hh
  exact icosianProjectiveAxisReflection_ne_one 0
    ((icosianProjectiveAxisReflection_line 0).trans hh)

theorem icosianProjectiveReflection_order (p : IcosianRootPoint) :
    orderOf (icosianProjectiveReflection p) = 2 :=
  orderOf_eq_prime (by simpa only [pow_two] using icosianProjectiveReflection_square p)
    (icosianProjectiveReflection_ne_one p)

theorem icosianProjectiveLineInvolutions_card (p : IcosianRootPoint) :
    Nat.card (icosianProjectiveLineInvolutions p) = 2 := by
  rw [icosianProjectiveLineInvolutions,Nat.card_zpowers,icosianProjectiveReflection_order]

/-- The local reflection subgroup is central in the full point stabilizer. -/
theorem icosianProjectiveLineInvolutions_central (p : IcosianRootPoint) :
    (icosianProjectiveLineInvolutions p).subgroupOf
      (MulAction.stabilizer IcosianProjectiveModel p) ≤
        Subgroup.center (MulAction.stabilizer IcosianProjectiveModel p) := by
  intro a ha
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  have hgc : g.val*icosianProjectiveReflection p=icosianProjectiveReflection p*g.val := by
    have h := icosianProjectiveReflection_conjugate g.val p
    rw [g.property] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hle : icosianProjectiveLineInvolutions p ≤
      Subgroup.centralizer ({g.val} : Set IcosianProjectiveModel) := by
    apply Subgroup.zpowers_le.mpr
    exact Subgroup.mem_centralizer_singleton_iff.mpr hgc.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm

end Atlas.Conway
