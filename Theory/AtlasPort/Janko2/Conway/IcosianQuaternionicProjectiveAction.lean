/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianQuaternionicProjectiveAction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveModel

/-!
# IcosianQuaternionicProjectiveAction

The full quaternionic projective-plane action has precisely the two signs as kernel.
Restriction to the root lines proves one inclusion; scalar negation proves the converse and gives a faithful quotient action.

Source: Gerald Höhn, `Atlas/Conway/IcosianQuaternionicProjectiveAction.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianCentralSign_fixes_projective (p : IcosianQuaternionPoint) :
    icosianCentralSign • p=p := by
  induction p using Projectivization.ind with
  | h x hx =>
    rw [Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
    refine ⟨MulOpposite.op (-1 : IcosianQuaternion),?_⟩
    change MulOpposite.op (-1 : IcosianQuaternion) • x=icosianCentralSign.val x
    rw [icosianCentralSign_apply]
    funext i
    simp

theorem icosian_quaternionic_projective_kernel :
    (MulAction.toPermHom icosianHermitianGroup IcosianQuaternionPoint).ker=icosianCentralSigns := by
  ext g
  constructor
  · intro hg
    apply icosian_fix_rootPoints_eq_sign g
    intro p
    apply Subtype.ext
    exact DFunLike.congr_fun hg p.val
  · intro hg
    apply Equiv.ext
    intro p
    change g • p=p
    rcases hg with rfl|rfl
    · exact one_smul _ _
    · exact icosianCentralSign_fixes_projective p

/-- The action on the entire quaternionic projective plane of the actual
rank-three right quaternion space, not just the finite315-line configuration. -/
def icosianQuaternionicProjectiveHom : IcosianProjectiveModel →* Equiv.Perm IcosianQuaternionPoint :=
  QuotientGroup.lift _ (MulAction.toPermHom icosianHermitianGroup IcosianQuaternionPoint)
    icosian_quaternionic_projective_kernel.ge

theorem icosianQuaternionicProjectiveHom_injective :
    Function.Injective icosianQuaternionicProjectiveHom :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr icosian_quaternionic_projective_kernel.symm

instance icosianQuaternionicProjectiveAction : MulAction IcosianProjectiveModel IcosianQuaternionPoint :=
  MulAction.compHom _ icosianQuaternionicProjectiveHom

instance icosianQuaternionicProjective_faithful : FaithfulSMul IcosianProjectiveModel IcosianQuaternionPoint where
  eq_of_smul_eq_smul h := icosianQuaternionicProjectiveHom_injective (Equiv.ext h)

theorem icosianQuaternionicProjectiveAction_mk (g : icosianHermitianGroup)
    (p : IcosianQuaternionPoint) : icosianProjectiveProjection g • p=g • p := rfl

theorem icosianProjectiveRootPoint_val_smul (g : IcosianProjectiveModel) (p : IcosianRootPoint) :
    (g • p).val=g • p.val := by
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective icosianCentralSigns g
  rfl

end Atlas.Conway
