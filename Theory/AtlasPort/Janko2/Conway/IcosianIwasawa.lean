/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianIwasawa.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveReflections
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionFixedLine
public import Theory.AtlasPort.Janko2.GroupTheory.IwasawaStabilizer

/-!
# IcosianIwasawa

Each line reflection generates an abelian normal subgroup of its point stabilizer.
Reflection generation and perfectness yield simplicity once primitivity is supplied.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianIwasawa.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open scoped commutatorElement

def icosianProjectiveLineInvolutions (p : IcosianRootPoint) : Subgroup IcosianProjectiveModel :=
  Subgroup.zpowers (icosianProjectiveReflection p)

theorem icosianProjectiveReflection_fixes (p : IcosianRootPoint) :
    icosianProjectiveReflection p • p=p :=
  icosianLineReflection_fixes p

theorem icosianProjectiveLineInvolutions_le_stabilizer (p : IcosianRootPoint) :
    icosianProjectiveLineInvolutions p≤MulAction.stabilizer IcosianProjectiveModel p :=
  Subgroup.zpowers_le.mpr (icosianProjectiveReflection_fixes p)

theorem icosianProjectiveLineInvolutions_normal (p : IcosianRootPoint) :
    ((icosianProjectiveLineInvolutions p).subgroupOf
      (MulAction.stabilizer IcosianProjectiveModel p)).Normal := by
  constructor
  intro a ha g
  have hgc : g.val*icosianProjectiveReflection p=icosianProjectiveReflection p*g.val := by
    have h := icosianProjectiveReflection_conjugate g.val p
    rw [show g.val • p=p from g.property] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hle : icosianProjectiveLineInvolutions p≤
      Subgroup.centralizer ({g.val} : Set IcosianProjectiveModel) := by
    apply Subgroup.zpowers_le.mpr
    exact Subgroup.mem_centralizer_singleton_iff.mpr hgc.symm
  have hc := (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm
  change g.val*a.val=a.val*g.val at hc
  change g.val*a.val*g.val⁻¹∈icosianProjectiveLineInvolutions p
  rw [hc,mul_inv_cancel_right]
  exact ha

theorem icosianProjectiveLineInvolutions_abelian (p : IcosianRootPoint) :
    IsMulCommutative (icosianProjectiveLineInvolutions p) := by
  unfold icosianProjectiveLineInvolutions
  infer_instance

theorem icosianProjectiveLineInvolutions_normalClosure (p : IcosianRootPoint) :
    Subgroup.normalClosure (icosianProjectiveLineInvolutions p : Set IcosianProjectiveModel)=⊤ := by
  apply top_unique
  rw [← icosianProjectiveReflection_generation]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨q,rfl⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq IcosianProjectiveModel p q
  rw [← hg,← icosianProjectiveReflection_conjugate]
  exact Subgroup.Normal.conj_mem inferInstance
    _ (Subgroup.subset_normalClosure (Subgroup.mem_zpowers _)) g

theorem icosianProjectiveAxisReflection_ne_one (i : Fin 3) :
    icosianProjectiveAxisReflection i≠1 := by
  intro h
  exact icosianAxisReflection_not_sign i ((QuotientGroup.eq_one_iff _).mp h)

instance icosianProjective_nontrivial : Nontrivial IcosianProjectiveModel :=
  ⟨⟨icosianProjectiveAxisReflection 0,1,icosianProjectiveAxisReflection_ne_one 0⟩⟩

theorem icosianProjective_nonabelian : ¬IsMulCommutative IcosianProjectiveModel := by
  let := icosianProjective_perfect
  exact Group.IsPerfect.not_isMulCommutative IcosianProjectiveModel

/-- The structural orbit theorem, still required separately, is the sole
geometric premise of this final application of the audited Iwasawa criterion. -/
theorem icosianProjective_simple_of_primitive
    [MulAction.IsPreprimitive IcosianProjectiveModel IcosianRootPoint] :
    IsSimpleGroup IcosianProjectiveModel := by
  let := icosianProjective_perfect
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple (icosianRootAxisPoint 0)
    (icosianProjectiveLineInvolutions (icosianRootAxisPoint 0))
    (icosianProjectiveLineInvolutions_le_stabilizer _)
    (icosianProjectiveLineInvolutions_normal _)
    (icosianProjectiveLineInvolutions_abelian _)
    (icosianProjectiveLineInvolutions_normalClosure _)

end Atlas.Conway
