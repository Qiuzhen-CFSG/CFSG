/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianProjectiveReflections.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianOrder
public import Theory.AtlasPort.Janko2.GroupTheory.FrameReflectionCommutator

/-!
# IcosianProjectiveReflections

Root-line reflections generate the sign quotient. A coordinate frame gives an
explicit commutator, and conjugation equivariance with transitivity proves
perfectness.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianProjectiveReflections.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
open scoped commutatorElement

def icosianProjectiveReflection (p : IcosianRootPoint) : IcosianProjectiveModel :=
  icosianProjectiveProjection (icosianLineReflection p)

theorem icosianProjectiveReflection_square (p : IcosianRootPoint) :
    icosianProjectiveReflection p*icosianProjectiveReflection p=1 := by
  rw [icosianProjectiveReflection,← map_mul,icosianLineReflection_square,map_one]

theorem icosianProjectiveReflection_conjugate (g : IcosianProjectiveModel)
    (p : IcosianRootPoint) :
    g*icosianProjectiveReflection p*g⁻¹=icosianProjectiveReflection (g • p) := by
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective icosianCentralSigns g
  change icosianProjectiveProjection g*icosianProjectiveProjection (icosianLineReflection p)*
    (icosianProjectiveProjection g)⁻¹=icosianProjectiveReflection (icosianProjectiveProjection g • p)
  rw [icosianProjectivePointAction_mk,icosianProjectiveReflection,← map_inv,← map_mul,← map_mul,
    icosianLineReflection_conjugate]

theorem icosianProjectiveReflection_generation :
    Subgroup.closure (Set.range icosianProjectiveReflection)=⊤ := by
  have hr : Set.range icosianProjectiveReflection=
      icosianProjectiveProjection '' Set.range icosianLineReflection :=
    Set.range_comp _ _
  rw [hr,← MonoidHom.map_closure]
  change icosianReflectionGroup.map icosianProjectiveProjection=⊤
  rw [icosianReflectionGroup_eq_top,← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

instance icosianHermitian_rootPoint_pretransitive :
    MulAction.IsPretransitive icosianHermitianGroup IcosianRootPoint where
  exists_smul_eq p q := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq icosianReflectionGroup p q
    exact ⟨g.val,hg⟩

instance icosianProjective_rootPoint_pretransitive :
    MulAction.IsPretransitive IcosianProjectiveModel IcosianRootPoint where
  exists_smul_eq p q := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq icosianHermitianGroup p q
    exact ⟨icosianProjectiveProjection g,hg⟩

def icosianProjectiveAxisReflection (i : Fin 3) : IcosianProjectiveModel :=
  icosianProjectiveProjection (icosianAxisReflection i)

theorem icosianProjectiveAxisReflection_line (i : Fin 3) :
    icosianProjectiveAxisReflection i=icosianProjectiveReflection (icosianRootAxisPoint i) := by
  unfold icosianProjectiveAxisReflection icosianProjectiveReflection icosianRootAxisPoint
  rw [icosianLineReflection_root]
  rfl

theorem icosianProjectiveAxisReflection_square (i : Fin 3) :
    icosianProjectiveAxisReflection i*icosianProjectiveAxisReflection i=1 := by
  rw [icosianProjectiveAxisReflection_line]
  exact icosianProjectiveReflection_square _

theorem icosianProjectiveAxisReflection_comm (i j : Fin 3) :
    icosianProjectiveAxisReflection i*icosianProjectiveAxisReflection j=
      icosianProjectiveAxisReflection j*icosianProjectiveAxisReflection i := by
  unfold icosianProjectiveAxisReflection
  rw [← map_mul,← map_mul,icosianAxisReflection_mul_comm]

theorem icosianProjectiveAxisReflection_product :
    icosianProjectiveAxisReflection 0*icosianProjectiveAxisReflection 1*
      icosianProjectiveAxisReflection 2=1 := by
  unfold icosianProjectiveAxisReflection
  rw [← map_mul,← map_mul]
  change icosianProjectiveProjection icosianCentralSign=1
  exact (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)

def icosianProjectiveAxisCycle : IcosianProjectiveModel :=
  icosianProjectiveProjection (icosianMonomialToHermitian
    (icosianPureBlockPermutation (Equiv.swap 0 1*Equiv.swap 1 2)))

theorem icosianProjectiveAxisCycle_axis :
    icosianProjectiveAxisCycle • icosianRootAxisPoint 0=icosianRootAxisPoint 1 := by
  unfold icosianProjectiveAxisCycle
  rw [icosianProjectivePointAction_mk,icosianPureBlockPermutation_axis]
  rfl

/-- The required explicit frame commutator in the actual sign quotient. -/
theorem icosianProjective_frame_commutator :
    ⁅icosianProjectiveAxisCycle,icosianProjectiveAxisReflection 0⁆=
      icosianProjectiveAxisReflection 2 := by
  apply Atlas.GroupTheory.frame_involution_commutator _ (icosianProjectiveAxisReflection 1) _ _
    (icosianProjectiveAxisReflection_square 0) (icosianProjectiveAxisReflection_square 1)
    (icosianProjectiveAxisReflection_square 2) (icosianProjectiveAxisReflection_comm 0 1)
    icosianProjectiveAxisReflection_product
  rw [icosianProjectiveAxisReflection_line,icosianProjectiveAxisReflection_line,
    icosianProjectiveReflection_conjugate,icosianProjectiveAxisCycle_axis]

theorem icosianProjective_perfect : Group.IsPerfect IcosianProjectiveModel :=
  Atlas.GroupTheory.perfect_of_transitive_commutator_family icosianProjectiveReflection
    icosianProjectiveReflection_conjugate icosianProjectiveReflection_generation
    (icosianRootAxisPoint 2) icosianProjectiveAxisCycle (icosianProjectiveAxisReflection 0)
    (icosianProjective_frame_commutator.trans (icosianProjectiveAxisReflection_line 2))

end Atlas.Conway
