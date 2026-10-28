module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.MovedInduction

/-!
# The genuine moved source action inside LA

For any original best offender A, the local group LA has generalized Fitting
subgroup L and trivial two-core. Faithfulness on L makes its action on the
literal moved space faithful; the commutator equality [L,A]=L supplies offender
generation. Thus the complete source hypothesis restricts to this moved action
without assuming F*(G)=L globally. Failure of Irr⁺ passes through the actual
subspace inclusion and subgroup restriction.

Source: Aschbacher--Smith B.5.1, printed pp.99–102, observations α and β and
U=[V,L]. These reductions preserve both original component and offender.
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped ENNReal MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- On the literal moved module, adjoining any original best offender to L
preserves the complete source domain. F*(G)=L is not needed globally. -/
theorem local_moved_source_hypothesis
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    {A : Subgroup G} (hA : IsBestOffender ρ A) :
    QuasisimpleSourceHypothesis (s.space.toRepresentation.comp (L ⊔ A).subtype)
      K (L.subgroupOf (L ⊔ A)) := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let H := L ⊔ A
  let C := L.subgroupOf H
  let μ := s.space.toRepresentation.comp H.subtype
  have hp : IsPGroup 2 A := hA.1.2.isPGroup 2 A
  have hfit : generalizedFitting H = C :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  have hcore : pCore 2 H = ⊥ :=
    IrreducibleBranch.local_twoCore_eq_bot L H h.fitting h.twoCore le_sup_left
  let : IsQuasisimple C :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hfL : Function.Injective (s.space.toRepresentation.comp L.subtype) := by
    intro x y hxy
    apply IrreducibleBranch.component_faithful h s
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => exact congrArg s.central.toSubmodule.mkQ (LinearMap.congr_fun hxy v)
  have hfC : Function.Injective (μ.comp C.subtype) := by
    intro x y hxy
    apply (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).injective
    apply hfL
    exact hxy
  have hf : Function.Injective μ := by
    apply IrreducibleBranch.faithful_of_fitting_restriction
    rwa [hfit]
  have hb : IsBestOffender μ (A.subgroupOf H) :=
    (bestOffender_on_subrepresentation ρ s.space hA).subgroupOf s.space.toRepresentation le_sup_right
  let J := offenderSubgroup μ
  let : J.Normal := offenderSubgroup_normal μ
  have haJ : A.subgroupOf H ≤ J := hb.le_offenderSubgroup μ
  have hcomm : ⁅C, A.subgroupOf H⁆ = C := by
    simpa only [hfit] using QuasisimpleSections.commutator_fitting_eq hcore
      (inferInstance : IsQuasisimple (generalizedFitting H)) hb.1.1 (hb.1.2.isPGroup 2 _)
  have hcJ : C ≤ J := by
    rw [← hcomm]
    exact (commutator_mono le_rfl haJ).trans (commutator_le_right _ _)
  have hgen : J = ⊤ := by
    apply top_unique
    rw [← subgroupOf_self H, subgroupOf_sup (show L ≤ H from le_sup_left)
      (show A ≤ H from le_sup_right)]
    exact sup_le hcJ haJ
  refine ⟨inferInstance,hf,inferInstance,
    (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))).mpr h.sqtk,
    ?_,hcore,hgen⟩
  rw [hfit]
  apply (sup_of_le_left ?_).symm
  rw [← hfit]
  exact le_trans (show center H ≤ fittingSubgroup H from
    le_sSup ⟨inferInstance, inferInstance⟩) le_sup_left

omit [Finite G] in
/-- The actual local restriction has precisely the same moved vectors. -/
theorem local_moved_space {L : Subgroup G} (A : Subgroup G) :
    moved (ρ.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A)) = moved ρ L := by
  unfold moved subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨l,hl,w,hw,rfl⟩
    exact ⟨l.val,hl,w,hw,rfl⟩
  · rintro ⟨l,hl,w,hw,rfl⟩
    exact ⟨⟨l,(show L ≤ L ⊔ A from le_sup_left) hl⟩,hl,w,hw,rfl⟩

/-- Failure of Irr⁺ persists on the actual moved module and its LA restriction. -/
theorem local_moved_not_irrPlus
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (A : Subgroup G) (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) :
    ¬ IsIrrPlus (s.space.toRepresentation.comp (L ⊔ A).subtype)
      (L.subgroupOf (L ⊔ A))
      (moved (s.space.toRepresentation.comp (L ⊔ A).subtype) (L.subgroupOf (L ⊔ A))) := by
  rw [local_moved_space]
  intro hi
  exact moved_not_irrPlus ρ h s hnot
    ((IsIrrPlus.subgroupOf_iff s.space.toRepresentation L (L ⊔ A) le_sup_left _).mp hi)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
