module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.RepeatedSocle
/-!
# Whole-group and ratio conclusions for doubled SL3 modules

The defining-field displacement bound gives rank at most twice the field
degree for a quadratic subgroup; each nontrivial subgroup costs at least
the field degree on each natural copy. Thus the doubled action has quadratic
ratio at least one. Its literal occurrence in the original FF source forces
the original ratio to equal one, without a fixed-supplement assumption.

A.1.42 supplies a Sylow-stable natural submodule from repeated coordinates.
Full B.4.2 on its faithful LT action, and the natural half-ratio witness,
place every original Sylow offender inside L. Original generation gives G=L.
All actual central kernels and local subgroups are retained.

Source: Aschbacher--Smith B.5.1, printed p.101, case (I) and clause (1)(ii).
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
private theorem ratio_le_actionEquiv {H X : Type*} [Group H]
    [AddCommGroup X] [Module (ZMod 2) X] {σ : Representation (ZMod 2) H X}
    (e : ActionEquiv ρ σ) : quadraticRatio σ ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA,hq⟩
  have hAm : IsElementaryTwo (A.map e.groupEquiv.toMonoidHom) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_,IsElementaryAbelian.map _⟩
    intro hh
    apply hA.1
    apply Subgroup.map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
    simpa only [Subgroup.map_bot] using hh
  have hqm : IsQuadratic σ (A.map e.groupEquiv.toMonoidHom) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ w
    obtain ⟨v,rfl⟩ := e.linearEquiv.surjective w
    have hh := congrArg e.linearEquiv (hq a ha b hb v)
    change σ (e.groupEquiv a) (σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v) =
      σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v
    simpa only [e.intertwines,map_sub] using hh
  have hr : actionRatio σ (A.map e.groupEquiv.toMonoidHom) = actionRatio ρ A := by
    unfold actionRatio
    rw [← fixedCodim_map_equivariant ρ σ _ e.linearEquiv e.intertwines,
      rank_map_injective _ e.groupEquiv.injective]
  exact iInf_le_of_le (A.map e.groupEquiv.toMonoidHom) (iInf_le_of_le ⟨hAm,hqm⟩ hr.le)

/-- Fixed codimension doubles under the actual two-copy action. -/
theorem repeated_two_fixedCodim [FiniteDimensional (ZMod 2) V] (A : Subgroup G) :
    fixedCodim (repeated ρ 2) A = 2 * fixedCodim ρ A := by
  have he := fixedCodim_map_equivariant (repeated ρ 2) (ρ.prod ρ)
    (MonoidHom.id G) (LinearEquiv.finTwoArrow (R := ZMod 2) (M := V))
    (fun _ _ => rfl) A
  simpa only [Subgroup.map_id,fixedCodim_prod,two_mul] using he

/-- Every binary defining field satisfies the doubled-natural ratio lower bound. -/
theorem one_le_doubledThree_ratio (F : BinaryField) :
    1 ≤ quadraticRatio (repeated (linearNatural F 3) 2) := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA,hq⟩
  have hqN : IsQuadratic (linearNatural F 3) A := by
    intro a ha b hb v
    exact congrFun (hq a ha b hb (fun _ => v)) (0 : Fin 2)
  have hr := NaturalExtensions.LargerFieldThree.quadratic_three_rank_bound F hA.1 hqN
  have hp := (NaturalExtensions.LargerFieldThree.field_dimensions_pos F 3 hA.1).1
  have hc : F.degree ≤ fixedCodim (linearNatural F 3) A := by
    rw [ChapterK.Linear.Natural.fixedCodim_eq_field_codim]
    exact Nat.le_mul_of_pos_right _ hp
  have hbound : rank A ≤ fixedCodim (repeated (linearNatural F 3) 2) A := by
    rw [repeated_two_fixedCodim]
    omega
  have hr0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hA.rank_pos
  unfold actionRatio
  apply (ENNReal.le_div_iff_mul_le (Or.inl hr0) (Or.inl (by simp))).mpr
  simpa only [one_mul] using (show (rank A : ℝ≥0∞) ≤ fixedCodim (repeated (linearNatural F 3) 2) A by exact_mod_cast hbound)

/-- Restriction to an invariant subspace decreases the quadratic ratio. -/
theorem subrepresentation_quadraticRatio_le [FiniteDimensional (ZMod 2) V]
    (U : Subrepresentation ρ) : quadraticRatio U.toRepresentation ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA,hq⟩
  exact subrepresentation_ratio_le_actionRatio ρ U hA hq

/-- The original FF action with a doubled-natural moved module has ratio one. -/
theorem doubleThree_source_ratio [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hL : L = ⊤) (F : BinaryField)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F 3) 2)) : quadraticRatio ρ = 1 := by
  let := h.finite_module
  let c := ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv).symm
  let a : ActionEquiv s.space.toRepresentation (repeated (linearNatural F 3) 2) :=
    ⟨c.trans e.groupEquiv,e.linearEquiv,fun g v => e.intertwines (c g) v⟩
  apply le_antisymm
  · exact (isFFModule_iff_quadraticRatio_le_one ρ).mp (ExtensionConsequences.source_isFF h)
  · exact ((one_le_doubledThree_ratio F).trans (ratio_le_actionEquiv _ a)).trans
      (subrepresentation_quadraticRatio_le ρ s.space)

/-- On the original source domain, repeated SL3 coordinates force G=L. -/
theorem whole_of_repeatedThree_source [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (F : BinaryField) {r : ℕ}
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 r) :
    L = ⊤ := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let T : Sylow 2 G := Classical.choice inferInstance
  let H := L ⊔ (T : Subgroup G)
  let C := L.subgroupOf H
  let μ := s.space.toRepresentation
  let δ := μ.comp H.subtype
  let c : C ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv c.symm
  have hfit : generalizedFitting H = C :=
    IrreducibleBranch.local_generalizedFitting L T h.fitting h.twoCore T.isPGroup'
  have hfL : Function.Injective (μ.comp L.subtype) := by
    intro x y hxy
    apply IrreducibleBranch.component_faithful h s
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => exact congrArg s.central.toSubmodule.mkQ (LinearMap.congr_fun hxy v)
  have hfC : Function.Injective (δ.comp C.subtype) := by
    intro x y hxy
    apply c.injective
    exact hfL hxy
  have hfδ : Function.Injective δ := by
    apply IrreducibleBranch.faithful_of_fitting_restriction
    rwa [hfit]
  obtain ⟨a⟩ := hn
  have hnC : IsRepeatedLinearNatural (δ.comp C.subtype) F 3 r :=
    ⟨⟨c.trans a.groupEquiv,a.linearEquiv,fun g v => a.intertwines (c g) v⟩⟩
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  obtain ⟨I,hI,hsI⟩ := repeated_natural_stable_submodule δ hfδ C ((T : Subgroup G).subgroupOf H)
    ((Subgroup.nontrivial_iff_ne_bot C).mp inferInstance) T.isPGroup'.comap_subtype
    F (by decide : 2 ≤ 3) hnC
  have hs : (⊤ : Subgroup H) ≤ subspaceStabilizer δ I.toSubmodule := by
    rw [← subgroupOf_self H,subgroupOf_sup (show L ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right)]
    apply sup_le _ hsI
    apply le_subspaceStabilizer
    intro g hg v hv
    exact I.apply_mem_toSubmodule ⟨g,hg⟩ hv
  let J : Subrepresentation δ := ⟨I.toSubmodule,fun g v hv => (hs (Subgroup.mem_top g) v).2 hv⟩
  obtain ⟨e⟩ := hI
  let eJ : ActionEquiv (J.toRepresentation.comp C.subtype) (linearNatural F 3) :=
    ⟨e.groupEquiv,e.linearEquiv,fun g v => e.intertwines g v⟩
  have hfJ : Function.Injective (J.toRepresentation.comp C.subtype) := by
    intro x y he
    apply eJ.groupEquiv.injective
    apply ChapterK.Linear.Natural.natural_injective F 3
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := eJ.linearEquiv.surjective w
    rw [← eJ.intertwines,← eJ.intertwines]
    exact congrArg eJ.linearEquiv (LinearMap.congr_fun he v)
  have hf : Function.Injective J.toRepresentation := by
    apply IrreducibleBranch.faithful_of_fitting_restriction
    rwa [hfit]
  have hirr : IsIrreducible (J.toRepresentation.comp C.subtype) :=
    ExtensionConsequences.irreducible_of_equiv eJ
      (ExtensionConsequences.linearNatural_irreducible F (by decide))
  have hsq : IsSQTK K H := IrreducibleBranch.local_sqtk hK L T h.sqtk T.isPGroup'
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hiF : IsIrreducible (J.toRepresentation.comp (generalizedFitting H).subtype) := by rwa [hfit]
  have hhalf : quadraticRatio J.toRepresentation ≤ 1/2 := by
    simpa using ChapterK.Linear.Natural.quadraticRatio_le J.toRepresentation C F 3 eJ (by decide)
  apply IrreducibleBranch.whole_of_sylow_offenders_le ρ L T h.generated
  unfold generatedBy
  apply iSup_le
  intro B
  apply iSup_le
  rintro ⟨hB,hBT⟩
  have hBH : B ≤ H := hBT.trans le_sup_right
  have hbδ : IsBestOffender δ (B.subgroupOf H) :=
    (bestOffender_on_subrepresentation ρ s.space hB).subgroupOf μ hBH
  have hbJ := bestOffender_on_subrepresentation δ J hbδ
  have hc := earlier H _ J.toRepresentation hsq inferInstance hf hiF ⟨B.subgroupOf H,hbJ⟩
  have hgen := generated_of_half J.toRepresentation hc hhalf
  have hBC : B.subgroupOf H ≤ C := by
    rw [← hfit]
    exact (hbJ.le_offenderSubgroup J.toRepresentation).trans_eq hgen
  intro b hb
  exact hBC (show (⟨b,hBH hb⟩ : H) ∈ B.subgroupOf H from hb)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
