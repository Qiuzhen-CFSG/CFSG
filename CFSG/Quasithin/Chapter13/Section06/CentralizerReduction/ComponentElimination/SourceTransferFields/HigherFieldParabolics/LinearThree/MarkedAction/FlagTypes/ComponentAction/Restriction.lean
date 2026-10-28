module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.FlagTypes.Preparation
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Restricting the literal component section to the offender actor

For C ≤ H, restriction of the actor preserves [V,C] and its quotient by
C_[V,C](C). The group identification is the actual subgroup inclusion and
the linear identification is the identity on this quotient. Consequently a
repeated natural action found inside H transports back without changing its
multiplicity or imposing a marking on the model group.

The adequate classifier's quasisimple branch identifies C with F*(H), by
containment between components. Its S₃ branch cannot contain a component.
The other three alternatives retain all their extension and quotient data.
The source-specific applications are in the parent ComponentAction module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1 and
B.5.6, printed pp.99–105; application before 13.6.14, printed p.929.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

/-- The moved and central spaces determine the section, including its action. -/
theorem movedSection_unique (s t : MovedSection ρ C) : s = t := by
  obtain ⟨S, hS, Z, hZ⟩ := s
  obtain ⟨T, hT, Y, hY⟩ := t
  have hST : S = T := Subrepresentation.ext (hS.trans hT.symm)
  subst T
  have hZY : Z = Y := Subrepresentation.ext (hZ.trans hY.symm)
  subst Y
  rfl

/-- Restriction keeps the literal moved subspace and its central kernel. -/
def restrictSection (s : MovedSection ρ C) (H : Subgroup D) (hCH : C ≤ H) :
    MovedSection (ρ.comp H.subtype) (C.subgroupOf H) where
  space := ⟨s.space.toSubmodule, fun g v hv => s.space.apply_mem_toSubmodule g hv⟩
  space_eq := by
    rw [s.space_eq]
    have h := subspaceCommutator_map_embedding (ρ.comp H.subtype) ρ H.subtype
      (LinearMap.id (R := ZMod 2) (M := V)) (fun _ _ => rfl) (C.subgroupOf H) ⊤
    simpa only [Submodule.map_id, map_subgroupOf_eq_of_le hCH] using h.symm
  central := ⟨s.central.toSubmodule, fun g v hv => s.central.apply_mem_toSubmodule g hv⟩
  central_eq := by
    change s.central.toSubmodule = fixedSpace (s.space.toRepresentation.comp H.subtype)
      (C.subgroupOf H)
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le hCH, s.central_eq]

/-- The action comparison retains both the group inclusion and a linear intertwiner. -/
def restrictionActionEquiv (s : MovedSection ρ C) (H : Subgroup D) (hCH : C ≤ H) :
    ActionEquiv ((restrictSection s H hCH).action.comp (C.subgroupOf H).subtype)
      (s.action.comp C.subtype) where
  groupEquiv := subgroupOfEquivOfLe hCH
  linearEquiv := LinearEquiv.refl _ _
  intertwines g w := by
    induction w using Submodule.Quotient.induction_on with | _ v => rfl

/-- Changing the ambient actor preserves an arbitrary marking of repeated natural modules. -/
theorem repeated_restrict_iff (s : MovedSection ρ C) (H : Subgroup D)
    (hCH : C ≤ H) (F : BinaryField) (d r : ℕ) :
    IsRepeatedLinearNatural
      ((restrictSection s H hCH).action.comp (C.subgroupOf H).subtype) F d r ↔
      IsRepeatedLinearNatural (s.action.comp C.subtype) F d r := by
  let a := restrictionActionEquiv s H hCH
  constructor
  · rintro ⟨e⟩
    refine ⟨{ groupEquiv := a.groupEquiv.symm.trans e.groupEquiv
              linearEquiv := e.linearEquiv
              intertwines := ?_ }⟩
    intro g w
    exact e.intertwines (a.groupEquiv.symm g) w
  · rintro ⟨e⟩
    refine ⟨{ groupEquiv := a.groupEquiv.trans e.groupEquiv
              linearEquiv := e.linearEquiv
              intertwines := ?_ }⟩
    intro g w
    exact e.intertwines (a.groupEquiv g) w

/-- Extraction may use any construction of the canonical moved section. -/
theorem repeated_of_restrictedSection (s : MovedSection ρ C) (H : Subgroup D)
    (hCH : C ≤ H) (t : MovedSection (ρ.comp H.subtype) (C.subgroupOf H))
    (F : BinaryField) (d r : ℕ)
    (h : IsRepeatedLinearNatural (t.action.comp (C.subgroupOf H).subtype) F d r) :
    IsRepeatedLinearNatural (s.action.comp C.subtype) F d r := by
  rw [movedSection_unique t (restrictSection s H hCH)] at h
  exact (repeated_restrict_iff s H hCH F d r).mp h

/-- In the quasisimple classifier alternative, the specified component is F*(D). -/
theorem component_eq_fitting [Finite D] (hC : IsComponent D C)
    (hF : IsQuasisimple (generalizedFitting D)) : C = generalizedFitting D :=
  hC.eq_of_le ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hF⟩
    (component_le_generalizedFitting D C hC)

private theorem no_component_of_symmetricThree (hC : IsComponent D C)
    (e : D ≃* Equiv.Perm (Fin 3)) : False := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom.comp C.subtype) (e.injective.comp C.subtype_injective)
  let : IsQuasisimple C := hC.2
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  exact Group.IsPerfect.not_isSolvable C inferInstance

/-- The full adequate alternatives at a specified component, with S₃ excluded
and the quasisimple action attached to that component itself. -/
theorem classifier_at_component [Finite D] (hC : IsComponent D C)
    (h : NontrivialAdequateAlternative ρ) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ C) ∨
      Nonempty (SourceTwoFactorCase ρ) ∨
      Nonempty (ChapterB.OuterSixThreeShape D) ∨ Nonempty (HyperplaneCase ρ) := by
  cases h with
  | quasisimple hF c =>
    left
    rw [component_eq_fitting hC hF]
    exact ⟨c⟩
  | symmetricThree c => exact (no_component_of_symmetricThree hC c.equiv).elim
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | outerSixThree c => exact Or.inr (Or.inr (Or.inl ⟨c⟩))
  | hyperplane c => exact Or.inr (Or.inr (Or.inr ⟨c⟩))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.MarkedAction.ComponentAction
