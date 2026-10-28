module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels.Source
public import Theory.Representation.HexacodeAction.EvenBinaryRecognition
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Transport

/-!
# Hexacode coordinates on the full original covered-six moved module

The original B.5 section has zero central denominator. Recognize its faithful
irreducible quotient as the even hexacode action, then pull the coordinates
back through that literal quotient map. The action equivalence consequently
concerns the full moved space, without assuming a block predicate or discarding
a fixed central factor.

Source: Aschbacher--Smith K.1.3 and 13.6.22, printed pp.453 and 932.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
open ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination
universe u w
variable {D : Type u} [Group D] [Finite D]
  {V : Type w} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C : Subgroup D} [C.Normal]

omit [Finite D] [C.Normal] in
/-- The full moved component action has actual hexacode coordinates.
The group equivalence includes the explicitly constructed actor twist. -/
theorem ActionData.hexacode_coordinates (m : ActionData ρ C)
    (eC : C ≃* Atlas.Codes.HexEvenAutomorphisms) :
    Nonempty (ActionEquiv
      (m.conclusion.sectionData.space.toRepresentation.comp
        (C.subgroupOf (offenderSubgroup ρ)).subtype)
      Hexacode.evenAction) := by
  let B := C.subgroupOf (offenderSubgroup ρ)
  let eB : B ≃* Atlas.Codes.HexEvenAutomorphisms :=
    (subgroupOfEquivOfLe m.component_le_offenders).trans eC
  let s := m.conclusion.sectionData
  let σ := (s.action.comp B.subtype).comp eB.symm.toMonoidHom
  have hf : Function.Injective σ :=
    (m.faithful.comp B.subtype_injective).comp eB.symm.injective
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eB.symm.toMonoidHom eB.symm.surjective
      (s.action.comp B.subtype)).mpr m.irreducible
  obtain ⟨a, f, h⟩ := Hexacode.EvenBinaryRecognition.exists_equivariant σ hf hi m.tripleSix.dimension
  let q := (s.central.toSubmodule.quotEquivOfEqBot m.central_eq_bot).symm
  refine ⟨⟨eB.trans a, q.trans f, ?_⟩⟩
  intro g v
  have hh := h (eB g) (q v)
  simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    eB.symm_apply_apply, LinearEquiv.trans_apply, MulEquiv.trans_apply,
    q, Submodule.quotEquivOfEqBot_symm_apply, MovedSection.action,
    ← Submodule.mkQ_apply, Subrepresentation.quotientRepresentation_mk] using hh

/-- Extend the section from the offender actor to its original ambient actor.
The underlying moved vectors and central denominator are unchanged. -/
@[expose] noncomputable def ActionData.ambientSection (m : ActionData ρ C) : MovedSection ρ C :=
  SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.liftSection
    m.component_le_offenders m.conclusion.sectionData

omit [Finite D] in
/-- The coordinates retain the original component inclusion after extending
the actor. This is the chart consumed by the full hexacode normalizer. -/
theorem ActionData.ambient_hexacode_coordinates (m : ActionData ρ C)
    (eC : C ≃* Atlas.Codes.HexEvenAutomorphisms) :
    Nonempty (ActionEquiv (m.ambientSection.space.toRepresentation.comp C.subtype)
      Hexacode.evenAction) := by
  obtain ⟨a⟩ := m.hexacode_coordinates eC
  refine ⟨⟨(subgroupOfEquivOfLe m.component_le_offenders).symm.trans a.groupEquiv,
    a.linearEquiv, ?_⟩⟩
  intro g v
  exact a.intertwines ((subgroupOfEquivOfLe m.component_le_offenders).symm g) v

omit [Finite D] [Module.Finite (ZMod 2) V] in
/-- The ambient section retains the proved zero central denominator. -/
theorem ActionData.ambient_central_eq_bot (m : ActionData ρ C) :
    m.ambientSection.central.toSubmodule = ⊥ := m.central_eq_bot

omit [Finite D] [Module.Finite (ZMod 2) V] in
/-- Extending the actor keeps the full moved dimension six. -/
theorem ActionData.ambient_dimension (m : ActionData ρ C) :
    Module.finrank (ZMod 2) m.ambientSection.space.toSubmodule = 6 := m.dimension

omit [Finite D] [Module.Finite (ZMod 2) V] in
/-- Irr+ is preserved for the original component, with the original vectors. -/
theorem ActionData.ambient_irrPlus (m : ActionData ρ C) :
    IsIrrPlus ρ C m.ambientSection.space.toSubmodule :=
  (IsIrrPlus.subgroupOf_iff ρ C (offenderSubgroup ρ)
    m.component_le_offenders _).mp m.irrPlus

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
