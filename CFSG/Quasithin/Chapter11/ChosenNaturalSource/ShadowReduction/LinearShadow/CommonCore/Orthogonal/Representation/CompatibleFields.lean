module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Representation.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.Source

/-!
# Application to the original common-plane field comparison

The constructed determinant action supplies the independent orthogonal
marking required by the existing common-plane consumer. Its intertwining
identity is the literal original conjugation, and its field is the independently
given K-field. Applying the consumer proves compatibility with the original
SL₃ field on P ∩ V = V₂ without assuming field compatibility.

Component recognition is discharged in Orthogonal.Complete. The common-core
owner constructs the earlier OrthogonalInput. Source: Aschbacher--Smith,
printed pp.774--775, the orthogonal paragraph and 11.3.8.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] {Y P K L₂ : Subgroup G} {F : BinaryField}

/-- The original matrix marking supplies the independent marking required
by the compatible-field construction, on exactly the same P and Y. -/
def OrthogonalMarking.toSectionMarking [IsMulCommutative P]
    (a : OrthogonalMarking Y P K L₂ F) :
    CompatibleCartan.MarkedSections.OrthogonalMarking F P Y where
  core_le := a.core_le
  actors := a.projection
  surjective := a.surjective
  kernel := a.kernel
  coordinates := a.coordinates.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  intertwines := by
    intro y v
    change (a.coordinates.symm (Multiplicative.ofAdd
      (ClassicalOrthogonal.FourPlusMatrix.matrixAction (a.projection y) v)) : G) = _
    let p := a.coordinates.symm (Multiplicative.ofAdd v)
    have hp : (a.coordinates p).toAdd = v :=
      congrArg Multiplicative.toAdd (a.coordinates.apply_symm_apply _)
    have hh := a.intertwines y p
    rw [hp] at hh
    have he : a.coordinates.symm (Multiplicative.ofAdd
        (ClassicalOrthogonal.FourPlusMatrix.matrixAction (a.projection y) v)) =
        P.normalizerMonoidHom (inclusion a.normalizes y) p := by
      apply a.coordinates.injective
      rw [a.coordinates.apply_symm_apply]
      exact Multiplicative.toAdd.injective hh.symm
    exact congrArg Subtype.val he

variable [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)

/-- The section consumer receives the constructed marking, with the
independent K-field and actual conjugation on the literal source groups. -/
theorem source_section_marking_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    let := pairCore_elementary d.source d.conjugator_mem d.conjugates_disjoint
    Nonempty (CompatibleCartan.MarkedSections.OrthogonalMarking d.pair_field
      (pairCore V H h) (orthogonalJoin (f.Li 1) V h)) := by
  let := pairCore_elementary d.source d.conjugator_mem d.conjugates_disjoint
  obtain ⟨a⟩ := source_orthogonal_marking_of_components d hK hL
  exact ⟨a.toSectionMarking⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)

/-- Application to the existing common-plane consumer: its independent
orthogonal marking is constructed from the original component assertions. -/
theorem source_compatible_fields_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    let := D.elementary
    let := pairCore_elementary d.source d.conjugator_mem d.conjugates_disjoint
    let := CompatibleCartan.originalModule D (.sl3 m) d.seed_fixed
    ∃ mP : Module S.field.Carrier (Additive (pairCore V H h)),
      let := mP
      (∀ (a : S.field.Carrier) (b : f.Vi 1),
        ((a • Additive.ofMul
          (⟨b,(show (b : G) ∈ pairCore V H h ⊓ V from d.intersection_eq_plane.symm ▸ b.property).1⟩ :
            pairCore V H h)).toMul : G) =
        ((a • Additive.ofMul
          (⟨b,(show (b : G) ∈ pairCore V H h ⊓ V from d.intersection_eq_plane.symm ▸ b.property).2⟩ :
            V)).toMul : G)) ∧
      ∃ ρ : Representation S.field.Carrier (orthogonalJoin (f.Li 1) V h)
          (Additive (pairCore V H h)),
        ∀ (y : orthogonalJoin (f.Li 1) V h) (p : Additive (pairCore V H h)),
          ((ρ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G) := by
  let := D.elementary
  let := pairCore_elementary d.source d.conjugator_mem d.conjugates_disjoint
  obtain ⟨a⟩ := source_orthogonal_marking_of_components d hK hL
  exact CompatibleCartan.MarkedSections.exists_compatible_fields D S m f
    (pairCore V H h) (pairGroup V h) d.seed_fixed d.pair_field a.toSectionMarking
    (by rw [d.pair_field.card_eq,d.pair_degree]) d.local_core.symm d.seed_core
    d.intersection_eq_plane le_sup_left
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
