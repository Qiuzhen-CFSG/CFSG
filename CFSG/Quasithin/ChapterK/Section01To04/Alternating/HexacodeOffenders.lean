module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.ModelContract
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.Transport
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.PlaneKernels
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.ModelExtension
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.EvenGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.OuterExclusion

/-!
# Assembly of the recognized hexacode branch of K.1.3

The actual module intertwiner transports the pointwise plane kernels, best
offenders, their generated subgroup and the quadratic ratio. The marked
full intertwiner is used in the outer case so that the transported even
cover is precisely the source component L. The coordinate, scalar and
central-quotient assertions are constructed from the concrete model.

The concrete even-cover calculation and exclusion of outer best offenders
discharge every model premise. `source` gives generation, the actual
field-plane action and ratio one; `conclusion` supplies corrected B.4.2(8)
while retaining the original recognition. Recognition remains the separate
parent's input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.1.3,
printed p.453 (PDF p.464), implying corrected B.4.2(8), printed p.86.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
open ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ProjectiveLine

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Plane fixing is transported along the actual module coordinates. -/
theorem planes_of_model {H : Type*} [Group H]
    {σ : Representation (ZMod 2) H hexacode} {M : Subgroup H}
    (e : ActionEquiv ρ σ) (h : ModelCalculation σ M) :
    ∀ A, IsBestOffender ρ A → ∃ P :
      Submodule BinaryField.four.Carrier (Fin 3 → BinaryField.four.Carrier),
      Module.finrank BinaryField.four.Carrier P = 2 ∧
      A = subspaceKernel ρ ((P.restrictScalars (ZMod 2)).comap
        (e.linearEquiv.trans modelCoordinates).toLinearMap) ⊤ := by
  intro A hA
  obtain ⟨P, hd, hP⟩ := h.offenders _ (bestOffender_map e hA)
  refine ⟨P, hd, ?_⟩
  apply Subgroup.map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
  rw [hP]
  exact (subspaceKernel_map e
    ((P.restrictScalars (ZMod 2)).comap modelCoordinates.toLinearMap)).symm

/-- The full marking restricts to the same module identification on L. -/
def markedRestriction
    (m : MarkedActionEquiv ρ ⊤ L Hexacode.action hexSign.ker) :
    ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction where
  groupEquiv := m.subgroupEquiv
  linearEquiv := m.action.linearEquiv
  intertwines g v := by
    have h := m.action.intertwines ⟨g.val, Subgroup.mem_top _⟩ v
    rw [m.compatible g] at h
    exact h

/-- The ambient group equivalence preserves the literal even component. -/
theorem marked_even_map
    (m : MarkedActionEquiv ρ ⊤ L Hexacode.action hexSign.ker) :
    L.map (wholeAction rfl m.action).groupEquiv.toMonoidHom = hexSign.ker := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    change m.action.groupEquiv ⟨g, Subgroup.mem_top _⟩ ∈ hexSign.ker
    rw [m.compatible ⟨g, hg⟩]
    exact (m.subgroupEquiv ⟨g, hg⟩).property
  · intro hx
    obtain ⟨g, hg⟩ := m.subgroupEquiv.surjective ⟨x, hx⟩
    refine ⟨g, g.property, ?_⟩
    change m.action.groupEquiv ⟨g.val, Subgroup.mem_top _⟩ = x
    rw [m.compatible g]
    exact congrArg Subtype.val hg

/-- Transport both concrete model calculations, including the literal plane
kernels and the marked even component in the full extension. -/
theorem source_of_model_calculations (a : HexacodeAction ρ L)
    (heven : ModelCalculation Hexacode.evenAction ⊤)
    (hfull : ModelCalculation Hexacode.action hexSign.ker) :
    offenderSubgroup ρ = L ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ L) ∧
      quadraticRatio ρ = 1 := by
  rcases a.extension with hL | hm
  · subst L
    let e := wholeAction rfl a.restricted
    have hg : offenderSubgroup ρ = ⊤ := by
      apply Subgroup.map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
      rw [offenderSubgroup_map e, heven.generated,
        Subgroup.map_top_of_surjective _ e.groupEquiv.surjective]
    refine ⟨hg, ⟨?_⟩, (quadraticRatio_eq e).trans heven.ratio⟩
    exact
      { centerEquiv := centerEquiv a.restricted
        quotientEquiv := quotientEquiv a.restricted
        dimension := dimension a.restricted
        coordinates := coordinates a.restricted
        scalar_linear := coordinates_scalar_linear a.restricted
        offenders := planes_of_model e heven }
  · obtain ⟨m⟩ := hm
    let e := wholeAction rfl m.action
    let r := markedRestriction m
    have hg : offenderSubgroup ρ = L := by
      apply Subgroup.map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
      rw [offenderSubgroup_map e, hfull.generated]
      exact (marked_even_map m).symm
    refine ⟨hg, ⟨?_⟩, (quadraticRatio_eq e).trans hfull.ratio⟩
    exact
      { centerEquiv := centerEquiv r
        quotientEquiv := quotientEquiv r
        dimension := dimension r
        coordinates := coordinates r
        scalar_linear := coordinates_scalar_linear r
        offenders := planes_of_model e hfull }

/-- Source-correct conditional assembly, retaining the original recognition. -/
theorem conclusion_of_model_calculations (a : HexacodeAction ρ L)
    (heven : ModelCalculation Hexacode.evenAction ⊤)
    (hfull : ModelCalculation Hexacode.action hexSign.ker) : Conclusion ρ L := by
  obtain ⟨hg, ⟨action⟩, hr⟩ := source_of_model_calculations a heven hfull
  exact Conclusion.ff (.tripleSix a) (.tripleSix hg action hr)

/-- Final source adapter with precisely the two independent remaining calculations.
The extension's plane, generation and ratio assertions are discharged here. -/
theorem conclusion_of_even_and_outer (a : HexacodeAction ρ L)
    (heven : ModelCalculation Hexacode.evenAction ⊤)
    (hout : ∀ A, IsBestOffender Hexacode.action A → A ≤ hexSign.ker) :
    Conclusion ρ L :=
  conclusion_of_model_calculations a heven (full_model_of_even heven hout)

/-- K.1.3 for the recognized hexacode action. The concrete Sylow geometry
and outer exclusion discharge all offender premises. The field planes have
vector dimension two, and their kernels fix them pointwise in the whole actor. -/
theorem source (a : HexacodeAction ρ L) :
    offenderSubgroup ρ = L ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ L) ∧
      quadraticRatio ρ = 1 :=
  source_of_model_calculations a EvenGeometry.modelCalculation
    (full_model_of_even EvenGeometry.modelCalculation outer_bestOffender_le_even)

/-- The corrected B.4.2(8) alternative, with no additional model premise. -/
theorem irreducibleActionCase (a : HexacodeAction ρ L) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨hg, ⟨action⟩, hr⟩ := source a
  exact .tripleSix hg action hr

/-- The complete recognized K.1.3 branch for the alternating-module assembly,
retaining the original model identification. -/
theorem conclusion (a : HexacodeAction ρ L) : Conclusion ρ L :=
  Conclusion.ff (.tripleSix a) (irreducibleActionCase a)

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
