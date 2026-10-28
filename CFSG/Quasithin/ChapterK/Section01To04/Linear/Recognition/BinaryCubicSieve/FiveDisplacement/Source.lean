module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve

/-!
# The SL₅ displacement branches on the original Chapter K action

The actual equivalence from the source component to SL₅ marks the action used
by both branch estimates. The faithful irreducible source action supplies the
transport hypotheses, and the core discharges the full-normalizer displacement
premise of both degree consumers.

The unconditional applications use `multiple_support_displacement`, deriving
finite dimension, faithfulness and irreducibility from `SourceHypothesis`.
The cubic-ratio bound remains on the original ambient group. The conditional
APIs remain available, while no extra displacement premise is needed by
`source_finrank_le_fourteen` or `source_degrees`.
Source: Aschbacher–Smith K.3.2, printed pp.454–455 (PDF pp.465–466).
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement

open Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The two remaining estimates suffice for the literal source degree window. -/
theorem source_finrank_le_fourteen_of_inner_and_graph {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* SL5TenDimensional.Group)
    (hinner : InnerEstimate (modelAction ρ e))
    (hgraph : GraphEstimate (modelAction ρ e)) : Module.finrank (ZMod 2) V ≤ 14 :=
  five_finrank_le_fourteen_of_displacement h e
    (multiple_support_displacement_of_inner_and_graph (modelAction ρ e)
      (modelAction_injective ρ h.faithful e)
      (modelAction_irreducible ρ h.irreducible e) hinner hgraph)

/-- The actual marked source action has degree five or ten once both
independent common-fixed-space estimates are proved. -/
theorem source_degrees_of_inner_and_graph {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* SL5TenDimensional.Group)
    (hinner : InnerEstimate (modelAction ρ e))
    (hgraph : GraphEstimate (modelAction ρ e)) :
    Module.finrank (ZMod 2) V = 5 ∨ Module.finrank (ZMod 2) V = 10 :=
  five_degrees_of_displacement h e
    (multiple_support_displacement_of_inner_and_graph (modelAction ρ e)
      (modelAction_injective ρ h.faithful e)
      (modelAction_irreducible ρ h.irreducible e) hinner hgraph)

/-- The proved displacement estimate on the actual marked source component.
All representation hypotheses come from the original Chapter K input. -/
theorem source_displacement {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* SL5TenDimensional.Group) :
    FiveMultipleSupportDisplacement (modelAction ρ e) := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  exact multiple_support_displacement (modelAction ρ e)
    (modelAction_injective ρ h.faithful e)
    (modelAction_irreducible ρ h.irreducible e)

/-- The binary SL₅ degree window from the ambient source cubic-ratio bound,
with the full-normalizer displacement premise discharged. -/
theorem source_finrank_le_fourteen {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* SL5TenDimensional.Group) :
    Module.finrank (ZMod 2) V ≤ 14 :=
  five_finrank_le_fourteen_of_displacement h e (source_displacement h e)

/-- The actual marked source action has degree five or ten, with no extra
inner or graph displacement premise. -/
theorem source_degrees {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* SL5TenDimensional.Group) :
    Module.finrank (ZMod 2) V = 5 ∨ Module.finrank (ZMod 2) V = 10 :=
  five_degrees_of_displacement h e (source_displacement h e)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement
