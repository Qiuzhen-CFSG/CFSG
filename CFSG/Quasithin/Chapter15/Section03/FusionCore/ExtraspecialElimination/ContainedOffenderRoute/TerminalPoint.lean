module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReductionAssembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointTransport

/-!
# Shared point interface for the final model branches

The point lies on the literal component commutator subrepresentation of
U_H/Z. Its difference from the image of an actual element of Z_S is fixed
by H*. This is enough to compare the two point stabilizers; no direct-sum
or global projection is required. The asserted stabilizer is the actual
Y₀*T*, and its properness forces the point to be nonzero.

`TerminalPoint` is an output interface still to be constructed from B.2.14
and the local source hypotheses. Its introduction is not a proof that the
point or stabilizer marking exists. Independent final model calculations
may take it explicitly; the final assembly retains its construction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
preceding 15.3.49(k), printed p.1144, and the point exclusions, p.1145.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup Representation Representation.BinaryOffender ModelExclusions
open scoped IsMulCommutative
universe u

variable {G : Type u} [Group G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (r : ReducedModels.Input κ H M Y V Y0 T ZS Z E L upper)

/-- The component point, with its literal seed and parabolic marking.
Its existence is a separate mathematical obligation. -/
structure TerminalPoint where
  space : Subrepresentation r.placed.action.representation
  component_space : space.toSubmodule =
    Coinvariants.ker (r.placed.action.representation.comp (starImage H L).subtype)
  supplement : space.toSubmodule ⊔ r.placed.action.representation.invariants = ⊤
  seed : ZS
  point : space.toSubmodule
  fixed_difference :
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
      ⟨(seed : G), le_conjugateSpanBy ZS H seed.property⟩) - point.val ∈
        fixedSpace r.placed.action.representation ⊤
  stabilizer : starImage H Y0 ⊔ starImage H T = pointStabilizer space.toRepresentation point
  proper : starImage H Y0 ⊔ starImage H T ≠ ⊤

namespace TerminalPoint
variable {r}

/-- The marking refers to the source seed itself, despite a possibly
nontrivial intersection of the moved and fixed spaces. -/
theorem source_stabilizer (p : TerminalPoint r) :
    pointStabilizer p.space.toRepresentation p.point =
      pointStabilizer r.placed.action.representation
        (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
          ⟨(p.seed : G), le_conjugateSpanBy ZS H p.seed.property⟩)) := by
  ext g
  have hf := p.fixed_difference ⟨g, mem_top g⟩
  change r.placed.action.representation g (_ - p.point.val) = _ - p.point.val at hf
  rw [map_sub] at hf
  constructor
  · intro hg
    have he := congrArg Subtype.val hg
    change r.placed.action.representation g p.point.val = p.point.val at he
    change r.placed.action.representation g _ = _
    simpa only [he, sub_left_inj] using hf
  · intro hg
    apply Subtype.ext
    change r.placed.action.representation g p.point.val = p.point.val
    change r.placed.action.representation g _ = _ at hg
    simpa only [hg, sub_right_inj] using hf

/-- Properness of the actual marked parabolic proves nonzero position. -/
theorem point_ne_zero (p : TerminalPoint r) : p.point ≠ 0 := by
  intro hz
  apply p.proper
  rw [p.stabilizer, hz]
  exact top_unique (fun _ _ => map_zero _)

end TerminalPoint
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
