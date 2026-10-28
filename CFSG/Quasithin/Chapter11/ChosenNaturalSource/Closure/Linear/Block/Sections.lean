module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Splitting

/-!
# Literal sections in the SL₃ block argument

The special factor in 11.5.7 is (U∩L)/C_{U∩L}(L). Its denominator
is central in U∩L, so the ordinary group quotient is available without
an ambient-normality assumption. The separate quotient U/Z(U) is the
section carrying the exceptional K action. Neither quotient replaces
the point quotient U/V₁ used in the natural-sum argument.

These definitions fix the interfaces for the remaining structure,
exceptional-action and multiplicity proofs; no special-group or rank
conclusion is built into them.

Source: Aschbacher--Smith, 11.5.7, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)
/-- The part of U lying in the original component, with no Sylow identification. -/
def componentPart : Subgroup G := E.W ⊓ L
/-- C_{U∩L}(L), as a subgroup of U∩L for the literal quotient. -/
def centralPart : Subgroup (componentPart E) :=
  (centralizer (L : Set G)).subgroupOf (componentPart E)
theorem centralPart_le_center : centralPart E ≤ center (componentPart E) := by
  intro c hc
  rw [mem_center_iff]
  intro a
  apply Subtype.ext
  exact hc a a.property.2
instance centralPart_normal : (centralPart E).Normal := by
  constructor
  intro c hc a
  have he := mem_center_iff.mp (centralPart_le_center E hc) a
  rwa [he,mul_inv_cancel_right]
/-- The source special group (U∩L)/C_{U∩L}(L). -/
abbrev SpecialFactor := componentPart E ⧸ centralPart E
/-- Z(U) as an actual subgroup of the original ambient group. -/
def closureCenter : Subgroup G := (center E.W).map E.W.subtype
/-- The original central quotient, on which the exceptional K must act. -/
abbrev CentralQuotient := E.W ⧸ center E.W
@[simp] theorem centralPart_map :
    (centralPart E).map (componentPart E).subtype =
      E.W ⊓ L ⊓ centralizer (L : Set G) := by
  rw [centralPart,subgroupOf_map_subtype,inf_comm]
  rfl
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block
