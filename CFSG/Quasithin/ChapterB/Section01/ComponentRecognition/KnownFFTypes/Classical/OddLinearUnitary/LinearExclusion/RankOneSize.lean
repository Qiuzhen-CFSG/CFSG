module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.ProjectiveDegree
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.InnerGeneration
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration

/-!
# The source rank-one field bound

For the source action with central quotient PSL₂(p^e), where p is odd prime
and e is one or two, cubic ratio at most two forces p^e ≤ 25.

The actual-cover comparison and Borel weight calculation give the binary
degree minimum. Three inner conjugates and four outer conjugates, together
with the disjoint actor's rank bound, discharge `SourceGenerationBounds`.
The reduction on the original binary space bounds its degree by twelve or
eighteen. Thus p^e ≤ 25 in prime degree; in quadratic degree p² ≤ 37, so
oddness again gives p² ≤ 25. The diagonal and field calculations retain the
actual conjugators and coefficient-field action.

This supplies `hsize` in `linear_parameters_of_source_calculations`. The small
parameter exclusions and final K.2 assembly remain with LinearExclusion.

Sources: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
Classification of 2F-modules I, (2.5)--(2.6) and Proposition 4.1, pp.4,8--9.
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
open Subgroup Theory.GroupTheory Representation.BinaryOffender

universe u v

/-- The concrete inner, diagonal and field calculations discharge every
generation and outer-rank premise of the source size reduction. -/
theorem sourceGenerationBounds : SourceGenerationBounds.{u, v} := by
  intro G V _ _ _ _ _ ρ h p e hp ho he hlarge hm
  exact ⟨source_inner_three_conjugates ρ h hp ho he hlarge hm,
    source_outer_four_conjugates ρ h hp ho he hlarge hm,
    source_disjoint_actor_rank ρ h hp ho he hlarge hm⟩

/-- The rank-one field-order bound used by K.2, on the actual central quotient
and original binary action, with no extra degree or generation premise. -/
theorem source_field_order_le_twentyFive
    {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hlo : 4 ≤ p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (hq : cubicRatio ρ ≤ 2) : p ^ e ≤ 25 :=
  source_field_order_le_twentyFive_of_generation ρ h sourceGenerationBounds
    hp ho he hlo hm hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
