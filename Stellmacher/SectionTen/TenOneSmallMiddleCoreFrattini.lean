module
public import Stellmacher.SectionTen.TenOneSmallMiddleCoreCenter
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# The Frattini subgroup of the small middle core

When the first neighboring module has order eight and its local quotient
is SL₂(2), the Frattini subgroup of the actual middle two-core is its
intrinsic middle center. No order assumption on the middle core is needed.

The proved elementary quotient of the middle core by its middle center gives
one containment by the finite-p-group Frattini criterion. For the reverse
containment, the generated middle neighborhood lies in the middle core and
has derived subgroup equal to the middle center. Monotonicity puts that
center in the middle-core commutator subgroup, which lies in its Frattini
subgroup. Mapping along the literal core subtype transfers this containment
to the required intrinsic subgroup.

Source: the Frattini consequence used before the order-32 normalizer action
in Stellmacher (10.1)(a3), printed p.61 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- The small middle core has Frattini subgroup equal to its middle center. -/
public theorem ten_one_small_middle_core_frattini
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    frattini (QAt ctx.Γ middle) =
      (ZAt ctx.Γ middle).subgroupOf (QAt ctx.Γ middle) := by
  let Q := QAt ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  let W := GeneratedNeighborhoodV ctx.Γ middle
  have hQp : IsPGroup 2 Q := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt middle)
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := GAt ctx.Γ middle)).map _
  let _ : Fact (IsPGroup 2 Q) := ⟨hQp⟩
  obtain ⟨hN, helementary⟩ :=
    ten_one_small_middle_core_quotient_elementary ctx middle hpath hsmall hmodel
  let _ := hN
  apply le_antisymm
  · exact Subgroup.frattini_le_of_elementary_quotient hQp (Z.subgroupOf Q) helementary
  · have hWQ : W ≤ Q := nine_seven_neighborhood_le_own_core
      ctx.toLocalContext.toSectionNineLocalContext
      (by change 2 < ctx.criticalPath.length; rw [ctx.critical_length]; decide) middle
    have hderived : DerivedAmbient W = Z :=
      (ten_one_small_derived ctx middle hpath hsmall).trans
        (ten_one_small_intersection ctx middle hpath hsmall)
    have hZcomm : Z ≤ ⁅Q, Q⁆ := by
      rw [← hderived, show DerivedAmbient W = ⁅W, W⁆ from
        Subgroup.map_subtype_commutator W]
      exact Subgroup.commutator_mono hWQ hWQ
    have hnative : Z.subgroupOf Q ≤ commutator Q := by
      apply (Subgroup.map_le_map_iff_of_injective Q.subtype_injective).mp
      rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_subtype_commutator]
      exact inf_le_left.trans hZcomm
    exact hnative.trans (commutator_le_frattini_of_isPGroup (p := 2))

end Stellmacher.SectionTen
