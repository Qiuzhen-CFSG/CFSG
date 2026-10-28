module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.LocalAction

/-!
# Compatible automorphisms of the Tits Sylow subgroup

A Sylow automorphism is compatible with the two marked parabolics when
it extends to an automorphism of each, using the actual subgroup inclusions.
Every restriction of a full Sylow-preserving automorphism is compatible,
since both parabolics are intrinsic. Thus a count of compatible restrictions
bounds the image of the full restriction homomorphism.

This interface retains the full local groups and agreement on their common
Sylow subgroup; it assumes no numerical package for their two-cores.
Source: Parrott (1972), §5, p.683, and the automorphism assertion in
Aschbacher–Smith F.1.12, printed pp.263–264.
-/

@[expose] public section
namespace Tits.SharpOuterBound
open Subgroup OuterOddSubgroups ExceptionalParabolics

/-- The two local extensions must agree with the specified Sylow automorphism. -/
def HasCompatibleParabolicExtensions (f : MulAut S) : Prop :=
  ∃ a : MulAut first, ∃ b : MulAut second,
    (∀ s : S, (a ⟨s.val, sylow_le_first s.property⟩ : Atlas1600Group) = (f s : Atlas1600Group)) ∧
    (∀ s : S, (b ⟨s.val, sylow_le_second s.property⟩ : Atlas1600Group) = (f s : Atlas1600Group))

/-- The actual compatible Sylow automorphisms, without chosen local witnesses. -/
abbrev CompatibleSylowRestrictions := {f : MulAut S // HasCompatibleParabolicExtensions f}

/-- Both intrinsic parabolics supply extensions of every global restriction. -/
theorem sylowRestriction_hasCompatibleParabolicExtensions (a : sylowStabilizer) :
    HasCompatibleParabolicExtensions (sylowRestriction a) := by
  refine ⟨(parabolicRestriction a).1, (parabolicRestriction a).2, ?_, ?_⟩ <;> intro s <;> rfl

/-- The image of global restriction embeds into the compatible local restrictions. -/
def restrictionRangeEmbedding : sylowRestriction.range ↪ CompatibleSylowRestrictions where
  toFun f := ⟨f.val, by
    obtain ⟨a, ha⟩ := f.property
    rw [← ha]
    exact sylowRestriction_hasCompatibleParabolicExtensions a⟩
  inj' := by
    intro f g h
    exact Subtype.ext (congrArg (fun a : CompatibleSylowRestrictions => a.val) h)

/-- Local compatibility gives an upper bound for every extendible restriction. -/
theorem sylowRestriction_range_card_le_compatible :
    Nat.card sylowRestriction.range ≤ Nat.card CompatibleSylowRestrictions :=
  Nat.card_le_card_of_injective restrictionRangeEmbedding restrictionRangeEmbedding.injective

end Tits.SharpOuterBound
end
