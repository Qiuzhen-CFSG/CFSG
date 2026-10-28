module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.RestrictionBounds
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Automorphisms
public import Theory.SpecificGroups.Tits.SharpOuterBound

/-!
# The common Tits endpoint restrictions have order 2048

The full binary Ree realization gives the actual Tits outer automorphism
quotient order two. Sylow conjugacy makes its restriction stabilizer surject
onto that quotient, with at least 2048 inner maps in the kernel. Thus the
stabilizer has at least 4096 elements. Its restriction kernel has at most two
elements, so its restriction image has at least 2048 elements.

Every such global restriction extends to both intrinsic parabolics. The proved
fusion upper bound of 2048 forces equality with their entire intersection.
All restrictions use the literal Sylow inclusions; no abstract automorphism
cardinality is substituted for the restriction image.

Source context: Parrott (1972), §5, p.683; Aschbacher--Smith F.1.11--12,
printed pp.262--263. This is a direct model calculation using the corrected
first Tits core of order 512 and quotient Sz(2).
-/

public section
noncomputable section
namespace Tits.AmalgamRigidity
open ExceptionalParabolics OuterOddSubgroups SharpOuterBound

/-- Global restrictions extend across both specified Sylow inclusions. -/
theorem globalRestriction_le_intersection :
    sylowRestriction.range ≤ firstRestrictions ⊓ secondRestrictions := by
  rintro f ⟨a, rfl⟩
  exact ⟨⟨(parabolicRestriction a).1, fun _ => rfl⟩,
    ⟨(parabolicRestriction a).2, fun _ => rfl⟩⟩

/-- Exactly 2048 Sylow automorphisms arise from the full Tits group. -/
theorem globalRestriction_card : Nat.card sylowRestriction.range = 2048 := by
  have hcount : Nat.card sylowRestriction.ker * Nat.card sylowRestriction.range =
      Nat.card sylowStabilizer := by rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hk := sylowRestriction_kernel_card_le_two
  have hr := sylowRestriction_range_card_le
  have houter : Nat.card (MulAut.Outer Atlas1600Group) = 2 := FullRee.inner_index
  have houtcount := toOuter.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr toOuter_surjective,
    Subgroup.card_top, houter] at houtcount
  have hkout := toOuter_kernel_card_ge
  nlinarith

/-- The fusion bound on the common endpoint restrictions is attained. -/
theorem restriction_intersection_card :
    Nat.card (firstRestrictions ⊓ secondRestrictions : Subgroup (MulAut S)) = 2048 := by
  apply Nat.le_antisymm restriction_intersection_card_le
  rw [← globalRestriction_card]
  exact Nat.card_le_card_of_injective _
    (Subgroup.inclusion_injective globalRestriction_le_intersection)

/-- Every simultaneous local restriction is a global restriction. -/
theorem globalRestriction_eq_intersection :
    sylowRestriction.range = firstRestrictions ⊓ secondRestrictions := by
  apply Subgroup.eq_of_le_of_card_ge globalRestriction_le_intersection
  rw [globalRestriction_card, restriction_intersection_card]

end Tits.AmalgamRigidity
