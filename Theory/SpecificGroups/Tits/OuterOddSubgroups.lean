module

public import Theory.SpecificGroups.Tits.OuterOddSubgroups.Displacement
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.SylowAutomorphisms
public import Theory.GroupTheory.CyclicNormalOddQuotient

/-!
# Odd outer subgroups of the Tits group

Sylow conjugacy makes the stabilizer of the certified Sylow two-subgroup
surject onto Out(T). The two certified parabolic overlap-centralizer bounds
embed the kernel of restriction to Aut(S) into S × S. The Frattini-quotient
calculation proves that Aut(S) is a two-group, so the stabilizer and Out(T)
are two-groups as well. The certified Parrott–Atlas isomorphism transports
this conclusion to the actual presentation carrier.

Thus the outer group has no nontrivial odd-prime subgroups, and the trivial
normal subgroup witnesses `HasCyclicNormalOddQuotient`. The conditional
reductions remain available, and the final theorems discharge all their
local premises without additional hypotheses on the presentation carrier.

Source: Aschbacher–Smith, combined manuscript, printed p.510 and Remark
A.2.4 on p.33; compare GLS3, Theorem 2.5.15. This route avoids constructing
the full Ree group as an automorphism group.
-/

@[expose] public section
namespace Tits.OuterOddSubgroups
open Subgroup ExceptionalParabolics Theory.GroupTheory

/-- A two-group restriction image and kernel make the full Sylow stabilizer a two-group. -/
theorem sylowStabilizer_isPGroup_of_restriction
    (hS : IsPGroup 2 (MulAut atlas1600SylowTwoSubgroup))
    (hK : IsPGroup 2 sylowRestriction.ker) : IsPGroup 2 sylowStabilizer := by
  intro a
  obtain ⟨n, hn⟩ := hS (sylowRestriction a)
  have hm : a ^ (2 ^ n) ∈ sylowRestriction.ker := by
    change sylowRestriction (a ^ (2 ^ n)) = 1
    rwa [map_pow]
  obtain ⟨m, hm⟩ := hK ⟨a ^ (2 ^ n), hm⟩
  refine ⟨n + m, ?_⟩
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val hm

/-- The restriction bounds control every outer class of the certified Atlas model. -/
theorem atlas_outer_isPGroup_of_restriction
    (hS : IsPGroup 2 (MulAut atlas1600SylowTwoSubgroup))
    (hK : IsPGroup 2 sylowRestriction.ker) : IsPGroup 2 (MulAut.Outer Atlas1600Group) :=
  (sylowStabilizer_isPGroup_of_restriction hS hK).of_surjective toOuter toOuter_surjective

/-- The local bounds imply the outer two-group assertion for the actual presentation. -/
theorem parrott_outer_isPGroup_of_local
    (hS : IsPGroup 2 (MulAut atlas1600SylowTwoSubgroup))
    (hfirst : first ⊓ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r1) : Set Atlas1600Group) ≤ S)
    (hsecond : second ⊓ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r8) : Set Atlas1600Group) ≤ S) :
    IsPGroup 2 (MulAut.Outer ParrottGroup) :=
  (atlas_outer_isPGroup_of_restriction hS
    (kernel_isPGroup_of_overlap_centralizers hfirst hsecond)).of_equiv
      (MulAut.outerCongr parrottFiniteImageEquiv).symm

/-- The concrete local bounds suffice for the odd-subgroup condition used on p.510. -/
theorem parrott_hasCyclicNormalOddQuotient_of_local
    (hS : IsPGroup 2 (MulAut atlas1600SylowTwoSubgroup))
    (hfirst : first ⊓ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r1) : Set Atlas1600Group) ≤ S)
    (hsecond : second ⊓ centralizer
      (reflectionOverlap (atlas1600ParrottAssignment .r8) : Set Atlas1600Group) ≤ S) :
    HasCyclicNormalOddQuotient (MulAut.Outer ParrottGroup) :=
  hasCyclicNormalOddQuotient_of_isPGroup_two
    (parrott_outer_isPGroup_of_local hS hfirst hsecond)

/-- The outer automorphism group of Parrott's actual Tits presentation is a two-group. -/
theorem parrott_outer_isPGroup : IsPGroup 2 (MulAut.Outer ParrottGroup) :=
  parrott_outer_isPGroup_of_local SylowAutomorphisms.isPGroup_mulAut
    first_overlap_centralizer_le second_overlap_centralizer_le

/-- The Tits presentation satisfies the outer-group condition used on printed p.510. -/
theorem parrott_hasCyclicNormalOddQuotient :
    HasCyclicNormalOddQuotient (MulAut.Outer ParrottGroup) :=
  hasCyclicNormalOddQuotient_of_isPGroup_two parrott_outer_isPGroup

end Tits.OuterOddSubgroups
end
