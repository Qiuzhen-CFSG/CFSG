module

public import Theory.Mathieu.M23.Properties.OuterRestriction.HeptadOuter
public import Theory.Mathieu.M23.Properties.OuterRestriction.Pointwise
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.HeptadAutomorphisms
public import Theory.GroupTheory.ConjugacyInvariantOuterAutomorphisms
public import Theory.GroupTheory.CyclicNormalOddQuotient

/-!
# The outer-automorphism restriction for the actual M23

The carrier is the full permutation automorphism group of the concrete
S(4,7,23) Witt design, as defined in Basic. Involution fusion and the intrinsic
centralizer two-core characterize the conjugacy class of the heptad stabilizer,
so every abstract automorphism can be normalized to preserve that stabilizer.
Its outer group is a two-group; an automorphism fixing it pointwise is the
identity by the finite centralizer calculation and its ordinary maximality.
Restriction therefore makes Out(M23) a two-group.

GLS3, Table 5.3d, asserts the stronger Out(M23) = 1. The two-group consequence
proved here supplies exactly the odd-subgroup restriction needed in
Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.510,
for the Mathieu case in the SQTK list on printed p.33. All normalization,
local-automorphism and pointwise-kernel obligations are discharged for the
actual carrier; there is no extra automorphism premise.
-/

open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu
open M23Geometry

/-- Every automorphism can be adjusted by an inner automorphism to preserve
the concrete heptad stabilizer. -/
public theorem m23_aut_normalizes_heptad_up_to_inner (a : MulAut M23) :
    ∃ g : M23, (MulAut.conj g * a) • heptadStabilizer = heptadStabilizer := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj
    (a involutionRepresentative) involutionRepresentative
    ((a.orderOf_eq _).trans involutionRepresentative_order) involutionRepresentative_order)
  have hfix : (MulAut.conj g * a) involutionRepresentative = involutionRepresentative := hg
  refine ⟨g, ?_⟩
  change heptadStabilizer.map (MulAut.conj g * a).toMonoidHom = heptadStabilizer
  have h := fixedHeptad_stabilizer_map_of_aut_fix involutionRepresentative_order
    (MulAut.conj g * a) hfix
  simpa only [fixedHeptad_involutionRepresentative, involutionHeptad, heptadStabilizer,
    omega] using h

/-- The full outer automorphism group of the concrete M23 is a two-group. -/
public theorem m23_outer_isTwoGroup : IsPGroup 2 (MulAut.Outer M23) := by
  apply MulAut.isPGroup_outer_of_conjugacy_invariant_subgroup heptadStabilizer 2
    m23_aut_normalizes_heptad_up_to_inner OuterRestriction.heptad_outer_isTwoGroup
  intro a ha
  rw [OuterRestriction.aut_eq_one_of_heptad_fixed a ha]
  exact (MulAut.innerSubgroup M23).one_mem

/-- The actual M23 outer group satisfies the cyclic-normal odd-quotient
condition used by the quasithin component reduction. -/
public theorem m23_outer_hasCyclicNormalOddQuotient :
    Theory.GroupTheory.HasCyclicNormalOddQuotient (MulAut.Outer M23) :=
  Theory.GroupTheory.hasCyclicNormalOddQuotient_of_isPGroup_two m23_outer_isTwoGroup

end Sporadic.Mathieu
