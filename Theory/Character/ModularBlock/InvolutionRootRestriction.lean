module

public import Theory.Character.ModularBlock.InvolutionRootTrace
public import Theory.Character.ModularBlock.RestrictionProjectorTrace

/-!
# Principal-block restriction on roots of an involution

Let `x` be an involution and `C` its centralizer. On elements of `C` whose
cyclic subgroup contains `x`, the compatible local principal projection of
an ambient irreducible character equals that character if its ambient block
is principal, and vanishes otherwise. The modular place is arbitrary.

The integral regular-bimodule comparison in `InvolutionRootTrace`, followed
by extension to complex coefficients, identifies the local-left and
ambient-right mixed traces. Ordinary character orthogonality, as packaged in
`RestrictionProjectorTrace`, extracts each restricted character's projection.

Source: Alperin--Brauer--Gorenstein, Chapter III, Sections 5--6, associated-block
support and generalized decomposition expansion, especially III.6 preceding
equation (4).
-/

public section
noncomputable section

namespace ModularBlock.InvolutionRootRestriction

open scoped BigOperators
open PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

/-- The compatible local principal projection of a restricted ambient row on
cyclic roots of an involution, for any prescribed modular place. -/
theorem restriction_projection_on_involution_roots
    (d : PrincipalCongruenceBlockData G) (x : G) (hx : orderOf x = 2)
    (i : d.I) (a : Subgroup.centralizer (Set.singleton x))
    (hxa : x ∈ Subgroup.zpowers (a : G)) :
    let C := Subgroup.centralizer (Set.singleton x)
    let b := CompatibleBrauerBlock.localData d C
    (∑ j ∈ b.block,
      scalarProduct C (fun c => d.chi i (ConjClasses.mk (c : G)))
        (fun c => b.chi j (ConjClasses.mk c)) * b.chi j (ConjClasses.mk a)) =
      if i ∈ d.block then d.chi i (ConjClasses.mk (a : G)) else 0 := by
  exact RestrictionProjectorTrace.restriction_projection_of_mixed_trace d
    (Subgroup.centralizer (Set.singleton x))
    (CompatibleBrauerBlock.localData d (Subgroup.centralizer (Set.singleton x))) a
    (fun g => InvolutionRootTrace.complex_root_trace d x hx a hxa g) i

end ModularBlock.InvolutionRootRestriction
