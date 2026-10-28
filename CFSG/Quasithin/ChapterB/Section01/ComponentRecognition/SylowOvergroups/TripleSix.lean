module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Reduction
public import Theory.Representation.HexacodeAction.Cover
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups.CentralCover

/-!
# Proper Sylow overgroups of the genuine triple cover of A₆

The coordinate map on the even hexacode automorphisms is a central
surjection onto A₆. The proper-overgroup geometry in that quotient and
solvable central lifting give F*(X) ≤ O₂(X)(X ∩ Z(L)) for each proper
Sylow-two overgroup X in the actual cover. The argument applies to X
whether or not it contains the central subgroup of order three.

The final theorem applies this bound to the literal local intersection
in B.1.13. Relative subnormality of K and [L,K] = L exclude the remaining
central factor and give K = L.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.13,
printed p.74 (PDF p.85); the triple-cover convention is A.3.5, printed p.43.
The concrete carrier and its central quotient are the checked ATLAS
hexacode construction imported by `HexacodeAction.Cover`.
-/

public section
open Subgroup Theory.GroupTheory Atlas.Codes
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
variable {G L : Type*} [Group G] [Group L]

/-- Every proper Sylow-two overgroup in an actual triple-six model satisfies
the Fitting bound with the original component's centre retained. -/
theorem tripleSix_proper_sylow_fitting_bound [Finite L] [IsQuasisimple L]
    (e : L ≃* HexEvenAutomorphisms) : ProperSylowFittingBound L := by
  let f := hexEvenCoordinate.comp e.toMonoidHom
  have hf : Function.Surjective f := hexEvenCoordinate_surjective.comp e.surjective
  have hk : f.ker ≤ center L := by
    intro x hx
    have he : e x ∈ center HexEvenAutomorphisms := by
      rw [← Representation.Hexacode.even_kernel_eq_center]
      exact hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp he (e y)
  intro S X hSX hX
  exact AlternatingSix.ProperSylowOvergroups.centralCover_fitting_bound f hf hk S X hSX hX

/-- The triple-cover branch of B.1.13 after the source containment step. -/
theorem tripleSix_eq_component [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) (hL : IsComponent G L)
    (hLK : ⁅L, K⁆ = L) (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hKL : K ≤ L) (e : L ≃* HexEvenAutomorphisms) : K = L := by
  let := hL.2
  exact eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (tripleSix_proper_sylow_fitting_bound e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
