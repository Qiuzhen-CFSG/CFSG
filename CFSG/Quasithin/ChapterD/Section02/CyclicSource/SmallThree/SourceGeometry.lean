module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.Support
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.EndpointCount

/-!
# The two actual support planes in the original D.2.25 branch

The source's nonempty order-three support family first spans the whole module
by fixed-complement separation. The literal SQTK cover makes each involution
centralizer in O₃ cyclic, bounding the number of independent cubic factors by
three. The cyclic ratio excludes one factor and the invariant-three-plane
argument excludes three. Thus the original canonical normal subgroup is E₉,
and its two actual support planes sum to the original four-dimensional module.

Source: Aschbacher–Smith D.2.25, printed p.190. The final order-eighteen
normalizer and local-generation endpoint consumes these marked planes.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The original source hypotheses produce the actual elementary nine-group,
its two canonical support planes, and their full four-dimensional sum. -/
theorem Hypotheses.smallThree_two_supportFactors (h : Hypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hq : cubicRatio ρ = 2)
    (hne : ∃ X : Subgroup G, X ≤ pCore 3 G ∧ Nat.card X = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2) :
    let := BinaryGroupAction.action ρ
    let Y := smallSupportGroup G (Multiplicative V) 1
    ∃ d : FittingConfigurations.SupportFactors ρ Y 2,
      (∀ i, d.ambient i ∈ smallSupportFactors G (Multiplicative V) 1) ∧
      Nat.card Y = 9 ∧ Module.finrank (ZMod 2) V = 4 := by
  apply SmallThree.canonical_two_supportFactors ρ h.toCoreHypotheses hq
  · exact h.toCoreHypotheses.involution_threeCore_centralizer_cyclic hH f honto hfive
  · exact h.smallThree_moved ρ hfive hq hne

end CFSG.Quasithin.ChapterD.CyclicSource