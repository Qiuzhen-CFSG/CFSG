module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds

/-!
# Independent remaining calculations for PSL₂(25)

The actor geometry uses only actual elements of G: a cyclic actor has four
conjugate generators, and a larger actor meets the component in an involution.
At rank three, an inner reflection and its conjugate inside the involution
centralizer have product of order three. The conjugator and reflection are
required to lie in the component. Thus the order-48 centralizer in PGL₂(25)
is never presumed to act on the original module.

The second calculation is the uniform displacement bound eight for inner
order-three elements. A proposed proof uses a nontrivial free orbit of twelve
weights for the actual Borel 5²:12. This bound would remove the need to classify
degree-twelve modules in the exclusion argument. The predicates below specify
outstanding mathematical inputs; neither is asserted here.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v

/-- The needed group calculation, with conjugators in the literal ambient group
and the rank-three centralizer calculation entirely inside the component. -/
def ActorGeometry (G : Type u) [Group G] : Prop :=
  ∀ A : Subgroup G, IsElementaryTwo A →
    (rank A = 1 ∧ ∃ t : G, t ∈ A ∧ orderOf t = 2 ∧
      ∃ g : Fin 4 → G, generalizedFitting G ≤
        closure (Set.range fun i => g i * t * (g i)⁻¹)) ∨
    (∃ t : G, t ∈ A ∧ t ∈ generalizedFitting G ∧ orderOf t = 2 ∧
      (rank A = 3 → ∃ g a : G,
        g ∈ generalizedFitting G ∧ a ∈ A ∧ a ∈ generalizedFitting G ∧
        Commute g t ∧ orderOf (a * (g * a * g⁻¹)) = 3))

/-- A uniform representation bound; no upper degree or ratio assumption is made. -/
def ThreeDisplacementBound {G : Type u} {V : Type v} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) : Prop :=
  ∀ x : G, x ∈ generalizedFitting G → orderOf x = 3 →
    8 ≤ fixedCodim ρ (zpowers x)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
