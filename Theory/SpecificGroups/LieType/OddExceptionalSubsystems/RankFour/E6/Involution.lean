module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.E6.Geometry
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.Involution

/-!
# The native E6 involution and its graph-fixed witness

These are the literal source words used by the split and twisted E6
centralizer constructions. The neighboring product witnesses noncentrality
before either defining central quotient.

Source: GLS3 §2.6; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.OddRankFour.E6
open TwistedE6.FoldedSubsystem
local instance : Theory.AlgebraicGroup.StandardRootSystem.typeE6RootPairing.IsIrreducible :=
  TwistedE6.TheoremDRootNormalizer.pairing_irreducible
variable (F : Type*) [Field F]

abbrev involution : TwistedE6.splitCarrier F := nodes.involution F

theorem involution_eq : involution F = coroot F 0 * coroot F 5 := rfl

theorem involution_square : involution F ^ 2 = 1 := nodes.involution_square F

theorem involution_chart (a : Fin 4 → Multiplicative F) :
    Commute (involution F) (chart F a) := nodes.involution_chart F a

theorem involution_not_commute_folded (h2 : (2 : F) ≠ 0) :
    ¬ Commute (involution F) (simpleRoot F true 1 1 * simpleRoot F true 4 1) :=
  nodes.involution_not_commute_neighbor F h2

end ExceptionalSplit.OddRankFour.E6
