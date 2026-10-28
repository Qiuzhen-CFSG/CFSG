module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.DoubleNatural
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.Transport
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.AxisFour
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.NaturalRoots

/-!
# Higher-rank splitting in B.4.9(2)(i)

In every binary dimension at least six, common-axis roots in the natural
quotient orientation, or common-center roots in the dual orientation, have
zero double displacement on the original extension. The matrix calculations
use ordinary sections of the literal quotient and retain the original actor
marking, including every degree-one field carrier.

These identities construct an ambient quadratic four-group whose three
nonidentity elements fix the same hyperplane on the actual quotient. Thus all
hypotheses of B.4.9(1) hold, without an FF assumption; applying its authorized
universal implication gives an invariant complement to the original natural
submodule. The rank-three root-group and F₄ clauses are vacuous here.
`HigherRank.FFReduction` applies the result to the shared best offender in its
original Sylow, retaining Thompson replacement and the two-factor budget.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(2)(i),
printed pp.92–95. The printed FF proof stops at dimension five; the root
calculations supply the higher-dimensional branch without an upper dimension bound
or a strongly-quasithin hypothesis. Discharge of B.4.9(1) remains with its
independent source owner.
-/

public section
open Representation
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open QuasisimpleSource QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}

/-- Discharge the natural-orientation premise of the ambient four-group
construction on the original actors and literal quotient. -/
theorem HigherRank.natural_axis_root_products (d : DoubleNatural F n ρ)
    (hF : F.degree = 1) (hn : 6 ≤ n) : HigherRank.NaturalAxisRootProducts d hF := by
  intro eQ i j k hij hkj
  exact HigherRank.degree_one_natural_root_product d hF hn eQ hij hkj

namespace DoubleNatural
variable (d : DoubleNatural F n ρ)

/-- Both quotient orientations satisfy the complete B.4.9(1) hypotheses in
every binary dimension at least six. No geometric or root-product premise
remains, and the four-group need not lie inside a chosen offender. -/
theorem binary_higher_splitting_hypotheses (hF : F.degree = 1) (hn : 6 ≤ n) :
    SourceHypotheses d :=
  HigherRank.degree_one_quadraticSplitting_source d hF hn
    (HigherRank.natural_axis_root_products d hF hn)

/-- B.4.9(2)(i) in every binary dimension at least six, in the stronger form
independent of the FF hypothesis. The sole remaining premise is the exact
universal B.4.9(1) implication, supplied by the source assembly. -/
theorem binary_higher_splits (hF : F.degree = 1) (hn : 6 ≤ n)
    (splitting : ∀ d' : DoubleNatural F n ρ, SourceHypotheses d' → d'.Splits) :
    d.Splits :=
  splitting d (d.binary_higher_splitting_hypotheses hF hn)

end DoubleNatural
end CFSG.Quasithin.ChapterB.NaturalExtensions
