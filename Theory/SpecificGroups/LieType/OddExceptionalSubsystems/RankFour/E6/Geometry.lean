module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.Chart

/-!
# The graph-stable four-root chart in actual E6

The literal E6 simple-root conventions realize the generic signed chart
at nodes 0,5,2,3. The exported formulas use the same `simpleRoot` maps as
the twisted E6 carrier, so its fixed-point construction can reuse native
faithfulness and the three graph-fixed coroot detectors directly.

Source: GLS3 §2.6; Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.OddRankFour.E6
open Theory.AlgebraicGroup.StandardRootSystem
open TwistedE6.FoldedSubsystem
attribute [local instance] Classical.decEq
local instance : Fintype typeE6Roots := Fintype.ofFinite _
local instance : typeE6RootPairing.IsIrreducible := TwistedE6.TheoremDRootNormalizer.pairing_irreducible

def nodes : SixNodes typeE6RootPairing_base where
  node := typeE6RootPairing_baseEquiv
  injective := typeE6RootPairing_baseEquiv.injective
  cartan := typeE6RootPairing_base_cartan_apply

variable (F : Type*) [Field F]

abbrev chart : (Fin 4 → Multiplicative F) →* TwistedE6.splitCarrier F := nodes.chart F
abbrev coroot (i : Fin 6) : TwistedE6.splitCarrier F := nodes.coroot F i

theorem chart_formula (a : Fin 4 → Multiplicative F) :
    chart F a = simpleRoot F true 0 (a 0).toAdd * simpleRoot F true 5 (a 1).toAdd *
      simpleRoot F true 2 (a 2).toAdd * simpleRoot F false 3 (a 3).toAdd := by
  exact nodes.chart_formula F a

theorem chart_injective (h2 : (2 : F) ≠ 0) : Function.Injective (chart F) :=
  nodes.chart_injective F h2

theorem coroot_three_chart (a : Fin 4 → Multiplicative F) :
    coroot F 3 * chart F a * (coroot F 3)⁻¹ = chart F ![a 0,a 1,(a 2)⁻¹,a 3] :=
  nodes.coroot_three_chart F a

theorem coroot_two_chart (a : Fin 4 → Multiplicative F) :
    coroot F 2 * chart F a * (coroot F 2)⁻¹ = chart F ![a 0,a 1,a 2,(a 3)⁻¹] :=
  nodes.coroot_two_chart F a

theorem coroot_pair_chart (a : Fin 4 → Multiplicative F) :
    (coroot F 1 * coroot F 4) * chart F a * (coroot F 1 * coroot F 4)⁻¹ =
      chart F ![(a 0)⁻¹,(a 1)⁻¹,a 2,a 3] := nodes.coroot_pair_chart F a

end ExceptionalSplit.OddRankFour.E6
