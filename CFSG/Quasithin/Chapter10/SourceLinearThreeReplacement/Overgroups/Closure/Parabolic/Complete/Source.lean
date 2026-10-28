module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Wreath.Source

/-!+# The maximal-parabolic realization of the original centralizer seed

The original paired natural action identifies C_{L₀T}(z) as a maximal
subgroup with two-core quotient S₃ wr C₂. Its embedded two-residual is
X = O²(C_{L₀}(z)); the intrinsic wreath calculation gives X ∈ Ξ(G,T)
and its elementary cubic quotient. Combining these proved calculations
discharges both inputs to the published parabolic-seed contract.

The final application constructs every LocalInput hypothesis for the
literal X in any overgroup of XT. This module is a leaf above the two
independent producers, preserving the earlier conditional assembly.

Source: Aschbacher--Smith 10.2.4, 10.2.11 and §10.3,
printed pp.747,753--754,756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The exact source contract, with both natural-action recognition and
the intrinsic wreath-residual calculation discharged. -/
theorem parabolicSeed (T : Sylow 2 G) : ParabolicSeedAt T :=
  parabolicSeed_of_recognition (Natural.diagonalRecognition T) (wreathResidualAt T)

/-- The actual centralizer seed supplies the local embedding input for
every containing overgroup, without an extra recognition premise. -/
theorem localInput
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    {H : Subgroup G}
    (hH : centralizerSeed T L (d.first * d.second) ⊔ (T : Subgroup G) ≤ H) :
    ∃ P : Subgroup G,
      LocalInput 3 (T : Subgroup G) (centralizerSeed T L (d.first * d.second)) P H := by
  obtain ⟨r⟩ := parabolicSeed T hmany L D s d
  exact r.localInput hH

/-- The required wreath equivalence is on the literal seed-Sylow join. -/
theorem seed_wreath
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s) :
    Nonempty (((centralizerSeed T L (d.first * d.second) ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (centralizerSeed T L (d.first * d.second) ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      ParabolicWreath) := by
  obtain ⟨r⟩ := parabolicSeed T hmany L D s d
  exact r.seed_wreath

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
