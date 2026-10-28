module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.ComparisonInputs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.SmallUnitary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.FixedModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.BenderComparison
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters.RankTwoComparison

/-!
# Parameters of the classical triple covers in 13.8.17

The even-field branch of A.3.6 has the required exponent and congruence;
solvability of SU₃(2) removes its one excluded endpoint. For an odd prime,
the actual central quotient is the corresponding projective matrix group.
The center-three condition excludes the prime three. Defining-prime cubes
exclude the fixed PSL₄(2), PSL₅(2), and A₇ alternatives of F.9.18.

The Bender and rank-two comparisons exclude all remaining odd-prime
possibilities using the actual Sylow two-ranks and orders, including the
binary commutator carriers. The final theorem discharges both comparison
inputs and proves `ClassicalCoverParameters` for every finite quasisimple
group. This is the intrinsic parameter comparison used by `lift_classified`;
the source classification hypotheses remain with its caller.

Source: Aschbacher–Smith, A.3.6(2), printed p.43; F.9.18(4), pp.325–326;
and 13.8.17, p.953 (PDF p.970), combined manuscript of 1 March 2004.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
open Subgroup Theory.GroupTheory
open Chapter1.Section02.LocalModels Models
universe u

/-- Assembly from the two infinite-family comparisons.
All field conventions, central-quotient transports, fixed-model exclusions,
and the small unitary endpoint are discharged here; the unconditional theorem
below supplies both comparison inputs. -/
theorem classicalCoverParameters_of_odd_comparisons
    {G : Type u} [Group G] [IsQuasisimple G]
    (hB : OddBenderComparison (G ⧸ center G))
    (hR : OddRankTwoComparison (G ⧸ center G)) : ClassicalCoverParameters G := by
  intro unitary q hq hz hmodel hquot
  rcases hq with heven | ⟨hp, ho⟩
  · exact even_parameters heven hmodel
  · have hlarge := odd_parameter_ge_five hp ho hz hmodel
    have hprojective := quotient_isPSLSign hp ho hmodel
    exfalso
    cases hquot with
    | bender h => exact hB unitary q hp ho hlarge hprojective h
    | linear_three n hn h => exact (hR unitary q hp ho hlarge hprojective n hn).1 h
    | symplectic n hn h => exact (hR unitary q hp ho hlarge hprojective n hn).2.1 h
    | g2 n hn h => exact (hR unitary q hp ho hlarge hprojective n hn).2.2 h
    | linear_four h => exact odd_projective_not_binary hp ho hprojective (Or.inl rfl) h
    | linear_five h => exact odd_projective_not_binary hp ho hprojective (Or.inr rfl) h
    | alternating_seven h => exact odd_projective_not_alternating_seven hp ho hprojective h

/-- The classical triple covers compatible with the full F.9.18 quotient list
have exactly the even-field parameters required in 13.8.17, with no additional
model-comparison premises. -/
theorem classicalCoverParameters (G : Type u) [Group G] [Finite G] [IsQuasisimple G] :
    ClassicalCoverParameters G :=
  classicalCoverParameters_of_odd_comparisons
    (oddBenderComparison (G ⧸ center G)) (oddRankTwoComparison (G ⧸ center G))

end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
