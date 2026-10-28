module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.Induction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.Placement

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicRank
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicContradiction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.ExclusionBounds
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.Assembly

/-!
# Splitting exclusions, A₁ placement, and the cyclic contradiction

The two nonsplitting exclusions follow from the precise two-factor B.4.9(1)
input by finite-length induction and actual equivariant sections, with duality
for the chosen socle submodule. The placement tools use the concrete point
parabolic and competing marked two-space.

`source_placement_and_rank` proves A₁ ≰ I and m(Uγ*) > 1 from the actual
critical pair, central section and explicit earlier chapter conclusions.
In rank one it proves W = I and the commutator two-space, constructs the
source Sylow flag, central actor and marked V₂ vector, and derives the
order-four actor bound in either natural orientation. The source lifting
argument makes the derived middle parabolic normalize the actual conjugate
actor; its concrete no-E₄ obstruction completes the contradiction.

`nonsplitting_bounds` supplies the fixed-codimension and displacement-line
forms used by the later critical-pair consumers. The only splitting premise
is the precise two-factor B.4.9(1) statement. The natural head, compatible
chief factors and genuine earlier chapter facts remain the authorized inputs
of these conditional implications; the full 13.8.25 theorem is assembled
by the parent development.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/
