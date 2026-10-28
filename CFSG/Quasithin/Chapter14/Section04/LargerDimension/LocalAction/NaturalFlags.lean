module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.SourceFlags
public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry

/-!
# The natural-action input for the original source flag

The genuine earlier natural-module hypothesis says that the actual
conjugation action of L on the elementary group V is the full automorphism
group, with kernel O₂(L). L is two-perfect and T-invariant. Together with
the actual three-dimensional flag of Notation 12.8.2 this is the input for
constructing the two residual parabolics. It contains none of their cubic,
commutator-generation or flag-intersection conclusions.

`NaturalFlags.Construction` constructs the source flags from this input;
`NaturalFlagData` is its output contract, not an encoding of the hypothesis.
The elementary containment V≤E is proved here using the literal conjugator
and the existing source 12.8.13(1) calculation.

Source: Aschbacher--Smith, Hypothesis 12.8.1 and Notation 12.8.2,
14.3.10 and 14.4.8(1), printed pp.849,993,1009.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
variable {G : Type*} [Group G]

/-- The earlier natural action, keeping its literal map and kernel. -/
structure NaturalThreeAction (L V : Subgroup G) (T : Sylow 2 G) where
  residual : twoResidual L = L
  T_normalizes : (T : Subgroup G) ≤ normalizer (L : Set G)
  normalizes : L ≤ normalizer (V : Set G)
  surjective : Function.Surjective (conjugation L V normalizes)
  kernel : (conjugation L V normalizes).ker = pCore 2 L

/-- The actual source E contains V. This uses g∈L, so the chosen conjugator
normalizes the natural module; no moved-space equality is assumed. -/
theorem natural_flag_seed_le_E {L V : Subgroup G} {T : Sylow 2 G}
    [IsElementaryAbelian 2 V] (d : NaturalThreeAction L V T)
    (F : Chapter12.Section08.InvariantFlag T V 3) (g : G) (hg : g ∈ L) :
    V ≤ F.E g := by
  exact F.seed_le_E_of_normalizes g (d.normalizes hg)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
