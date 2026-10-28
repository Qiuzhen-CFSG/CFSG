module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.MarkedBorel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.CoreObstruction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceAlternatives

/-!
# Local SL₃(4) graph alternatives

`source_alternatives` constructs the source Borel marking and applies the
intrinsic calculation. It retains B = O²(B₀), B = θ(B) ≤ L₁, three-rank two,
the covered A₆ model, the actual Borel two-core and the full torus quotient.
Its graph branch supplies the original t*'s special-linear action and the
central X* comparison. Its graph-field branch supplies the actual central
L₀* image and derives H ≤ N_G(L₀).

Both branches compare the relevant two-residual with the center, rather
than asserting the obstructed full-centralizer identity. Earlier source
clauses and standard-automorphism coverage remain explicit inputs; the
parent owns coverage, final exclusion and module assembly. The normalizer
tool below uses precisely N_G(L₀) ≤ M from 13.2.2(9) and recovers
two-perfectness from L₀'s definition.

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955
(PDF pp.971–972), combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
open LinearThree.Geometry.CoveredProduct
variable {G : Type*} [Group G] [Finite G]

/-- The source normalizer step with L₀'s actual definition and the source inclusion. -/
theorem central_zero_contradiction (H K L M : Subgroup G)
    [(Source.starImage H K).Normal] (eK : Source.starImage H K ≃* SL)
    (hLH : ResidualPlacement.zero L ≤ H)
    (hLK : Source.starImage H (ResidualPlacement.zero L) ≤ Source.starImage H K)
    (hQ : Source.QH H ≤ normalizer (ResidualPlacement.zero L : Set G))
    (hz : modelImage H K (ResidualPlacement.zero L) eK = center SL)
    (hNM : normalizer (ResidualPlacement.zero L : Set G) ≤ M) (hHM : ¬ H ≤ M) : False :=
  graph_field_contradiction H K (ResidualPlacement.zero L) M hLH (zero_isPPerfect L) hQ
    (starImage_eq_center_of_modelImage H K _ eK hLK hz) hNM hHM

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
