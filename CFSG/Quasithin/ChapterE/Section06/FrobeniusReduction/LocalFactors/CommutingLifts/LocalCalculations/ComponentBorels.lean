module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.Orders
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.UnitaryThree

/-!
# Local commutator control in component Borels

Every component Borel in E.6.11(3b) admits a regular cyclic subgroup with
the original action image on V such that commuting odd actors centralize it
modulo O₂(L ∩ M). For PSL₂, Suzuki, and central two-covers of PSL₃(4), the
Borel order bounds the whole action kernel by its two-core. For PSU₃,
the cyclic Borel quotient makes the image of the original torus invariant.
For ordinary PSL₃, a compatible root torus gives the required calculation
for the actual matrix automorphisms, including their graph and field parts.

The theorem below assembles all five model constructors. It keeps the actual
model isomorphisms, the unitary fixed-field parameter, the embedded Sylow
subgroup and the relative C-component normalization hypothesis. Its output
feeds `ConjugateAssembly.exists_calculations_of_replacement`; no extra action
or kernel premise remains. The earlier E.6.11 component and torus conclusions
remain explicit inputs, to be supplied by the source theorem's assembly.
Source: Aschbacher–Smith, E.6.11(3b) and E.6.25, printed pp.249–250,255.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
open Components
variable {G : Type*} [Group G] [Finite G]

/-- Every E.6.11 component Borel supplies the local commutator bound used
in E.6.25, after a possible replacement of the regular cyclic subgroup.
The replacement preserves its actual induced action image on V. -/
theorem componentBorel_lift
    {K : GroupClass} {T : Sylow 2 G} {M V U Q L X : Subgroup G}
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hLC : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hX : RegularCyclicSection M V U X)
    (b : BorelAlternative M V U L (subgroupCorank V U))
    (t : TorusAction M V L X (subgroupCorank V U))
    (hn : 1 < subgroupCorank V U)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    ComponentBorelLiftConclusion M V U L X := by
  have hXL : X ≤ L := t.le_intersection.trans inf_le_left
  cases b.model with
  | linear_two _ iso =>
      exact componentBorel_lift_linear_two h earlier hU hX hLC hXL b hQ S hS iso
  | suzuki m hm hnm iso =>
      obtain ⟨e⟩ := iso
      exact componentBorel_lift_suzuki h earlier hU hX hLC hXL b hQ S hS m hm hnm e
  | linear_three _ iso =>
      exact componentBorel_lift_linear_three h earlier hU hL hLC hX b t hn hVL hQ S hS iso
  | unitary_three _ iso =>
      exact componentBorel_lift_unitary_three h earlier hU hX hL hLC hXL b hn hQ S hS iso
  | linear_three_cover hnm hz iso =>
      exact componentBorel_lift_linear_three_cover h earlier hU hX hLC hXL b hnm hz iso

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
