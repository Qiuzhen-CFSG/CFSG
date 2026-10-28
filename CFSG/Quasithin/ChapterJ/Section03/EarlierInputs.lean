module
public import CFSG.Quasithin.ChapterJ.Section03.Order
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.CubicSource
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Five

/-!
# The remaining earlier-source inputs to J.3.1

The original normalizer construction supplies both involution classes and
an ambient Sylow three-group of order27. The original five-centralizer
supplies the order125 odd core. Substituting those unconditional producers
leaves precisely J.2's Suzuki residual and middle-layer count480 as inputs
to the already proved order argument.

Source: Aschbacher--Smith J.2.7 and J.3.1--5, printed pp.437--439.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

/-- All independent cubic, five-core and two-class inputs are discharged;
only the indicated earlier J.2 conclusions remain. -/
theorem order_of_suzuki_and_middle_count (c : Choices d) (r : c.SuzukiSourceConclusion)
    (h480 : Nat.card {x : G // IsConj c.z x ∧ x∈d.toTypeRuSetup.K ∧
      x∉d.toTypeRuSetup.Q}=480) :
    Nat.card G=2^14*3^3*5^3*7*13*29 := by
  obtain ⟨P3,h3,_⟩ := SourceCompletion.cubic_sylow_source c
  let B5 : Sylow 5 d.toTypeRuSetup.H := Classical.choice inferInstance
  exact order_of_source_inputs c r (c.two_involution_classes_source) h480 P3 h3
    (fiveOddPart B5) (SourceCompletion.five_oddPart_card c B5)

end CFSG.Quasithin.ChapterJ.Section03
