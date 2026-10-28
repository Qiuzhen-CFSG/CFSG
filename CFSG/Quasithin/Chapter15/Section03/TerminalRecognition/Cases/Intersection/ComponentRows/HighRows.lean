module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Basic
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Actions
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.Permutation
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows.Mathieu
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows.Components
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows.FullActor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows.Thompson

/-!
# Degree-three and Mathieu rows of the terminal intersection

Rows (12) and (13) are excluded by the actual M₁₂ component order.
The degree-three component sieve identifies the component in (10) and
(11) with G₂(2)′. The full B.5.1 action then embeds G₂(2) in the
actual offender actor. This excludes (10), whose full ambient group
has order 6048, and makes the embedding surjective onto the ambient
graph extension in (11), which has order 12096. The isomorphism is
constructed from that embedding, never inferred just from the order.

The maximum-elementary argument in `HighRows.Thompson` identifies the
image of the original J(H) with the whole quotient in row (11). Together
with the graph involution's two-group quotient, this completes all three
required outputs. The row comparisons apply under either local labeling,
retaining the original source input and its normalization of J(T_E) by G₁.
The full B-side action witness remains explicit for the parent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.1/B.5.6, printed pp.99–105; F.6.18, pp.309–310;
and the final proof of 15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

namespace ComponentRows.HighRows
private theorem derived_card :
    Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 := by
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

private theorem full_card : Nat.card (Atlas.G2.Model (ZMod 2)) = 12096 := by
  norm_num [Atlas.G2.card_Model, Nat.card_zmod]

end ComponentRows.HighRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)
include d

/-- The actual component marking, together with the full B-side action,
constructs an embedding of full G₂(2) in the ambient quotient. -/
theorem full_g2_embedding_of_derived_component
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (e : generalizedFitting (coreQuotient H) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ∃ f : Atlas.G2.Model (ZMod 2) →* coreQuotient H, Function.Injective f := by
  have hc : Nat.card (generalizedFitting d.offenderGroup) = 6048 :=
    (Nat.card_congr ((d.offenderFittingEquiv hL).trans e).toEquiv).trans
      ComponentRows.HighRows.derived_card
  obtain ⟨f, hf⟩ := ComponentRows.HighRows.source_contains_full_g2 d.offenderAction c hc
  exact ⟨d.offenderGroup.subtype.comp f, d.offenderGroup.subtype_injective.comp hf⟩

/-- The complete degree-three full-component row is impossible in either
local labeling: its action would embed a group of order 12096 in one of order 6048. -/
theorem component_row_ten_false
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    {p : ℕ} (hp : p.Prime) (hm : p % 8 = 3 ∨ p % 8 = 5)
    (hdegree : FSource.DegreeThree p (coreQuotient H))
    (ht : generalizedFitting (coreQuotient H) = ⊤)
    (hs : Nonempty (d.quotientSylow ≃* FSource.W32)) : False := by
  obtain ⟨e⟩ := d.component_row_ten_derived hL c hp hm hdegree ht hs
  let eL := ((MulEquiv.subgroupCongr ht).trans topEquiv).trans e
  obtain ⟨f, hf⟩ := d.full_g2_embedding_of_derived_component hL c eL
  have hb := Nat.card_le_card_of_injective f hf
  rw [Nat.card_congr e.toEquiv, ComponentRows.HighRows.derived_card,
    ComponentRows.HighRows.full_card] at hb
  omega

/-- The full source action identifies the graph extension with the actual
G₂(2) octonion group and proves its required two-group quotient. This is
independent of the ordering of the two local subgroups. -/
theorem component_row_eleven_ambient
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (r : FSource.GraphExtensionRow (D := coreQuotient H))
    (hs : FSource.Extension d.quotientSylow FSource.C4Square FSource.E4) :
    Nonempty (coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  obtain ⟨e⟩ := d.component_row_eleven_derived hL c r hs
  have hc : Nat.card (coreQuotient H) = 12096 := by
    rw [← (generalizedFitting (coreQuotient H)).card_mul_index,
      ComponentRows.HighRows.graphRow_index r, Nat.card_congr e.toEquiv,
      ComponentRows.HighRows.derived_card]
  obtain ⟨f, hf⟩ := d.full_g2_embedding_of_derived_component hL c e
  have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [hc, ComponentRows.HighRows.full_card])
  exact ⟨⟨(MulEquiv.ofBijective f hb).symm⟩, ComponentRows.graphRow_quotient r⟩

/-- All three terminal outputs for the complete graph-extension row (11).
The original Thompson image is the full G₂(2) model. This uses the same
source input under either labeling of the local groups; the component
marking and ambient equivalence required by the Thompson argument are
constructed here from the row and the full B-side action. -/
theorem component_row_eleven
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (r : FSource.GraphExtensionRow (D := coreQuotient H))
    (hs : FSource.Extension d.quotientSylow FSource.C4Square FSource.E4) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  obtain ⟨⟨eD⟩, hquot⟩ := d.component_row_eleven_ambient hL c r hs
  obtain ⟨eL⟩ := d.component_row_eleven_derived hL c r hs
  obtain ⟨eX⟩ := d.thompson_image_g2 hL c eD eL
  exact ⟨.g2Two eX, .g2Two eD, hquot⟩

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
