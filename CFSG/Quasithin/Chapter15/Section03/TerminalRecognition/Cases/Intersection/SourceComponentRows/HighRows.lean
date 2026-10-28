module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceComponentRows.G2Thompson

/-!
# High rows for the corrected terminal source action

The existing degree-three and Mathieu component sieves consume the
source model extraction. The marked G₂(2) action then excludes row (10)
and identifies both the ambient group and Thompson image in row (11).

The proofs adapt the existing terminal `ComponentRows` comparison to the
full `ProjectiveLine.QuasisimpleSourceConclusion`. The two-dimensional
F₄ offender clause remains on the original action; no legacy clause is
constructed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1/B.5.6,
printed pp.99–105; F.6.18, pp.309–310; K.1.3, p.453; final proof of
15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

namespace SourceComponentRows.HighRows
universe u

private theorem degreeThree_comap {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) {p : ℕ} (h : FSource.DegreeThree p B) : FSource.DegreeThree p A := by
  cases h with
  | linear F hc hs f => exact .linear F hc hs (e.trans f)
  | projectiveLinear F hc hs f => exact .projectiveLinear F hc hs (e.trans f)
  | unitary F J hc hf hs f => exact .unitary F J hc hf hs (e.trans f)
  | projectiveUnitary F J hc hf hs f => exact .projectiveUnitary F J hc hf hs (e.trans f)

private theorem twoPart_of_sylow_card {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) {n : ℕ} (hS : Nat.card S = 2 ^ n) :
    (Nat.card D).factorization 2 = n := by
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) ((S.card_eq_multiplicity).symm.trans hS)

end SourceComponentRows.HighRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)
include d

/-- The degree-three full-component row has the actual G₂(2)′ model.
The full-group action exclusion remains a separate step. -/
theorem source_component_row_ten_derived
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    {p : ℕ} (hp : p.Prime) (hm : p % 8 = 3 ∨ p % 8 = 5)
    (hdegree : FSource.DegreeThree p (coreQuotient H))
    (ht : generalizedFitting (coreQuotient H) = ⊤)
    (hs : Nonempty (d.quotientSylow ≃* FSource.W32)) :
    Nonempty (coreQuotient H ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨s⟩ := hs
  have hS : Nat.card d.quotientSylow = 2 ^ 5 := by
    rw [Nat.card_congr s.toEquiv, RegularWreathProduct.card]
    norm_num [FSource.C]
  have hD := SourceComponentRows.HighRows.twoPart_of_sylow_card d.quotientSylow hS
  let f : generalizedFitting d.offenderGroup ≃* coreQuotient H :=
    (d.offenderFittingEquiv hL).trans ((MulEquiv.subgroupCongr ht).trans topEquiv)
  have hpL : (Nat.card (generalizedFitting d.offenderGroup)).factorization 2 = 5 := by
    rw [Nat.card_congr f.toEquiv, hD]
  obtain ⟨g⟩ := ComponentRows.HighRows.degreeThree_model_of_twoPart_five hp (by omega)
    (SourceComponentRows.HighRows.degreeThree_comap f hdegree) hpL (c.fittingModel d.offenderAction)
  exact ⟨f.symm.trans g⟩

/-- The graph row's component is G₂(2)′. No conclusion about the full
graph extension or the Thompson image is inferred from this comparison. -/
theorem source_component_row_eleven_derived
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (r : FSource.GraphExtensionRow (D := coreQuotient H))
    (hs : FSource.Extension d.quotientSylow FSource.C4Square FSource.E4) :
    Nonempty (generalizedFitting (coreQuotient H) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) := by
  let f := d.offenderFittingEquiv hL
  have hpL : (Nat.card (generalizedFitting d.offenderGroup)).factorization 2 = 5 := by
    rw [Nat.card_congr f.toEquiv]
    exact ComponentRows.HighRows.graphRow_fitting_twoPart r d.quotientSylow hs
  obtain ⟨g⟩ := ComponentRows.HighRows.degreeThree_model_of_twoPart_five r.prime_isPrime
    (by have h := r.congruence; omega)
    (SourceComponentRows.HighRows.degreeThree_comap f r.model.model) hpL (c.fittingModel d.offenderAction)
  exact ⟨f.symm.trans g⟩

end SourceInput

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)
include d

/-- F.6.18(13) is impossible: its actual component is M₁₂, whereas the
full source action gives one of the ten incompatible B.5.6 components.
The proof also applies to either labeling of its local subgroups. -/
theorem source_component_row_thirteen_false
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (e : generalizedFitting (coreQuotient H) ≃* Sporadic.Mathieu.M12) : False := by
  let f : generalizedFitting d.offenderGroup ≃* generalizedFitting (coreQuotient H) :=
    (MulEquiv.subgroupCongr (d.offender_fitting_eq hL)).trans
      (subgroupOfEquivOfLe ((d.fitting_le_thompson hL).trans d.thompson_image_le_offender))
  exact ComponentRows.HighRows.not_mathieuTwelve_model (f.trans e)
    (c.fittingModel d.offenderAction)

/-- F.6.18(12) is impossible in either local labeling. Simplicity of the
already constructed M₁₂ model identifies the ambient F* before comparison. -/
theorem source_component_row_twelve_false
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (e : coreQuotient H ≃* Sporadic.Mathieu.M12) : False := by
  let _ := Sporadic.Mathieu.m12_isSimpleGroup
  let _ : IsSimpleGroup (coreQuotient H) := e.isSimpleGroup
  have ht : generalizedFitting (coreQuotient H) = ⊤ := by
    have hn : generalizedFitting (coreQuotient H) ≠ ⊥ := by
      let _ := hL.simple
      let _ : Nontrivial (generalizedFitting (coreQuotient H)) :=
        (QuotientGroup.mk'_surjective (center (generalizedFitting (coreQuotient H)))).nontrivial
      exact (nontrivial_iff_ne_bot _).mp inferInstance
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_left hn
  exact d.source_component_row_thirteen_false hL c
    ((MulEquiv.subgroupCongr ht).trans (topEquiv.trans e))

end SourceInput

namespace SourceComponentRows.HighRows
private theorem derived_card :
    Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 := by
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

private theorem full_card : Nat.card (Atlas.G2.Model (ZMod 2)) = 12096 := by
  norm_num [Atlas.G2.card_Model, Nat.card_zmod]

end SourceComponentRows.HighRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)
include d

/-- The actual component marking, together with the full B-side action,
constructs an embedding of full G₂(2) in the ambient quotient. -/
theorem source_full_g2_embedding_of_derived_component
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (e : generalizedFitting (coreQuotient H) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ∃ f : Atlas.G2.Model (ZMod 2) →* coreQuotient H, Function.Injective f := by
  have hc : Nat.card (generalizedFitting d.offenderGroup) = 6048 :=
    (Nat.card_congr ((d.offenderFittingEquiv hL).trans e).toEquiv).trans
      SourceComponentRows.HighRows.derived_card
  obtain ⟨f, hf⟩ := SourceComponentRows.G2.projectiveLine_source_contains_full_g2 d.offenderAction c hc
  exact ⟨d.offenderGroup.subtype.comp f, d.offenderGroup.subtype_injective.comp hf⟩

/-- The complete degree-three full-component row is impossible in either
local labeling: its action would embed a group of order 12096 in one of order 6048. -/
theorem source_component_row_ten_false
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    {p : ℕ} (hp : p.Prime) (hm : p % 8 = 3 ∨ p % 8 = 5)
    (hdegree : FSource.DegreeThree p (coreQuotient H))
    (ht : generalizedFitting (coreQuotient H) = ⊤)
    (hs : Nonempty (d.quotientSylow ≃* FSource.W32)) : False := by
  obtain ⟨e⟩ := d.source_component_row_ten_derived hL c hp hm hdegree ht hs
  let eL := ((MulEquiv.subgroupCongr ht).trans topEquiv).trans e
  obtain ⟨f, hf⟩ := d.source_full_g2_embedding_of_derived_component hL c eL
  have hb := Nat.card_le_card_of_injective f hf
  rw [Nat.card_congr e.toEquiv, SourceComponentRows.HighRows.derived_card,
    SourceComponentRows.HighRows.full_card] at hb
  omega

/-- The full source action identifies the graph extension with the actual
G₂(2) octonion group and proves its required two-group quotient. This is
independent of the ordering of the two local subgroups. -/
theorem source_component_row_eleven_ambient
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (r : FSource.GraphExtensionRow (D := coreQuotient H))
    (hs : FSource.Extension d.quotientSylow FSource.C4Square FSource.E4) :
    Nonempty (coreQuotient H ≃* Atlas.G2.Model (ZMod 2)) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  obtain ⟨e⟩ := d.source_component_row_eleven_derived hL c r hs
  have hc : Nat.card (coreQuotient H) = 12096 := by
    rw [← (generalizedFitting (coreQuotient H)).card_mul_index,
      ComponentRows.HighRows.graphRow_index r, Nat.card_congr e.toEquiv,
      SourceComponentRows.HighRows.derived_card]
  obtain ⟨f, hf⟩ := d.source_full_g2_embedding_of_derived_component hL c e
  have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [hc, SourceComponentRows.HighRows.full_card])
  exact ⟨⟨(MulEquiv.ofBijective f hb).symm⟩, ComponentRows.graphRow_quotient r⟩

/-- All three terminal outputs for the complete graph-extension row (11).
The original Thompson image is the full G₂(2) model. This uses the same
source input under either labeling of the local groups; the component
marking and ambient equivalence required by the Thompson argument are
constructed here from the row and the full B-side action. -/
theorem source_component_row_eleven
    (hL : IsQuasisimple (generalizedFitting (coreQuotient H)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup))
    (r : FSource.GraphExtensionRow (D := coreQuotient H))
    (hs : FSource.Extension d.quotientSylow FSource.C4Square FSource.E4) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      IsPGroup 2 (coreQuotient H ⧸ generalizedFitting (coreQuotient H)) := by
  obtain ⟨⟨eD⟩, hquot⟩ := d.source_component_row_eleven_ambient hL c r hs
  obtain ⟨eL⟩ := d.source_component_row_eleven_derived hL c r hs
  obtain ⟨eX⟩ := d.source_thompson_image_g2 hL c eD eL
  exact ⟨.g2Two eX, .g2Two eD, hquot⟩

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
