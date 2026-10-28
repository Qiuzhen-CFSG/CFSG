module
public import Glauberman.PushingUpActionRecognition
public import Glauberman.PushingUpNaturalActionConsequences
/-!
# Original omega fixed-index conclusions

The source action-recognition theorem constructs the actual SL2(4) quotient
and natural coordinates. Applying the literal fixed-index and moved-centralizer
consequences discharges those extra premises: every subgroup of the original
Sylow group outside O2(H) moves at least four omega elements, and every
supplement of O2(H) has fixed index sixteen and the required Sylow intersection
with its moved-group centralizer.

This is the Niles2.9 input consumed by the source7.6 proof, without an assumed
quotient marking or a chosen module diagram. Source: Niles, Pushing-up in finite
groups (1979), Lemmas2.9 and7.6, printed pp.33 and61–62.
-/
set_option backward.isDefEq.respectTransparency false
public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace Glauberman
variable {H F:Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- Niles2.9 fixed-index conclusions under only the original source inputs. -/
theorem original_psl2_four_omega_fixedIndex_data
    (hF:Nat.card F=4) (S:Sylow 2 H)
    (hu:Order.HasUniqueMaximalOver (S:Subgroup H) ⊤)
    (K:Subgroup H) [K.Normal]
    (e:(H⧸K)≃*Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf:generalizedFitting H=pCore 2 H)
    (hno:NoCharacteristicNormal (S:Subgroup H)) :
    (∀A:Subgroup H,A≤(S:Subgroup H)→¬A≤pCore 2 H→
      4≤(omegaCenterIn (pCore 2 H)⊓centralizer (A:Set H)).relIndex (omegaCenterIn (pCore 2 H))) ∧
    (∀L:Subgroup H,L⊔pCore 2 H=⊤→
      (omegaCenterIn (pCore 2 H)⊓centralizer (L:Set H)).relIndex (omegaCenterIn (pCore 2 H))=16 ∧
      (S:Subgroup H)⊓centralizer ((⁅omegaCenterIn (pCore 2 H),L⁆:Subgroup H):Set H)=pCore 2 H) := by
  obtain ⟨q,hq,hk,hA,heq,hcard,E,hE⟩ :=
    original_psl2_four_omegaAction_recognition hF S hu K e hf hno
  constructor
  · intro A hAS hAQ
    exact original_omega_fixedIndex_lower_of_natural_quotient hF S hu K e q hq hk E hE A hAS hAQ
  · intro L hL
    obtain ⟨hi,hc⟩ := original_omega_supplement_natural_data q hq hk E hE L hL
    refine ⟨hi,?_⟩
    rw [hc]
    exact original_omega_sylow_centralizer_eq hF S hu K e q hq hk
end Glauberman
