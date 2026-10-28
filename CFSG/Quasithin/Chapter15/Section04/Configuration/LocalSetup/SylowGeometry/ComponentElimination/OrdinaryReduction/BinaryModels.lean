module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.Inputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Actions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.BinaryModels.Quotient
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.BinaryModels.Comparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.BinaryModels.LinearThreeFour
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.BinaryModels.Sporadic

/-!
# The ordinary binary component and its inner actions

First identify the actual quotient K/O₂(K) with PSL₄(2) or PSL₅(2)
inside the given automorphism quotient of H. The odd-core hypothesis
makes the component center its two-core. Applying the full six-way
1.1.5(3) alternative excludes the central-cover, alternating, and
sporadic obstructions by the proved model comparisons. The remaining
cases have trivial center and give literal inner automorphisms.

A nonidentity element of the source four-group therefore kills the
component's two-core, identifying K itself. For every element of Z,
the action's conjugator is transported from K as a subgroup of H to
K as a subgroup of G, giving the ambient equality in CentralInnerAction.

This completes the conditional binary-model contract. The parent owns
the derivation of the odd-core and ordinary-component hypotheses and
the subsequent binary central-four obstruction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 15.4.20, printed p.1164; full 1.1.5, printed pp.501–503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open OrdinaryReduction BinaryModels Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The ordinary component itself is a binary PSL model, and every actor
in the source central four-group acts by conjugation by an element of K. -/
theorem binary_models_of_ordinary {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : Earlier115Three κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (hodd : pPrimeCore 2 H = ⊥)
    (hcomponent : IsComponent H (K.subgroupOf H)) (hmodel : BinaryAutomorphismModel H) :
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL K n 2) ∧
      CentralInnerAction K d.Z := by
  have hKH : K ≤ H := s.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _
  let eK := subgroupOfEquivOfLe hKH
  let : IsQuasisimple (K.subgroupOf H) := hcomponent.2
  obtain ⟨n, hn, hm⟩ := source_binary_quotient s hcomponent hmodel
  let eQK := QuotientGroup.congr (pCore 2 (K.subgroupOf H)) (pCore 2 K) eK
    (pCore_map_iso 2 eK)
  have hquot := hm.of_mulEquiv eQK
  have hcenter := Chapter15.Section03.component_center_eq_twoCore hcomponent hodd
  obtain ⟨_, _, _, ha⟩ := component_actions_of_earlier115 hG earlier s.local115 hKH hcomponent
  have hf (z : G) (hz : z ∈ d.Z) (hne : z ≠ 1) :
      center (K.subgroupOf H) = ⊥ ∧
        ∃ l : K.subgroupOf H, ∀ x : K.subgroupOf H,
          z * (x : G) * z⁻¹ = (l : G) * (x : G) * (l : G)⁻¹ := by
    obtain ⟨α, hα, hm⟩ := ha z hz hne
    obtain ⟨hc, l, hl⟩ := model_action_of_separation linearThreeFour_separation
      sporadic_separation hn hcenter hquot hm
    refine ⟨hc, l, ?_⟩
    intro x
    rw [← hl] at hα
    exact (hα x).symm
  let : Nontrivial d.Z := Finite.one_lt_card_iff_nontrivial.mp (by rw [s.four]; decide)
  obtain ⟨z, hz⟩ := exists_ne (1 : d.Z)
  have hcore : pCore 2 (K.subgroupOf H) = ⊥ :=
    hcenter.symm.trans (hf z z.property (fun he => hz (Subtype.ext he))).1
  let eL : (K.subgroupOf H) ≃* ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm
  refine ⟨⟨n, hn, (hquot.of_mulEquiv eL).of_mulEquiv eK.symm⟩, ?_⟩
  intro z
  by_cases hz : (z : G) = 1
  · exact ⟨1, fun x => by simp [hz]⟩
  obtain ⟨l, hl⟩ := (hf z z.property hz).2
  refine ⟨eK l, ?_⟩
  intro x
  obtain ⟨x, rfl⟩ := eK.surjective x
  exact hl x

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
