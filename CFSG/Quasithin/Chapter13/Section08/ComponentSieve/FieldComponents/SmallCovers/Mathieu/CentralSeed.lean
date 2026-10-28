module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.SourceSeed
public import Theory.Representation.BinaryOffender.IrreducibleCentralSeed

/-!
# The M₂₂ contradiction on the actual central quotient

F.9.18 starts with I ∈ Irr⁺, whose irreducible representation is on I/C_I(K).
The earlier code contradiction requires recognition of I itself. Here the
irreducible rank-two seed is proved disjoint from C_I(K), so its literal
inclusion followed by the central quotient is injective and equivariant.
The quotient therefore supports the same parabolic fixed-line contradiction,
without a splitting assumption on I.

Recognition may choose its own M₂₂ coordinates. As in CodeAction, placement
is rerun in those coordinates, and the actual radical action is compared
through the star quotient. The M₂₄ fixed-line theorem then restricts to the
native ten-dimensional hyperplane. This applies the existing
`no_rank_two_seed_in_parabolic_fixed_line` to the central quotient.

The invariant Irr⁺ space, its saturation I = [Ũ_H,K], and code recognition
of its central quotient remain obligations of the representation-selection
argument. This module is a proved alternative terminal reduction, not a
claim that the M₂₂ branch has been assembled from F.9.18 and B.4.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21(2), printed p.956, PDF p.973, and A.1.40/F.9.18 (1 March 2004).
-/

@[expose] public noncomputable section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
open Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]
variable (H K L₁ T G₁ M V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The ambient H*-action on the literal central quotient I / C_I(K*). -/
def sourceCentralRepresentation (s : Placement.Setup H K L₁ T G₁ M)
    (d : SourceAction H V₃ V₁) (I : Subrepresentation d.representation) :
    Representation (ZMod 2) (Source.Hstar H)
      (centralQuotient d.representation (Source.starImage H K) I.toSubmodule) := by
  let := s.star_component_normal
  exact normalCentralQuotient d.representation (Source.starImage H K) I

omit [Finite G] in
/-- Restriction to K* is exactly the action in the Irr⁺ definition. -/
theorem sourceCentralRepresentation_restrict (s : Placement.Setup H K L₁ T G₁ M)
    (d : SourceAction H V₃ V₁) (I : Subrepresentation d.representation)
    (hst : Source.starImage H K ≤ subspaceStabilizer d.representation I.toSubmodule) :
    (sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I).comp
        (Source.starImage H K).subtype =
      centralQuotientRepresentation d.representation (Source.starImage H K) I.toSubmodule hst := rfl

/-- Central-quotient recognition suffices for the source contradiction.
The moved-space identity and code recognition remain explicit obligations;
no splitting of the chosen Irr⁺ space is needed. -/
theorem source_central_code_contradiction_of_group_seed
    (s : Placement.Setup H K L₁ T G₁ M) (d : SourceAction H V₃ V₁)
    (hline : V₁ < V₃) (hindex : (V₁.subgroupOf V₃).index = 4)
    (hgen : ⁅V₃, L₁⁆ = V₃) (hn : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      L₁ ⊔ T ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃)
    (I : Subrepresentation d.representation)
    (hI : I.toSubmodule = subspaceCommutator d.representation ⊤ (Source.starImage H K))
    (hcode : MathieuCode.IsM22Code
      ((sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I).comp
        (Source.starImage H K).subtype))
    (hfixed : MathieuCode.M24OctadFixedLine) : False := by
  let := s.star_component_normal
  let S := markedSeed H V₃ V₁ d.representation (d.isSourceAction H V₃ V₁) (L₁ ⊔ T) hn
  let : Representation.IsIrreducible S.toRepresentation :=
    markedSeed_irreducible H V₃ V₁ d.representation (d.isSourceAction H V₃ V₁)
      (L₁ ⊔ T) s.seed_join_sylow_le hn hline hirr
  have hS : S.toSubmodule =
      subspaceCommutator d.representation S.toSubmodule (Source.starImage H L₁) := by
    have hs := source_seed_commutator H V₃ V₁ d L₁
      (s.seed_le_component.trans s.component_le) (le_sup_left.trans hn) hline.le hgen
    rw [SourceAction.onH, commutator_inflation] at hs
    exact hs
  have hLK : Source.starImage H L₁ ≤ Source.starImage H K :=
    map_mono (subgroupOf_mono H s.seed_le_component)
  have hSI := seed_le_component d.representation (Source.starImage H K)
    (Source.starImage H L₁) I S.toSubmodule hLK hI hS
  let f := centralSeedMap d.representation (Source.starImage H K)
    I.toSubmodule S.toSubmodule hSI
  have hf : Function.Injective f := centralSeedMap_injective _ _ _ _ hSI
    (irreducible_commutator_disjoint_fixedSpace d.representation
      (Source.starImage H K) (Source.starImage H L₁) (Source.starImage H (L₁ ⊔ T))
      S le_normalizer_of_normal hLK hS)
  let σ := sourceCentralRepresentation H K L₁ T G₁ M V₃ V₁ s d I
  let τ := σ.comp (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨eK, E, he⟩ := hcode
  let e := (Components.componentStarEquiv H K s.component_le s.component).trans eK
  let s' := s.withModel e
  obtain ⟨w⟩ := s'.source_placement V₃ (ne_bot_of_gt hline) hgen
  have hrad : ∀ q v, E (τ q.val v) =
      MathieuCode.m22CodeRepresentation (w.radicalMap q) (E v) := by
    intro q v
    change E (σ (QuotientGroup.mk' (pCore 2 H) q.val) v) = _
    rw [w.radical_star]
    have hh := he ((Components.componentStarEquiv H K s'.component_le s'.component)
      (s'.model.symm (w.radicalMap q))) v
    simpa [s', Placement.Setup.withModel, e, MulEquiv.trans_apply] using hh
  let := source_seed_irreducible H V₃ V₁ d (L₁ ⊔ T) s.seed_join_sylow_le hn hline hirr
  exact no_rank_two_seed_in_parabolic_fixed_line τ
    ((L₁ ⊔ T).subgroupOf H) (s'.hexadOvergroup w.hexad)
    (seedRepresentation d.onH ((L₁ ⊔ T).subgroupOf H)
      (source_seed_stable d (L₁ ⊔ T) hn)).toRepresentation f hf
    (fun _ _ => rfl) (source_seed_finrank H V₃ V₁ hindex)
    (w.fixed_core_compare τ)
    (fixed_line_of_radical_model τ _ MathieuCode.m22CodeRepresentation w.radicalMap E hrad
      _ w.radical_range (MathieuCode.m22Hexad_fixedSpace_finrank_of_M24 hfixed w.hexad_mem))
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
