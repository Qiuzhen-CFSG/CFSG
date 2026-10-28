module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.CodeAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SeedComparison
public import Theory.Representation.Quotient

/-!
# The M₂₂ seed from the actual earlier subgroup statements

The quotient and conjugation conventions here agree with the existing source
seed constructions. Their index calculation turns |V₃:V₁|=4 into binary
rank two. The invariant-subgroup criterion between V₁ and V₃ gives
irreducibility under L₁T, transported through the actual star map. Finally,
[V₃,L₁]=V₃ descends to the required linear commutator identity. Thus the
terminal code contradiction needs no separate assumptions on an unrelated
rank-two representation or its embedding.

The component moved-space identity and code recognition remain explicit
obligations. This module proves their contradiction with the earlier source
seed; it does not prove the F.9.18/B.4 recognition step.

Source: Aschbacher–Smith, 13.7.3(6), the standing setup on printed
pp.946–947, and 13.8.21(2), printed p.956 (PDF p.973), 1 March 2004.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
variable (d : SourceAction H V₃ V₁)

omit [Finite G] in
/-- The existing source-action convention is the same conjugation formula. -/
theorem SourceAction.isSourceAction : IsSourceAction H V₃ V₁ d.representation := d.conjugation

/-- The literal source index gives the dimension of its actual quotient image. -/
theorem source_seed_finrank (hindex : (V₁.subgroupOf V₃).index = 4) :
    Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2 :=
  Components.Suzuki.NaturalSections.sourceSeed_finrank_two H V₃ V₁ hindex

omit [Finite G] in
/-- Group commutator generation descends through the actual quotient. -/
theorem source_seed_commutator (L₁ : Subgroup G) (hLH : L₁ ≤ H)
    (hn : L₁ ≤ normalizer (V₃ : Set G)) (hline : V₁ ≤ V₃)
    (hgen : ⁅V₃, L₁⁆ = V₃) :
    seedSpace H V₃ V₁ =
      subspaceCommutator d.onH (seedSpace H V₃ V₁) (L₁.subgroupOf H) := by
  rw [SourceAction.onH, commutator_inflation]
  exact (image_commutator_eq H V₃ V₁ d.representation (d.isSourceAction H V₃ V₁)
    L₁ V₃ hLH (le_conjugateSpanBy V₃ H) hn
    (hline.trans (le_conjugateSpanBy V₃ H))
    (by rw [commutator_comm, hgen]; exact le_sup_left)).symm

omit [Finite G] in
/-- Transport the earlier invariant-subgroup criterion through the star map. -/
theorem source_seed_irreducible (P : Subgroup G) (hPH : P ≤ H)
    (hn : P ≤ normalizer (V₃ : Set G)) (hline : V₁ < V₃)
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      P ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃) :
    Representation.IsIrreducible
      (seedRepresentation d.onH (P.subgroupOf H)
        (source_seed_stable d P hn)).toRepresentation := by
  let f := (QuotientGroup.mk' (pCore 2 H)).subgroupMap (P.subgroupOf H)
  have hi := markedSeed_irreducible H V₃ V₁ d.representation
    (d.isSourceAction H V₃ V₁) P hPH hn hline hirr
  exact (Representation.irreducible_comp_surjective_iff f
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _) _).mpr hi

variable (K L₁ T G₁ M : Subgroup G)

/-- The source code contradiction using only the earlier subgroup seed facts.
The component recognition and moved-space identity still require proof. -/
theorem source_code_contradiction_of_group_seed (s : Placement.Setup H K L₁ T G₁ M)
    (hline : V₁ < V₃) (hindex : (V₁.subgroupOf V₃).index = 4)
    (hgen : ⁅V₃, L₁⁆ = V₃) (hn : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      L₁ ⊔ T ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃)
    (I : Subrepresentation d.representation)
    (hI : I.toSubmodule = subspaceCommutator d.representation ⊤ (Source.starImage H K))
    (hcode : MathieuCode.IsM22Code (I.toRepresentation.comp (Source.starImage H K).subtype))
    (hfixed : MathieuCode.M24OctadFixedLine) : False := by
  let := source_seed_irreducible H V₃ V₁ d (L₁ ⊔ T) s.seed_join_sylow_le hn hline hirr
  exact source_code_contradiction H K L₁ T G₁ M V₃ V₁ s d
    (ne_bot_of_gt hline) hgen hn I hI hcode
    (source_seed_commutator H V₃ V₁ d L₁
      (s.seed_le_component.trans s.component_le) (le_sup_left.trans hn) hline.le hgen)
    (source_seed_finrank H V₃ V₁ hindex) hfixed
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
