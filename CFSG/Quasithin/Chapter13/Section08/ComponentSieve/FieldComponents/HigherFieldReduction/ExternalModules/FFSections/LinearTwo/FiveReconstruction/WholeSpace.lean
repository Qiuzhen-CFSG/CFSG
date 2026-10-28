module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import Theory.Representation.BinaryOffender.ConjugationGeneration

/-!
# Whole-space generation when the seed actor lies in the component

These conditional lemmas apply when `L₁ ≤ K`. In the notation of
13.7.5, that containment, `V₃ = [V₃,L₁]`, and normality give
`U_H = [U_H,K]`.  The literal quotient map
`U_H → U_H/V₁`, together with the actual conjugation formula for `ρ`, then
gives full commutator generation by the actual image `K*`.

Consequently a subrepresentation containing the source `K*`-moved space is
the whole literal `SeedAction.Space H V₃ V₁`.  The only module input in the
last step is the F.9.18(6) moved-space clause
`W = [U_H/V₁,K*]`; no equality `U = W`, vanishing centralizer, splitting,
dimension, or whole-module irreducibility is used as a premise.

This does not discharge external alternative (a) of 13.8.20, where
`X ≤ L₁` and `X ≰ K`. The source proves `L₁ ≤ K` on p.955 only after
eliminating alternative (a). Likewise 13.7.5 assumes `X ≤ K`, and
13.8.21 follows 13.8.20. None supplies the missing containment in the
external alternative.

Source: Aschbacher–Smith, Lemma 13.7.5(1–2), printed p.938, and the
internal alternative (b) of 13.8.20, printed p.955 (combined manuscript,
1 March 2004). The external central-quotient problem is separate.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.Source

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

variable {G : Type*} [Group G] [Finite G]
variable (H K L₁ T V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  [(Source.starImage H K).Normal]
  [(K.subgroupOf H).Normal]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)

include hρ

/- The actual source generation clause, transported through the literal
quotient.  `hH` is the source product `H = K L₁ T`; it is used only to
obtain the inclusion `K ≤ H` needed by the quotient map. -/
omit [Finite G] [(Source.starImage H K).Normal] in
theorem source_moved_eq_top
    (hH : H = K ⊔ (L₁ ⊔ T))
    (hL₁K : L₁ ≤ K)
    (hseed : V₃ = ⁅V₃, L₁⁆) :
    subspaceCommutator ρ ⊤ (Source.starImage H K) = ⊤ := by
  have hK : K ≤ H := hH ▸ le_sup_left
  have hUH : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ :=
    CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.UH_eq_commutator_of_seed
      H K L₁ V₃ hK hL₁K hseed
  let f : K →* Source.Hstar H :=
    (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hK)
  have hf : f.range = Source.starImage H K := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.val, hK y.property⟩, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.val, hy⟩, rfl⟩
  have hKU : K ≤ normalizer (Source.UH H V₃ : Set G) :=
    hK.trans (le_normalizer_conjugateSpanBy V₃ H)
  let q : Source.UH H V₃ →* Source.Utilde H V₃ V₁ :=
    QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
  have hgen : ⁅K, Source.UH H V₃⁆ = Source.UH H V₃ := by
    rw [commutator_comm]
    exact hUH.symm
  have hfull := commutator_eq_top_of_conjugation ρ (Source.UH H V₃) K hKU f q
    (QuotientGroup.mk'_surjective _) (fun k u => by
      exact hρ ⟨k.val, hK k.property⟩ u) hgen
  simpa only [hf] using hfull

/- The `SourceHypotheses` record stores the same product left-associated as
`H = K ⊔ L₁ ⊔ T`.  Keep that source-facing shape available at the boundary. -/
omit [Finite G] [(Source.starImage H K).Normal] in
theorem source_moved_eq_top_of_generation
    (hH : H = K ⊔ L₁ ⊔ T)
    (hL₁K : L₁ ≤ K)
    (hseed : V₃ = ⁅V₃, L₁⁆) :
    subspaceCommutator ρ ⊤ (Source.starImage H K) = ⊤ := by
  apply source_moved_eq_top H K L₁ T V₃ V₁ ρ hρ
    (by simpa only [sup_assoc] using hH) hL₁K hseed

/- Existing Chapter 13 source APIs often retain the conjugate-span form of
the product setup.  Once 13.7.5(1) has made `K` normal in `H`, that form is
the literal product form used above. -/
omit [Finite G] [(Source.starImage H K).Normal] in
theorem source_moved_eq_top_of_conjugateSpan
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T))
    (hL₁K : L₁ ≤ K)
    (hseed : V₃ = ⁅V₃, L₁⁆) :
    subspaceCommutator ρ ⊤ (Source.starImage H K) = ⊤ := by
  have hK : K ≤ H := (le_conjugateSpanBy K T).trans (hH ▸ le_sup_left)
  have hT : T ≤ H := hH ▸ le_sup_right.trans le_sup_right
  have hspan : conjugateSpanBy K T = K := by
    apply le_antisymm
    · exact conjugateSpanBy_le le_rfl
        (hT.trans (le_normalizer_of_normal_subgroupOf hK))
    · exact le_conjugateSpanBy K T
  apply source_moved_eq_top H K L₁ T V₃ V₁ ρ hρ
    (by rw [← hspan]; exact hH) hL₁K hseed

/- The final central-quotient elimination.  The hypothesis is only the
F.9.18(6) containment of the actual moved space in `W`; equality is supplied
by the constituent assembly when available. -/
omit [Finite G] [(Source.starImage H K).Normal] in
theorem whole_space_of_moved_le
    (W : Subrepresentation ρ)
    (hH : H = K ⊔ (L₁ ⊔ T))
    (hL₁K : L₁ ≤ K)
    (hseed : V₃ = ⁅V₃, L₁⁆)
    (hW : subspaceCommutator ρ ⊤ (Source.starImage H K) ≤ W.toSubmodule) :
    W.toSubmodule = ⊤ := by
  apply top_unique
  rw [← source_moved_eq_top H K L₁ T V₃ V₁ ρ hρ hH hL₁K hseed]
  exact hW

omit [Finite G] [(Source.starImage H K).Normal] in
theorem whole_space_of_generation
    (W : Subrepresentation ρ)
    (hH : H = K ⊔ L₁ ⊔ T)
    (hL₁K : L₁ ≤ K)
    (hseed : V₃ = ⁅V₃, L₁⁆)
    (hW : subspaceCommutator ρ ⊤ (Source.starImage H K) ≤ W.toSubmodule) :
    W.toSubmodule = ⊤ := by
  exact whole_space_of_moved_le H K L₁ T V₃ V₁ ρ hρ W
    (by simpa only [sup_assoc] using hH) hL₁K hseed hW

/- Equality form of the moved-space input, conditional on the same
containment `L₁ ≤ K`. -/
omit [Finite G] [(Source.starImage H K).Normal] in
theorem whole_space
    (W : Subrepresentation ρ)
    (hH : H = K ⊔ (L₁ ⊔ T))
    (hL₁K : L₁ ≤ K)
    (hseed : V₃ = ⁅V₃, L₁⁆)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K)) :
    W.toSubmodule = ⊤ := by
  exact whole_space_of_moved_le H K L₁ T V₃ V₁ ρ hρ W hH hL₁K hseed hW.symm.le

omit [Finite G] [(Source.starImage H K).Normal] in
theorem whole_space_of_conjugateSpan
    (W : Subrepresentation ρ)
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T))
    (hL₁K : L₁ ≤ K)
    (hseed : V₃ = ⁅V₃, L₁⁆)
    (hW : subspaceCommutator ρ ⊤ (Source.starImage H K) ≤ W.toSubmodule) :
    W.toSubmodule = ⊤ := by
  have hK : K ≤ H := (le_conjugateSpanBy K T).trans (hH ▸ le_sup_left)
  have hT : T ≤ H := hH ▸ le_sup_right.trans le_sup_right
  have hspan : conjugateSpanBy K T = K := by
    apply le_antisymm
    · exact conjugateSpanBy_le le_rfl
        (hT.trans (le_normalizer_of_normal_subgroupOf hK))
    · exact le_conjugateSpanBy K T
  exact whole_space_of_moved_le H K L₁ T V₃ V₁ ρ hρ W
    (by rw [← hspan]; exact hH) hL₁K hseed hW

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

end
