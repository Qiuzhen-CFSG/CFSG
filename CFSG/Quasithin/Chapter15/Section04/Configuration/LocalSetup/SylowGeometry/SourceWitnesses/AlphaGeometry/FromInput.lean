module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.AlphaGeometry.LocalData
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.AlphaSource

/-!
# The complete actual-module source application for 15.4.19

Baumann's argument is applied to the original four-dimensional module, with
all offender, generation and codimension hypotheses proved. It constructs
the Thompson-center decomposition and the original Baumann Sylow supplement.
These feed the same residual pairs and all four central-space calculations.
No whole-module decomposition, fixed summand or Sylow supplement is assumed.

The post-Sylow theorem constructs LocalData on those same pairs; its sole
later input is the uniform overgroup-Sylow conclusion of 15.4.20.
Source: Aschbacher--Smith, B.2.18 and 15.4.12,19--20, pp.81,1160--1165.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M M₁ M₂ X Y : Subgroup G}

/-- Construct every whole-module hypothesis actually used by the four
central-space calculations from the unchanged original source input. -/
theorem source_thompsonGeometry (h : Input K T M X 2) : ThompsonGeometry T M X := by
  obtain ⟨he, hc, _, ha⟩ := MarkedProduct.source_baumann_module h
  apply thompsonGeometry_of_alpha h (MarkedProduct.source_sylow_and_core h).2.1 he
  · simpa only [ChapterB.thompsonJ_zero] using ha
  · simpa only [ChapterB.thompsonJ_zero] using hc

/-- All three clauses of 15.4.19 and all four local intersections follow
from the actual source inputs, without Earlier412 or a fixed-space premise. -/
theorem source_geometry_conclusions_from_input
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥) :
    Conclusions (geometry pX pY) :=
  source_geometry_conclusions_thompson hX hY pX pY
    (source_thompsonGeometry hX) (source_thompsonGeometry hY)
    hM₁ hM₂ huniqueX huniqueY hne hZcard hCZ

/-- Construct the genuine geometry, including its original J, Z and V(M),
with source 15.4.19 valid simultaneously for every factor pair. -/
theorem source_lemma_15_4_19_from_input
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥) :
    ∃ d : Source.Geometry G,
      d.T = T ∧ d.wholeX = X ∧ d.wholeY = Y ∧ d.M₁ = M₁ ∧ d.M₂ = M₂ ∧
      d.J = ChapterB.thompsonJ (T : Subgroup G) 0 ∧
      d.Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧
      d.VM₁ = localV T M₁ ∧ d.VM₂ = localV T M₂ ∧ Conclusions d :=
  source_lemma_15_4_19_thompson hX hY (source_thompsonGeometry hX)
    (source_thompsonGeometry hY) hM₁ hM₂ huniqueX huniqueY hne hZcard hCZ

/-- The original source inputs and 15.4.20 construct every LocalData field
on the same pairs; no earlier module or local-data certificate remains. -/
theorem source_geometry_localData_from_input
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥)
    (hSylow : ∀ i j, ∀ H ∈ Chapter1.HOver G ((geometry pX pY).I i j : Set G),
      ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = (geometry pX pY).T₀) :
    Nonempty (Source.LocalData (geometry pX pY)) :=
  source_geometry_localData_thompson hX hY pX pY
    (source_thompsonGeometry hX) (source_thompsonGeometry hY)
    hM₁ hM₂ huniqueX huniqueY hne hZcard hCZ hSylow

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
