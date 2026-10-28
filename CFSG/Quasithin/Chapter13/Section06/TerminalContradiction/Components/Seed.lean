module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Definitions
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Selection

/-!
# The source-shaped terminal component seed

This file records the construction/lifting interface in Lemma 13.6.27.  The
ambient group in the file is the local group `G₁ = C_G(z)`, so every subgroup,
component and quotient below is intrinsic to that group.  The universal
Theorem 5.2.3, its 5.2.3.1 refinement, and the Chapter 1 adequate lift remain
explicit inputs.  Thus this module does not replace any of those source
theorems by a proposition already containing `Candidate`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
13.6.25--27, printed pp.934--935 (PDF pp.951--952), with Theorem 5.2.3,
A.3.12, 1.2.8 and E.2.2.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components

open Subgroup

universe u

variable {H : Type u} [Group H] [Finite H]

/-! ## The complete universal 5.2.3 implication -/

/-- The hypotheses retained when Theorem 5.2.3 is applied to `K₁`.

`residual`, `normalized` and `parameter` are the source hypotheses.  In
particular, this record contains no component or model conclusion. -/
structure Universal523Module (K₁ T : Subgroup H) : Prop where
  residual : K₁ = pResidual 2 H
  normalized : T ≤ normalizer (K₁ : Set H)
  parameter : 1 < ChapterE.generationParameter H

/-- The three alternatives of the universal 5.2.3 implication.

The second branch keeps the `L₂(4)` section and the component model supplied
by 5.2.3.1; the third branch is the equality `K₁ = K` and the genuine
`L₃(4)` quotient with its diagram action. -/
inductive Universal523Alternative (K₁ T : Subgroup H) : Prop
  | a7
      (model : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin 7))) :
      Universal523Alternative K₁ T
  | l2
      (K : Subgroup H)
      (component : K.IsCComponent)
      (contains : K₁ ≤ K)
      (normalized : T ≤ normalizer (K : Set H))
      (l2_section : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)))
      (model : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23)) :
      Universal523Alternative K₁ T
  | l3
      (K : Subgroup H)
      (component : K.IsCComponent)
      (equality : K = K₁)
      (normalized : T ≤ normalizer (K : Set H))
      (model : Nonempty ((K ⧸ pCore 2 K) ≃* L3Four))
      (diagram : ∃ e : (K ⧸ pCore 2 K) ≃* L3Four,
        NontrivialDynkinAction T K e) :
      Universal523Alternative K₁ T

/-! The non-`A₇` output is named so that the refinement and lifting inputs
refer to the same component witness. -/
def Universal523NonA7 (K₁ T K : Subgroup H) : Prop :=
  K.IsCComponent ∧ K₁ ≤ K ∧ T ≤ normalizer (K : Set H) ∧
    (Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
      (Nonempty ((K ⧸ pCore 2 K) ≃* L3Four) ∧
        ∃ e : (K ⧸ pCore 2 K) ≃* L3Four,
          NontrivialDynkinAction T K e))

/-- The complete universal implication, polymorphic in the selected residual. -/
def Universal523 (T : Subgroup H) : Prop :=
  ∀ K₁ : Subgroup H, Universal523Module K₁ T →
    Universal523Alternative K₁ T

/-! ## The source exclusions and lifting contracts -/

/-- The uniform `A₇` exclusion from Hypothesis 13.3.1. -/
def UniformNoA7 (_T : Subgroup H) : Prop :=
  ∀ K₁ : Subgroup H,
    Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin 7)) → False

/-- The 5.2.3.1 refinement.  It supplies only model identifications and the
diagram action; `Candidate` is formed below. -/
structure Universal523Refinement (K₁ T K : Subgroup H) : Prop where
  l2_section : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2))
  model : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
    Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
    (Nonempty ((K ⧸ pCore 2 K) ≃* L3Four) ∧
      ∃ e : (K ⧸ pCore 2 K) ≃* L3Four,
        NontrivialDynkinAction T K e)

/-- The adequate lift through `C_G(Z) ≤ C_G(z)`, after the source has supplied
the relevant Chapter 1 hypotheses. -/
structure AdequateLift (T K₁ K : Subgroup H) : Prop where
  component : K.IsCComponent
  contains : K₁ ≤ K
  normal : K.Normal
  model : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
    Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) ∨
    (Nonempty ((K ⧸ pCore 2 K) ≃* L3Four) ∧
      ∃ e : (K ⧸ pCore 2 K) ≃* L3Four,
        NontrivialDynkinAction T K e)

/-! ## Specialization of the universal output -/

set_option linter.unusedSectionVars false in
/-- Exclude the first universal alternative and expose the remaining source
data. -/
lemma Universal523Alternative.not_a7
    {K₁ T : Subgroup H} (hno : UniformNoA7 T)
    (h : Universal523Alternative K₁ T) :
    ∃ K : Subgroup H, Universal523NonA7 K₁ T K := by
  cases h with
  | a7 model => exact (hno K₁ model).elim
  | l2 K component contains normalized _ model =>
      rcases model with hJ | hM
      · exact ⟨K, component, contains, normalized, Or.inl hJ⟩
      · exact ⟨K, component, contains, normalized, Or.inr (Or.inl hM)⟩
  | l3 K component equality normalized model diagram =>
      exact ⟨K, component, equality ▸ le_rfl, normalized,
        Or.inr (Or.inr ⟨model, diagram⟩)⟩

set_option linter.unusedSectionVars false in
/-- Form the actual `Candidate` only after the refinement and adequate lift
have supplied the source model facts. -/
lemma candidate_of_refinement_and_lift
    {K₁ T K : Subgroup H}
    (hK : AdequateLift T K₁ K)
    (_href : Universal523Refinement K₁ T K) :
    Candidate T K := by
  rcases hK.model with hJ | hM | hL
  · exact Or.inl hJ
  · exact Or.inr (Or.inl hM)
  · exact Or.inr (Or.inr hL.2)

/-! ## The terminal assembly -/

/-- Construct the exceptional terminal component from the selected initial
residual.  The earlier source theorems are explicit premises and are not
hidden in a specialized implication. -/
theorem exists_terminal_component
    (T K₁ : Subgroup H)
    (hmod : Universal523Module K₁ T)
    (h523 : Universal523 T)
    (hnoA7 : UniformNoA7 T)
    (hrefine : ∀ {K₁ K : Subgroup H},
      Universal523NonA7 K₁ T K → Universal523Refinement K₁ T K)
    (hlift : ∀ {K₁ K : Subgroup H},
      Universal523Refinement K₁ T K → AdequateLift T K₁ K) :
    ∃ K : Subgroup H, K.IsCComponent ∧ Candidate T K ∧ K.Normal := by
  have hAlt := h523 K₁ hmod
  obtain ⟨K, hSeed⟩ := Universal523Alternative.not_a7 hnoA7 hAlt
  have href := hrefine hSeed
  have hKlift := hlift href
  refine ⟨K, hKlift.component, candidate_of_refinement_and_lift hKlift href,
    hKlift.normal⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components
