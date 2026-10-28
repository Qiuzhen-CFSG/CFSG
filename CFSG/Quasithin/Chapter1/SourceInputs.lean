module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SourceInputs
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Classification
-- Internal continuation of the ambient source proof, reusing its local SQTK deduction.
import all CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SourceInputs

/-!
# Applying the marked classifier to the original 1.1.5 configuration

The original ambient hypotheses construct the same component automorphism,
Sylow subgroup, characteristic-two fixed subgroup and odd-core inversion used
by the local classifier. The full earlier A/B/C implication supplies its
central-quotient model, and the proved local classification gives its complete
canonical action. The commutator equality and failure of containment retain
the literal ambient maps. Earlier partial reductions remain available.

Only the universal A/B/C input remains with its earlier-source assembly.
Source: Aschbacher--Smith 1.1.5, printed pp.501--503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1
open QuasisimpleInvolutions ChapterA.Section02
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The actual component application, retaining only the two outstanding
concrete source branches after inspecting the full earlier model catalogue. -/
theorem lemma_1_1_5_three_source_reduction
    (hG : IsSimpleQTKE κ G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC κ X)
    (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G)
    (h : Lemma115Hypotheses H S M z) (D : Subgroup H) (hD : IsComponent H D) :
    D.map H.subtype = ⁅D.map H.subtype, zpowers z⁆ ∧ ¬ D.map H.subtype ≤ M ∧
      (HasModelAction115 D z ∨ Nonempty (D ⧸ center D ≃* ReeF4.Model 1) ∨
        Nonempty (D ⧸ center D ≃* Held.He)) := by
  let : IsQuasisimple D := hD.2
  obtain ⟨hout, α, P, ha, d, hc⟩ := h.component_inputs D hD
  have hsqtk : IsSQTK κ D := (local_sqtk hG h.mem_H).subgroup D
  have hm : IsTheoremCModel (D ⧸ center D) :=
    quotient_model hsqtk (hABC D).1 (hABC (D ⧸ center D)).2.2
  refine ⟨hc, hout, ?_⟩
  rcases d.source_reduction hm with hmodel | hree | hheld
  · exact .inl ⟨α, ha, hmodel⟩
  · exact .inr (.inl hree)
  · exact .inr (.inr hheld)


/-- The field-eight Ree argument is discharged in the actual original
component application. Only the Held quotient remains explicit. -/
theorem lemma_1_1_5_three_source_reduction_he
    (hG : IsSimpleQTKE κ G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC κ X)
    (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G)
    (h : Lemma115Hypotheses H S M z) (D : Subgroup H) (hD : IsComponent H D) :
    D.map H.subtype = ⁅D.map H.subtype, zpowers z⁆ ∧ ¬ D.map H.subtype ≤ M ∧
      (HasModelAction115 D z ∨ Nonempty (D ⧸ center D ≃* Held.He)) := by
  let : IsQuasisimple D := hD.2
  obtain ⟨hout, α, P, ha, d, hc⟩ := h.component_inputs D hD
  have hsqtk : IsSQTK κ D := (local_sqtk hG h.mem_H).subgroup D
  have hm : IsTheoremCModel (D ⧸ center D) :=
    quotient_model hsqtk (hABC D).1 (hABC (D ⧸ center D)).2.2
  refine ⟨hc, hout, ?_⟩
  rcases d.source_reduction_he hm with hmodel | hheld
  · exact .inl ⟨α, ha, hmodel⟩
  · exact .inr hheld

/-- The complete original component clause of 1.1.5, with its local marked
classification discharged by the source theorem. -/
theorem lemma_1_1_5_three_source
    (hG : IsSimpleQTKE κ G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC κ X)
    (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G)
    (h : Lemma115Hypotheses H S M z) (D : Subgroup H) (hD : IsComponent H D) :
    D.map H.subtype = ⁅D.map H.subtype, zpowers z⁆ ∧ ¬ D.map H.subtype ≤ M ∧
      HasModelAction115 D z := by
  apply lemma_1_1_5_three_of_local_classification hG hABC
    (fun _ _ _ _ _ _ d hm => d.classify hm) H S M z h D hD

end CFSG.Quasithin.Chapter1
