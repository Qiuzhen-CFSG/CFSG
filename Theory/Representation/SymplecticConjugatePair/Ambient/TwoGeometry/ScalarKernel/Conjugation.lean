module
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Operators
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Generators

/-!
# Conjugation on the full paired symplectic group

The checked scalar, symplectic, field and graph intertwiners extend through
products and inverses. Faithfulness of the paired representation makes the
induced automorphism unique and hence gives an actual homomorphism.
Source: Aschbacher–Smith H.7, printed pp.388–389 of `refs/quasithin.pdf`.
-/
@[expose] public section
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair.Ambient
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

lemma exists_standard_intertwiner (s : standardAmbient (F := F)) :
    ∃ α : MulAut (Sp F), ∀ x v, s.val (graphPair x v) = graphPair (α x) (s.val v) := by
  obtain ⟨s, hs⟩ := s
  induction hs using Subgroup.closure_induction with
  | mem e he =>
    rcases he with ((⟨⟨a,b⟩, rfl⟩ | ⟨x, rfl⟩) | ⟨σ, rfl⟩) | rfl
    · exact ⟨1, Normalizer.scalarPair_intertwines graphAut a b⟩
    · refine ⟨MulAut.conj x, ?_⟩
      intro y v
      change graphPair x (graphPair y v) = graphPair (x*y*x⁻¹) (graphPair x v)
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    · exact ⟨fieldAutomorphism σ, Normalizer.fieldPair_intertwines σ⟩
    · exact ⟨graphAut, graphSwap_intertwines⟩
  | one => exact ⟨1, fun _ _ => rfl⟩
  | mul e f _ _ he hf =>
    obtain ⟨α, hα⟩ := he
    obtain ⟨β, hβ⟩ := hf
    refine ⟨α*β, ?_⟩
    intro x v
    change e (f (graphPair x v)) = _
    rw [hβ, hα]
    rfl
  | inv e _ he =>
    obtain ⟨α, hα⟩ := he
    refine ⟨α⁻¹, ?_⟩
    intro x v
    apply e.injective
    change e (e.symm (graphPair x v)) = e (graphPair (α.symm x) (e.symm v))
    rw [hα, e.apply_symm_apply, α.apply_symm_apply, e.apply_symm_apply]

lemma standard_intertwiner_unique (s : standardAmbient (F := F)) (α β : MulAut (Sp F))
    (hα : ∀ x v, standardAction s (graphPair x v) = graphPair (α x) (standardAction s v))
    (hβ : ∀ x v, standardAction s (graphPair x v) = graphPair (β x) (standardAction s v)) :
    α = β := by
  apply MulEquiv.ext
  intro x
  apply binaryPair_injective graphAut
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (standardAction.apply_bijective s).2 v
  exact (hα x w).symm.trans (hβ x w)

noncomputable def standardConjugation : standardAmbient (F := F) →* MulAut (Sp F) where
  toFun s := (exists_standard_intertwiner s).choose
  map_one' := standard_intertwiner_unique 1 _ 1 (exists_standard_intertwiner 1).choose_spec
    (fun _ _ => rfl)
  map_mul' s t := standard_intertwiner_unique (s*t) _ _
    (exists_standard_intertwiner (s*t)).choose_spec (by
      intro x v
      change s.val (t.val (graphPair x v)) = _
      rw [(exists_standard_intertwiner t).choose_spec,
        (exists_standard_intertwiner s).choose_spec]
      rfl)

lemma standardConjugation_intertwines (s : standardAmbient (F := F)) (x : Sp F) (v : Space F) :
    standardAction s (graphPair x v) = graphPair (standardConjugation s x) (standardAction s v) :=
  (exists_standard_intertwiner s).choose_spec x v

@[simp] lemma standardConjugation_scalarHom (p : Fˣ × Fˣ) :
    standardConjugation (scalarHom p) = 1 :=
  standard_intertwiner_unique _ _ _ (standardConjugation_intertwines _)
    (Normalizer.scalarPair_intertwines graphAut p.1 p.2)

@[simp] lemma standardConjugation_fullHom (x : Sp F) :
    standardConjugation (fullHom x) = MulAut.conj x := by
  apply standard_intertwiner_unique _ _ _ (standardConjugation_intertwines _)
  intro y v
  change graphPair x (graphPair y v) = graphPair (x*y*x⁻¹) (graphPair x v)
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

@[simp] lemma standardConjugation_fieldHom (σ : F ≃+* F) :
    standardConjugation (fieldHom σ) = fieldAutomorphism σ :=
  standard_intertwiner_unique _ _ _ (standardConjugation_intertwines _)
    (Normalizer.fieldPair_intertwines σ)

@[simp] lemma standardConjugation_graphActor :
    standardConjugation (graphActor (F := F)) = graphAut :=
  standard_intertwiner_unique _ _ _ (standardConjugation_intertwines _)
    graphSwap_intertwines

lemma actor_mul_fullHom (s : standardAmbient (F := F)) (x : Sp F) :
    s * fullHom x = fullHom (standardConjugation s x) * s := by
  apply standardAction_injective
  apply LinearMap.ext
  intro v
  exact standardConjugation_intertwines s x v

lemma scalarHom_commute_fullHom (p : Fˣ × Fˣ) (x : Sp F) :
    Commute (scalarHom p) (fullHom x) := by
  change scalarHom p * fullHom x = fullHom x * scalarHom p
  simpa only [standardConjugation_scalarHom, MulAut.one_apply] using actor_mul_fullHom (scalarHom p) x
end SymplecticConjugatePair.Ambient
