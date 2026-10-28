module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Transport

/-!
# Conjugation transport of the actual paired normalizer

An intertwiner of the derived representations conjugates their literal operator
images and normalizers. The resulting group equivalence intertwines evaluation,
and a transport preserving both marked summands carries summand permutation to
the new action. The supplied diagram-moving transport gives such an equivalence
without identifying the full binary symplectic group with its derived subgroup.

Source: Aschbacher–Smith H.7, printed pp.388–389, and the paired setup on
printed p.696 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair.Ambient
namespace Normalizer
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

lemma linearAction_conj_of_intertwines
    (ρ ψ : Representation (ZMod 2) G V) (α : MulAut G)
    (E : V ≃ₗ[ZMod 2] V)
    (hE : ∀ x v, E (ρ x v) = ψ (α x) (E v)) (x : G) :
    MulAut.conj E (linearAction ρ x) = linearAction ψ (α x) := by
  apply LinearEquiv.ext
  intro v
  change E (ρ x (E.symm v)) = ψ (α x) v
  rw [hE, E.apply_symm_apply]

lemma range_map_conj_of_intertwines
    (ρ ψ : Representation (ZMod 2) G V) (α : MulAut G)
    (E : V ≃ₗ[ZMod 2] V)
    (hE : ∀ x v, E (ρ x v) = ψ (α x) (E v)) :
    (linearAction ρ).range.map (MulAut.conj E).toMonoidHom = (linearAction ψ).range := by
  ext f
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨α x, (linearAction_conj_of_intertwines ρ ψ α E hE x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨linearAction ρ (α.symm x), ⟨_, rfl⟩, ?_⟩
    change MulAut.conj E (linearAction ρ (α.symm x)) = _
    rw [linearAction_conj_of_intertwines ρ ψ α E hE, α.apply_symm_apply]

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

lemma derivedImage_map_conj (τ τ' : MulAut (Sp F))
    (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ x v, E (derivedPair τ x v) = derivedPair τ' x (E v)) :
    (derivedImage τ).map (MulAut.conj E).toMonoidHom = derivedImage τ' :=
  range_map_conj_of_intertwines _ _ (MulEquiv.refl _) E hE

lemma pairedNormalizer_map_conj (τ τ' : MulAut (Sp F))
    (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ x v, E (derivedPair τ x v) = derivedPair τ' x (E v)) :
    (pairedNormalizer τ).map (MulAut.conj E).toMonoidHom = pairedNormalizer τ' := by
  change (Subgroup.normalizer (derivedImage τ : Set (Space F ≃ₗ[ZMod 2] Space F))).map _ = _
  rw [Subgroup.map_equiv_normalizer_eq, derivedImage_map_conj τ τ' E hE]
  rfl

/-- Conjugation by the given module intertwiner on the literal normalizers. -/
noncomputable def pairedNormalizerEquiv (τ τ' : MulAut (Sp F))
    (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ x v, E (derivedPair τ x v) = derivedPair τ' x (E v)) :
    pairedNormalizer τ ≃* pairedNormalizer τ' :=
  ((MulAut.conj E).subgroupMap (pairedNormalizer τ)).trans
    (MulEquiv.subgroupCongr (pairedNormalizer_map_conj τ τ' E hE))

lemma pairedNormalizerEquiv_intertwines (τ τ' : MulAut (Sp F))
    (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ x v, E (derivedPair τ x v) = derivedPair τ' x (E v))
    (x : pairedNormalizer τ) (v : Space F) :
    E (normalizerAction τ x v) =
      normalizerAction τ' (pairedNormalizerEquiv τ τ' E hE x) (E v) := by
  change E (x.val v) = E (x.val (E.symm (E v)))
  rw [E.symm_apply_apply]

lemma permutesSummands_of_equivariant {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) G (Space F))
    (ψ : Representation (ZMod 2) H (Space F))
    (φ : G ≃* H) (E : Space F ≃ₗ[ZMod 2] Space F)
    (hE : ∀ x v, E (ρ x v) = ψ (φ x) (E v))
    (hU : ∀ v, E v ∈ firstSummand ↔ v ∈ firstSummand)
    (hW : ∀ v, E v ∈ secondSummand ↔ v ∈ secondSummand)
    (hρ : PermutesSummands ρ) : PermutesSummands ψ := by
  intro y
  obtain ⟨x, rfl⟩ := φ.surjective y
  rcases hρ x with ⟨hxU, hxW⟩ | hx
  · left
    constructor
    · intro v
      obtain ⟨w, rfl⟩ := E.surjective v
      rw [← hE, hU, hU]
      exact hxU w
    · intro v
      obtain ⟨w, rfl⟩ := E.surjective v
      rw [← hE, hW, hW]
      exact hxW w
  · right
    constructor
    · intro v hv
      obtain ⟨w, rfl⟩ := E.surjective v
      rw [← hE, hW]
      exact hx.1 w ((hU w).mp hv)
    · intro v hv
      obtain ⟨w, rfl⟩ := E.surjective v
      rw [← hE, hU]
      exact hx.2 w ((hW w).mp hv)

variable [Finite F] [CharP F 2]

/-- Every diagram-moving pair has an evaluation-compatible normalizer equivalence. -/
theorem exists_pairedNormalizer_equiv (τ : MulAut (Sp F)) (hτ : ¬ PreservesDiagram τ) :
    ∃ (E : Space F ≃ₗ[ZMod 2] Space F)
      (φ : pairedNormalizer (graphAut (F := F)) ≃* pairedNormalizer τ),
      (∀ x v, E (normalizerAction graphAut x v) = normalizerAction τ (φ x) (E v)) ∧
      (∀ v, E v ∈ firstSummand ↔ v ∈ firstSummand) ∧
      (∀ v, E v ∈ secondSummand ↔ v ∈ secondSummand) := by
  obtain ⟨E, hE, hU, hW⟩ := exists_derivedPair_equiv τ hτ
  exact ⟨E, pairedNormalizerEquiv graphAut τ E hE,
    pairedNormalizerEquiv_intertwines graphAut τ E hE, hU, hW⟩

/-- Transport the canonical summand-permutation theorem; its premise is explicit. -/
theorem permutesSummands_of_graph (τ : MulAut (Sp F)) (hτ : ¬ PreservesDiagram τ)
    (hgraph : PermutesSummands (normalizerAction (graphAut (F := F)))) :
    PermutesSummands (normalizerAction τ) := by
  obtain ⟨E, φ, hE, hU, hW⟩ := exists_pairedNormalizer_equiv τ hτ
  exact permutesSummands_of_equivariant _ _ φ E hE hU hW hgraph

end Normalizer
end SymplecticConjugatePair.Ambient
