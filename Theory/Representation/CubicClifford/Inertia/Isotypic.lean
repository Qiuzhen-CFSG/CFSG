module

public import Theory.Representation.Clifford

/-!
# Isotypic components for the inertia construction

An isotypic component is the sum of all actual subrepresentations equivalent
to a fixed constituent. Isaacs, Lemma 1.13, identifies it with the selected
summands in a finite Clifford decomposition. Distinct simple types have
disjoint components; conjugation transports components. An extension of the
constituent to an overgroup supplies the intertwiner making its component
invariant under that overgroup.

These are the isotypic ingredients for the index-two construction supporting
Aschbacher–Smith 13.8.21(1), printed p.956; no cubic multiplicity is assumed.
-/

public section

noncomputable section

open scoped MonoidAlgebra

namespace Representation.CubicClifford.Inertia

variable {F H V : Type*} [Field F] [Group H] [AddCommGroup V] [Module F V]

/-- The component of the isomorphism class of an actual subrepresentation. -/
def component (ρ : Representation F H V) (A : Subrepresentation ρ) : Subrepresentation ρ :=
  ⨆ (B : Subrepresentation ρ) (_ : Nonempty (B.toRepresentation ≃ₗ A.toRepresentation)), B

/-- An occurring subrepresentation belongs to its component. -/
lemma le_component (ρ : Representation F H V) (A : Subrepresentation ρ) : A ≤ component ρ A :=
  le_iSup₂ (f := fun B (_ : Nonempty (B.toRepresentation ≃ₗ A.toRepresentation)) => B)
    A ⟨RepEquiv.refl _⟩

lemma component_asSubmodule (ρ : Representation F H V) (A : Subrepresentation ρ) :
    (component ρ A).asSubmodule = isotypicComponent F[H] ρ.asModule A.asSubmodule := by
  let e : Subrepresentation ρ ≃o Submodule F[H] ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  change e (⨆ B, ⨆ (_ : Nonempty (B.toRepresentation ≃ₗ A.toRepresentation)), B) = _
  simp only [OrderIso.map_iSup]
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun h => ?_
    exact le_sSup ((isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv B A).mp h)
  · refine sSup_le fun B h => ?_
    exact le_iSup₂_of_le (e.symm B)
      ((isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv (e.symm B) A).mpr h)
      (by simp)

private lemma simple_asSubmodule (ρ : Representation F H V) (A : Subrepresentation ρ)
    (hA : IsIrreducible A.toRepresentation) : IsSimpleModule F[H] A.asSubmodule := by
  apply isSimpleModule_iff_isAtom.mpr
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff A).mpr
    ((Subrepresentation.irreducible_iff_isAtom A).mp hA)

/-- Components of inequivalent irreducible constituents are disjoint. -/
lemma component_disjoint (ρ : Representation F H V) (A B : Subrepresentation ρ)
    (hA : IsIrreducible A.toRepresentation) (hB : IsIrreducible B.toRepresentation)
    (hne : ¬ Nonempty (A.toRepresentation ≃ₗ B.toRepresentation)) :
    Disjoint (component ρ A) (component ρ B) := by
  let e : Subrepresentation ρ ≃o Submodule F[H] ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have := simple_asSubmodule ρ A hA
  have := simple_asSubmodule ρ B hB
  have hca : (component ρ A).asSubmodule ∈ isotypicComponents F[H] ρ.asModule :=
    ⟨A.asSubmodule, inferInstance, component_asSubmodule ρ A⟩
  have hcb : (component ρ B).asSubmodule ∈ isotypicComponents F[H] ρ.asModule :=
    ⟨B.asSubmodule, inferInstance, component_asSubmodule ρ B⟩
  have hneq : (component ρ A).asSubmodule ≠ (component ρ B).asSubmodule := by
    intro heq
    have hle : A.asSubmodule ≤ isotypicComponent F[H] ρ.asModule B.asSubmodule := by
      rw [← component_asSubmodule, ← heq]
      exact le_component ρ A
    have h := isIsotypicOfType_submodule_iff.mp
      (IsIsotypicOfType.isotypicComponent F[H] ρ.asModule B.asSubmodule) A.asSubmodule hle
    exact hne ((isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv A B).mpr h)
  have hd := (sSupIndep_isotypicComponents F[H] ρ.asModule).pairwiseDisjoint hca hcb hneq
  apply disjoint_iff.mpr
  apply e.injective
  rw [e.map_inf, e.map_bot]
  exact hd.eq_bot

lemma component_eq_of_equiv (ρ : Representation F H V) {A B : Subrepresentation ρ}
    (e : A.toRepresentation ≃ₗ B.toRepresentation) : component ρ A = component ρ B := by
  apply le_antisymm
  · exact iSup_le fun C => iSup_le fun ⟨f⟩ => le_iSup₂_of_le C ⟨f.trans e⟩ le_rfl
  · exact iSup_le fun C => iSup_le fun ⟨f⟩ => le_iSup₂_of_le C ⟨f.trans e.symm⟩ le_rfl

/-- Ambient conjugation transports the entire isotypic component. -/
lemma conjugate_component (ρ : Representation F H V) (K : Subgroup H) [K.Normal]
    (x : H) (A : Subrepresentation (ρ.comp K.subtype)) :
    conjugateSubrepresentationOrderIso ρ K x (component (ρ.comp K.subtype) A) =
      component (ρ.comp K.subtype) (conjugateSubrepresentationOrderIso ρ K x A) := by
  let c := conjugateSubrepresentationOrderIso ρ K x
  change c (component _ A) = component _ (c A)
  apply le_antisymm
  · dsimp only [component]
    rw [c.map_iSup]
    refine iSup_le fun B => ?_
    rw [c.map_iSup]
    refine iSup_le fun ⟨f⟩ => ?_
    exact le_iSup₂_of_le (c B) ⟨conjugateSubrepresentationOrderIsoRepEquiv ρ K f x⟩ le_rfl
  · refine iSup_le fun B => iSup_le fun h => ?_
    have h' : Nonempty ((c.symm B).toRepresentation ≃ₗ A.toRepresentation) := by
      apply (isaacs_6_5_nonempty_repEquiv_conjugateOrderIso_iff ρ K x (c.symm B) A).mpr
      change Nonempty ((c (c.symm B)).toRepresentation ≃ₗ (c A).toRepresentation)
      rw [c.apply_symm_apply B]
      exact h
    have hle : c.symm B ≤ component (ρ.comp K.subtype) A := le_iSup₂_of_le _ h' le_rfl
    exact c.symm_apply_le.mp hle

/-- In a finite internal sum of simple subrepresentations, a component is exactly
the sum of the summands in its isomorphism class (Isaacs, Lemma 1.13). -/
lemma component_eq_selected (ρ : Representation F H V) (A : Subrepresentation ρ)
    (hA : IsIrreducible A.toRepresentation) {n : ℕ}
    (B : Fin n → Subrepresentation ρ) (hint : DirectSum.IsInternal (fun i => (B i).asSubmodule))
    (hB : ∀ i, IsIrreducible (B i).toRepresentation) :
    component ρ A = ⨆ (i : Fin n) (_ : Nonempty ((B i).toRepresentation ≃ₗ A.toRepresentation)),
      B i := by
  classical
  let e : Subrepresentation ρ ≃o Submodule F[H] ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  apply e.injective
  change (component ρ A).asSubmodule = e _
  rw [component_asSubmodule]
  change homogeneousComponent F[H] ρ.asModule A.asSubmodule = e _
  rw [homogeneousComponent_eq_selected_sum (simple_asSubmodule ρ A hA)
    (fun i => (B i).asSubmodule) hint (fun i => simple_asSubmodule ρ (B i) (hB i))]
  simp only [OrderIso.map_iSup]
  apply le_antisymm
  · exact iSup_le fun i => le_iSup₂_of_le i.1
      ((isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv (B i.1) A).mpr i.2) le_rfl
  · exact iSup_le fun i => iSup_le fun h => le_iSup_of_le
      ⟨i, (isaacs_6_5_nonempty_repEquiv_iff_asSubmodule_linearEquiv (B i) A).mp h⟩ le_rfl

variable {E : Type*} [AddCommGroup E] [Module F E]

private def extensionConjugateEquiv (K I : Subgroup H) [K.Normal] (hKI : K ≤ I)
    (τ : Representation F I E) (x : I) :
    τ.comp (Subgroup.inclusion hKI) ≃ₗ conjugateRep (τ.comp (Subgroup.inclusion hKI)) (x : H) := by
  refine RepEquiv.mk (LinearEquiv.ofBijective (τ x) (Representation.apply_bijective τ x)) ?_
  intro k
  ext v
  change τ x (τ (Subgroup.inclusion hKI k) v) =
    τ ⟨(x : H) * (k : H) * (x : H)⁻¹, _⟩ (τ x v)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  apply Subtype.ext
  simp [mul_assoc]

/-- An extension to I makes the constituent component invariant under I. -/
lemma component_stable (ρ : Representation F H V) (K I : Subgroup H) [K.Normal]
    (hKI : K ≤ I) (τ : Representation F I E) (A : Subrepresentation (ρ.comp K.subtype))
    (eA : A.toRepresentation ≃ₗ τ.comp (Subgroup.inclusion hKI)) (x : I) :
    conjugateSubrepresentationOrderIso ρ K (x : H) (component (ρ.comp K.subtype) A) =
      component (ρ.comp K.subtype) A := by
  rw [conjugate_component]
  apply component_eq_of_equiv
  exact (conjugateSubrepresentationEquiv ρ K A (x : H)⁻¹).trans
    ((conjugateRepEquiv eA (x : H)⁻¹).trans
      ((extensionConjugateEquiv K I hKI τ x⁻¹).symm.trans eA.symm))

end Representation.CubicClifford.Inertia
