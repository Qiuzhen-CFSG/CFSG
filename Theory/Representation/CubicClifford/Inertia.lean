module

public import Theory.Representation.CubicClifford.Inertia.TwoCosets
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.Algebra.Field.ZMod

/-!
# The index-two inertia block

For an irreducible representation of a finite group H, let a constituent of
its restriction to a normal subgroup K extend to a normal index-two subgroup I.
If the other coset exchanges its isomorphism class, its isotypic component is
an irreducible I-subrepresentation. Restriction back to K is the direct product
of that component and its conjugate, with a genuine intertwining equivalence.

The component is constructed by selecting the equivalent summands in Isaacs,
Theorem 6.5. The extension makes it I-invariant, distinct simple types make its
two translates disjoint, and ambient irreducibility proves block irreducibility.
The conjugate convention is `σ(gkg⁻¹)`, corresponding to the subspace `ρ(g⁻¹)C`.

This conditional construction supports the paired natural/dual factors in
Aschbacher–Smith 13.8.21(1), printed p.956. It assumes no multiplicity and does
not assert the source theorem or the subsequent cubic multiplicity calculation.
-/

public section

noncomputable section

namespace Representation.CubicClifford.Inertia

variable {F H V E : Type*} [Field F] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup E] [Module F E]

/-- Construct the irreducible I-block from a constituent extending to I whose
conjugate by the other coset is inequivalent. The two conclusions are actual
constituent occurrence and an actual K-representation product equivalence.
Only irreducibility of the constituent is needed for this construction. -/
theorem exists_block [Finite H] [FiniteDimensional F V]
    (ρ : Representation F H V) [IsIrreducible ρ]
    (K I : Subgroup H) [K.Normal] [I.Normal] (hKI : K ≤ I) (hindex : I.index = 2)
    (g : H) (hg : g ∉ I) (τ : Representation F I E)
    [IsIrreducible (τ.comp (Subgroup.inclusion hKI))]
    (A : Subrepresentation (ρ.comp K.subtype))
    (hocc : Nonempty (Representation.Equiv A.toRepresentation (τ.comp (Subgroup.inclusion hKI))))
    (hne : ¬ Nonempty (Representation.Equiv (τ.comp (Subgroup.inclusion hKI))
      (conjugateRep (τ.comp (Subgroup.inclusion hKI)) g))) :
    ∃ S : Subrepresentation (ρ.comp I.subtype), IsIrreducible S.toRepresentation ∧
      (∃ A' : Subrepresentation (S.toRepresentation.comp (Subgroup.inclusion hKI)),
        Nonempty (Representation.Equiv A'.toRepresentation (τ.comp (Subgroup.inclusion hKI)))) ∧
      Nonempty (Representation.Equiv (ρ.comp K.subtype)
        (Representation.prod (S.toRepresentation.comp (Subgroup.inclusion hKI))
          (conjugateRep (S.toRepresentation.comp (Subgroup.inclusion hKI)) g))) := by
  let eA := RepEquiv.ofRepresentationEquiv hocc.some
  have hA : IsIrreducible A.toRepresentation := eA.irreducible_of_euqiv inferInstance
  have hAatom := (Subrepresentation.irreducible_iff_isAtom A).mp hA
  obtain ⟨n, t, hint, hsimple, _, _⟩ := isaacs_theorem_6_5.{_, _, _, 0} ρ K inferInstance A hA
  let C : Subrepresentation (ρ.comp K.subtype) :=
    ⨆ (i : Fin n) (_ : Nonempty
      ((conjugateSubrepresentation ρ K A (t i)).toRepresentation ≃ₗ A.toRepresentation)),
      conjugateSubrepresentation ρ K A (t i)
  have hC : C = component (ρ.comp K.subtype) A :=
    (component_eq_selected (ρ.comp K.subtype) A hA
      (fun i => conjugateSubrepresentation ρ K A (t i)) hint hsimple).symm
  have hstable (x : I) : conjugateSubrepresentationOrderIso ρ K (x : H) C = C := by
    rw [hC]
    exact component_stable ρ K I hKI τ A eA x
  let S : Subrepresentation (ρ.comp I.subtype) := {
    toSubmodule := C.toSubmodule
    apply_mem_toSubmodule x v hv := by
      have hmem : ρ (x : H) v ∈
          (conjugateSubrepresentationOrderIso ρ K (x : H) C).toSubmodule := by
        rw [conjugateSubrepresentationOrderIso_toSubmodule]
        exact ⟨v, hv, rfl⟩
      rwa [hstable x] at hmem }
  have hAC : A ≤ C := by rw [hC]; exact le_component _ _
  have hS : S ≠ ⊥ := by
    intro hb
    apply hAatom.ne_bot
    apply le_bot_iff.mp
    have hCbot : C.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hb
    intro v hv
    have hmem : v ∈ C.toSubmodule := hAC hv
    rw [hCbot] at hmem
    exact hmem
  let D := conjugateSubrepresentationOrderIso ρ K g⁻¹ A
  have hD : IsIrreducible D.toRepresentation :=
    (Subrepresentation.irreducible_iff_isAtom D).mpr
      (((conjugateSubrepresentationOrderIso ρ K g⁻¹).isAtom_iff A).mpr hAatom)
  have hAD : ¬ Nonempty (A.toRepresentation ≃ₗ D.toRepresentation) := by
    rintro ⟨e⟩
    apply hne
    let f : D.toRepresentation ≃ₗ conjugateRep A.toRepresentation g := by
      have f : D.toRepresentation ≃ₗ conjugateRep A.toRepresentation (g⁻¹)⁻¹ :=
        conjugateSubrepresentationEquiv ρ K A (g⁻¹)⁻¹
      simpa only [inv_inv] using f
    exact ⟨(eA.symm.trans (e.trans (f.trans (conjugateRepEquiv eA g)))).toRepresentationEquiv⟩
  have hdisj : Disjoint C (conjugateSubrepresentationOrderIso ρ K g⁻¹ C) := by
    rw [hC, conjugate_component]
    exact component_disjoint (ρ.comp K.subtype) A D hA hD hAD
  have hdisj' : Disjoint C.toSubmodule (Submodule.map (ρ g⁻¹) C.toSubmodule) := by
    rw [← conjugateSubrepresentationOrderIso_toSubmodule ρ K g⁻¹ C]
    apply disjoint_iff.mpr
    exact congrArg Subrepresentation.toSubmodule hdisj.eq_bot
  have htop := pair_sup_top ρ K I hindex g hg A C hA hAC hstable
  refine ⟨S, block_irreducible ρ I hindex g hg S hS hdisj', ?_, ?_⟩
  · refine ⟨occurrence_in_larger (ρ.comp K.subtype) A C hAC, ?_⟩
    exact ⟨((occurrence_equiv (ρ.comp K.subtype) A C hAC).trans eA).toRepresentationEquiv⟩
  · exact ⟨productEquiv ρ K C g hdisj' htop⟩
end Representation.CubicClifford.Inertia

namespace Representation.CubicClifford

/-- The binary, absolutely irreducible constituent form of the index-two inertia
construction. V and E have independent universes. The occurrence is inside the
actual restriction along `Subgroup.inclusion hKI`. -/
theorem exists_index_two_inertia_block
    {H V E : Type*} [Group H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ]
    (K I : Subgroup H) [K.Normal] [I.Normal] (hKI : K ≤ I) (hindex : I.index = 2)
    (g : H) (hg : g ∉ I) (τ : Representation (ZMod 2) I E)
    [IsAbsolutelyIrreducible (τ.comp (Subgroup.inclusion hKI))]
    (A : Subrepresentation (ρ.comp K.subtype))
    (hocc : Nonempty (Representation.Equiv A.toRepresentation (τ.comp (Subgroup.inclusion hKI))))
    (hne : ¬ Nonempty (Representation.Equiv (τ.comp (Subgroup.inclusion hKI))
      (conjugateRep (τ.comp (Subgroup.inclusion hKI)) g))) :
    ∃ S : Subrepresentation (ρ.comp I.subtype), IsIrreducible S.toRepresentation ∧
      (∃ A' : Subrepresentation (S.toRepresentation.comp (Subgroup.inclusion hKI)),
        Nonempty (Representation.Equiv A'.toRepresentation (τ.comp (Subgroup.inclusion hKI)))) ∧
      Nonempty (Representation.Equiv (ρ.comp K.subtype)
        (Representation.prod (S.toRepresentation.comp (Subgroup.inclusion hKI))
          (conjugateRep (S.toRepresentation.comp (Subgroup.inclusion hKI)) g))) := by
  have := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible
    (τ.comp (Subgroup.inclusion hKI))
  exact Inertia.exists_block ρ K I hKI hindex g hg τ A hocc hne

end Representation.CubicClifford
