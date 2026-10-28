module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.BinaryPolar
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.ParabolicIntertwiner
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NormalizerGeometry
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar

/-!
# Diagram-preserving symplectic automorphisms are inner-field

Over every finite field of characteristic two, an automorphism preserving the
conjugacy classes of the actual point and plane parabolics is the product of
an inner automorphism and an entrywise field automorphism.

Point-parabolic preservation constructs a projective intertwiner. Distinct
point-stabilizer suborbit sizes force it to preserve orthogonality.
`BinaryPolar` identifies binary polar permutations with symplectic matrices;
`NonbinaryPolar` reconstructs and normalizes a semilinear map in the other
cases. Faithfulness of the projective matrix action then identifies the
original group automorphism. The final theorem discharges both geometric
premises of the retained conditional assembly lemma.

Source: the automorphism fact used in Aschbacher--Smith F.1.12, printed
pp.263--264 of `refs/quasithin.pdf`, including the binary innerness assertion.
-/

public noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
variable {F : Type*} [Field F] [CharP F 2]

/-- Faithfulness makes the group automorphism determined by its intertwiner
on the actual projective point action. -/
theorem eq_of_projective_intertwining (a b : MulAut (Sp F))
    (φ : Equiv.Perm (ProjectivePoint F))
    (ha : ∀ (h : Sp F) (p : ProjectivePoint F), φ (h • p) = a h • φ p)
    (hb : ∀ (h : Sp F) (p : ProjectivePoint F), φ (h • p) = b h • φ p) :
    a = b := by
  apply MulEquiv.ext
  intro h
  apply projectiveAction_injective
  apply Equiv.ext
  intro p
  obtain ⟨q, rfl⟩ := φ.surjective p
  exact (ha h q).symm.trans (hb h q)

/-- Once the actual projective intertwiner has been identified as inner-field,
the same identification holds for the automorphism of the matrix group. -/
theorem eq_inner_field_of_projective_intertwining (a : MulAut (Sp F))
    (g : Sp F) (σ : F ≃+* F)
    (ha : ∀ (h : Sp F) (p : ProjectivePoint F),
      innerFieldProjective g σ (h • p) = a h • innerFieldProjective g σ p) :
    a = (MulAut.conj g) * fieldAutomorphism σ :=
  eq_of_projective_intertwining a _ _ ha (fun h p => innerFieldProjective_smul g h σ p)

/-- The binary geometric theorem closes the innerness argument after the
polar intertwiner has been constructed. This statement does not assume or
claim that diagram preservation has already supplied that intertwiner. -/
theorem inner_of_polar_intertwining_of_card_two (hF : Nat.card F = 2)
    (a : MulAut (Sp F)) (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q)
    (ha : ∀ (h : Sp F) (p : ProjectivePoint F), φ (h • p) = a h • φ p) :
    ∃ g : Sp F, a = MulAut.conj g := by
  obtain ⟨g, rfl⟩ := polar_permutation_eq_projectiveAction_of_card_two hF φ hφ
  refine ⟨g, eq_of_projective_intertwining a (MulAut.conj g) _ ha ?_⟩
  intro h p
  change g • (h • p) = (g * h * g⁻¹) • (g • p)
  simp only [mul_smul, inv_smul_smul]

/-- The remaining geometric inputs suffice for the required classification,
including the two-element field. The first premise concerns the actual point
action; the second is needed only for nonbinary fields. The unconditional
diagram-preserving theorem below supplies both inputs. -/
theorem inner_field_of_polar_geometry (a : MulAut (Sp F)) (ha : PreservesDiagram a)
    (horthogonal : ∀ φ : Equiv.Perm (ProjectivePoint F),
      (∀ (h : Sp F) (p : ProjectivePoint F), φ (h • p) = a h • φ p) →
      ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q)
    (hnonbinary : Nat.card F ≠ 2 → ∀ φ : Equiv.Perm (ProjectivePoint F),
      (∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q) →
      ∃ (g : Sp F) (σ : F ≃+* F), φ = innerFieldProjective g σ) :
    ∃ (g : Sp F) (σ : F ≃+* F), a = (MulAut.conj g) * fieldAutomorphism σ := by
  obtain ⟨φ, hφ⟩ := exists_projective_intertwiner a ha.1
  have ho := horthogonal φ hφ
  by_cases hF : Nat.card F = 2
  · obtain ⟨g, hg⟩ := inner_of_polar_intertwining_of_card_two hF a φ ho hφ
    refine ⟨g, RingEquiv.refl F, ?_⟩
    have hf : fieldAutomorphism (RingEquiv.refl F) = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rfl
    rw [hf, mul_one]
    exact hg
  · obtain ⟨g, σ, rfl⟩ := hnonbinary hF φ ho
    exact ⟨g, σ, eq_inner_field_of_projective_intertwining a g σ hφ⟩

/-- Every diagram-preserving automorphism of the actual symplectic four-group
over a finite field of characteristic two is inner-field, including over a
two-element field. No geometric or semilinearity premise is required. -/
theorem inner_field_of_preservesDiagram [Finite F]
    (a : MulAut (Sp F)) (ha : PreservesDiagram a) :
    ∃ (g : Sp F) (σ : F ≃+* F), a = (MulAut.conj g) * fieldAutomorphism σ :=
  inner_field_of_polar_geometry a ha
    (fun φ hφ => orthogonal_iff_of_projective_intertwining a φ hφ)
    (fun hF φ hφ => polar_permutation_eq_innerFieldProjective_of_card_ne_two hF φ hφ)

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
