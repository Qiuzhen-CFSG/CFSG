module

public import Theory.Representation.SixLetterRadicalDisplacement.RadicalGeometry
public import Theory.Representation.SixLetterRadicalDisplacement.PermutationQuotients.QuadraticKernels

/-!
# Displacements forced by a noncentral marked syntheme quotient

Let E lie in the radical D of the canonical natural plane and act quadratically
on a noncentral equivariant quotient of the fifteen-syntheme permutation
module. The finite kernel calculations exclude D₀ and every conjugate of the
coordinate four-group from E. If E has order greater than two, the subgroup
lattice of D leaves exactly the three mixed four-groups. None fixes a letter,
and their augmentation displacement is F + W; their natural displacement is
the canonical plane. This supplies the extra information absent from the
unrestricted identity, whose certified counterexample is preserved by import.

For an alternating actor, the intrinsic even radical is likewise excluded;
a quadratic subgroup inside it has order at most two. Both the ambient and
intrinsic versions retain an explicit noncentral quotient, without a
faithfulness or fixed-letter assumption.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 13.8.34, printed p.968 (PDF p.985), using
the permutation quotient and quadraticity of 13.8.4(5),(6). The source owner
must identify the marked parabolic and its two-residual, and instantiate the
quotient and noncentrality on the actual sections.
-/

public section

open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Representation.BinaryOffender
namespace Representation.SixLetterRadicalDisplacement.PermutationQuotients

/-- A quadratic subgroup on a noncentral marked quotient cannot contain the even radical. -/
theorem D0_not_le_of_quadratic {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup S) (hq : IsQuadratic σ E) : ¬ D0 ≤ E := by
  intro h
  exact not_quadratic_D0 σ f hf heq hnc (fun a ha b hb v => hq a (h ha) b (h hb) v)

/-- A quadratic subgroup contains no conjugate of the coordinate four-group. -/
theorem coordinateFour_conjugate_not_le_of_quadratic {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup S) (hq : IsQuadratic σ E) (g : S) :
    ¬ coordinateFour.map (MulAut.conj g).toMonoidHom ≤ E := by
  intro h
  exact not_quadratic_coordinateFour_conjugate σ f hf heq hnc g
    (fun a ha b hb v => hq a (h ha) b (h hb) v)

/-- The three possible radical four-groups under the actual marked quotient hypothesis. -/
theorem mixed_four_cases_of_quadratic {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup S) (hq : IsQuadratic σ E)
    (hED : E ≤ D) (hcard : 2 < Nat.card E) :
    E = Subgroup.closure {swap01 * swap23, swap45} ∨
    E = Subgroup.closure {swap01 * swap45, swap23} ∨
    E = Subgroup.closure {swap23 * swap45, swap01} := by
  apply mixed_four_cases_of_not_coordinate E hED
    (D0_not_le_of_quadratic σ f hf heq hnc E hq) hcard
  intro g he
  exact coordinateFour_conjugate_not_le_of_quadratic σ f hf heq hnc E hq g he.ge

/-- Quadraticity on the noncentral marked quotient discharges the fixed-letter obstruction. -/
theorem no_fixed_letter_of_quadratic {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup S) (hq : IsQuadratic σ E)
    (hED : E ≤ D) (hcard : 2 < Nat.card E) :
    ∀ i : Fin 6, ∃ g ∈ E, g i ≠ i := by
  apply no_fixed_letter_of_not_coordinate E hED
    (D0_not_le_of_quadratic σ f hf heq hnc E hq) hcard
  intro g he
  exact coordinateFour_conjugate_not_le_of_quadratic σ f hf heq hnc E hq g he.ge

/-- The corrected augmentation displacement, with all coordinate exclusions discharged. -/
theorem augmentation_displacement_of_quadratic {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup S) (hq : IsQuadratic σ E)
    (hED : E ≤ D) (hcard : 2 < Nat.card E) : displacement E = F ⊔ W :=
  augmentation_displacement_of_no_fixed_letter E hED
    (D0_not_le_of_quadratic σ f hf heq hnc E hq) hcard
    (no_fixed_letter_of_quadratic σ f hf heq hnc E hq hED hcard)

/-- The order and both displacement identities for a quadratic radical subgroup of order greater than two. -/
theorem radical_displacements_of_quadratic {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup S) (hq : IsQuadratic σ E)
    (hED : E ≤ D) (hcard : 2 < Nat.card E) :
    Nat.card E = 4 ∧ naturalDisplacement E = canonicalPlane ∧
      displacement E = F ⊔ W := by
  obtain ⟨hc, hn⟩ := natural_displacement E hED
    (D0_not_le_of_quadratic σ f hf heq hnc E hq) hcard
  exact ⟨hc, hn, augmentation_displacement_of_quadratic σ f hf heq hnc E hq hED hcard⟩

/-- The corrected augmentation displacement has codimension two. -/
theorem augmentation_displacement_quotient_finrank_of_quadratic {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup S) (hq : IsQuadratic σ E)
    (hED : E ≤ D) (hcard : 2 < Nat.card E) :
    Module.finrank (ZMod 2) (U ⧸ displacement E) = 2 := by
  rw [augmentation_displacement_of_quadratic σ f hf heq hnc E hq hED hcard]
  exact augmentation_quotient_finrank

/-- The alternating boundary for a quadratic subgroup acting on a noncentral S₆ quotient. -/
theorem card_le_two_of_alternating_quadratic {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) S Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rho g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup S) (hq : IsQuadratic σ E)
    (hED : E ≤ D0) : Nat.card E ≤ 2 :=
  card_le_two_of_le_D0 E hED (D0_not_le_of_quadratic σ f hf heq hnc E hq)

/-- Intrinsic noncontainment for a quadratic subgroup on a noncentral A₆ quotient. -/
theorem alternatingRadical_not_le_of_quadratic {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rhoA g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup (alternatingGroup (Fin 6)))
    (hq : IsQuadratic σ E) : ¬ alternatingRadical ≤ E := by
  intro h
  exact not_quadratic_alternatingRadical σ f hf heq hnc
    (fun a ha b hb v => hq a (h ha) b (h hb) v)

/-- The intrinsic alternating boundary, with noncontainment supplied by the marked quotient. -/
theorem alternating_card_le_two_of_quadratic {Q : Type*}
    [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) Q) (f : P →ₗ[ZMod 2] Q)
    (hf : Function.Surjective f) (heq : ∀ g v, f (rhoA g v) = σ g (f v))
    (hnc : ∃ g v, σ g v ≠ v) (E : Subgroup (alternatingGroup (Fin 6)))
    (hq : IsQuadratic σ E) (hED : E ≤ alternatingRadical) : Nat.card E ≤ 2 := by
  have hmap : E.map (alternatingGroup (Fin 6)).subtype ≤ D0 := by
    rintro _ ⟨g, hg, rfl⟩
    exact (mem_alternatingRadical g).mp (hED hg)
  have hnot : ¬ D0 ≤ E.map (alternatingGroup (Fin 6)).subtype := by
    intro h
    apply alternatingRadical_not_le_of_quadratic σ f hf heq hnc E hq
    intro g hg
    obtain ⟨x, hx, he⟩ := h ((mem_alternatingRadical g).mp hg)
    have hxy : x = g := Subtype.ext he
    exact hxy ▸ hx
  have hc := card_le_two_of_le_D0 _ hmap hnot
  rwa [Subgroup.card_map_of_injective Subtype.val_injective] at hc

end Representation.SixLetterRadicalDisplacement.PermutationQuotients
