module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.CommutatorImage.Rotations
/-!
# The stabilizer of the Hermitian diagonal pair

The polar form detects the two diagonal coordinates, so their pointwise
stabilizer restricts to a norm isometry of the off-diagonal plane. Dividing
that map by its value at one gives an additive map preserving both trace
and norm. Every element therefore maps to itself or its conjugate, and
additivity makes that choice uniform. Thus the stabilizer consists of
norm-plane rotations, possibly followed by conjugation.

The proof extends the trace-and-norm argument of
`Representation.OrthogonalFourMinus.HermitianEquiv.CommutatorImage.NormPlane`
to arbitrary characteristic and retains all rotations. It supplies the
stabilizer used by the full orthogonal normal form. Sources: GLS3 §2.7;
Aschbacher–Smith A.2.17, printed pp.38–39 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
open Representation.OrthogonalFourMinus
universe u
variable {E : Type u} [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)
private theorem norm_preserving_fixed_one (T : E →+ E)
    (h1 : T 1 = 1)
    (hN : ∀ z, T z * σ (T z) = z * σ z) :
    (∀ z, T z = z) ∨ (∀ z, T z = σ z) := by
  have htrace (z : E) : T z + σ (T z) = z + σ z := by
    have h := hN (z + 1)
    simp only [map_add, h1, map_one] at h
    linear_combination h - hN z
  have heither (z : E) : T z = z ∨ T z = σ z := by
    have hp : (T z - z) * (T z - σ z) = 0 := by
      linear_combination T z * htrace z - hN z
    simpa only [mul_eq_zero, sub_eq_zero] using hp
  by_cases h : ∀ z, T z = z
  · exact Or.inl h
  · push Not at h
    obtain ⟨t, ht⟩ := h
    have htt := (heither t).resolve_left ht
    right
    intro z
    rcases heither z with hz | hz
    · rcases heither (t + z) with htz | htz
      · rw [map_add, hz] at htz
        exact (ht (add_right_cancel htz)).elim
      · rw [map_add, htt, hz, map_add] at htz
        exact hz.trans (add_left_cancel htz)
    · exact hz

/-- An additive norm isometry is multiplication by a norm-one element,
possibly followed by conjugation. -/
theorem norm_isometry_normal_form (L : E →+ E)
    (hN : ∀ z, norm σ hσ (L z) = norm σ hσ z) :
    ∃ u : E, norm σ hσ u = 1 ∧
      ((∀ z, L z = u * z) ∨ (∀ z, L z = u * σ z)) := by
  have hN' (z : E) : L z * σ (L z) = z * σ z :=
    congrArg Subtype.val (hN z)
  let u := L 1
  have hu : u * σ u = 1 := by simpa [u] using hN' 1
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  let T : E →+ E :=
    { toFun := fun z => u⁻¹ * L z
      map_zero' := by simp
      map_add' := by intro x y; simp [mul_add] }
  have hT1 : T 1 = 1 := by exact inv_mul_cancel₀ hu0
  have hTN (z : E) : T z * σ (T z) = z * σ z := by
    change (u⁻¹ * L z) * σ (u⁻¹ * L z) = _
    rw [map_mul, map_inv₀]
    calc
      (u⁻¹ * L z) * ((σ u)⁻¹ * σ (L z)) =
          (u * σ u)⁻¹ * (L z * σ (L z)) := by
            rw [mul_inv]; ring
      _ = z * σ z := by rw [hu, hN']; simp
  refine ⟨u, ?_, ?_⟩
  · apply Subtype.ext
    exact hu
  · rcases norm_preserving_fixed_one σ T hT1 hTN with h | h
    · left
      intro z
      have he := congrArg (u * ·) (h z)
      simpa [T, ← mul_assoc, hu0] using he
    · right
      intro z
      have he := congrArg (u * ·) (h z)
      simpa [T, ← mul_assoc, hu0] using he

open ClassicalOrthogonal.Minus (Orthogonal)

/-- A full determinant isometry fixing the diagonal vectors restricts to a norm isometry. -/
theorem stabilizer_offDiagonal
    (g : Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ))
    (h0 : g.val (firstDiagonal σ hσ) = firstDiagonal σ hσ)
    (h1 : g.val (secondDiagonal σ hσ) = secondDiagonal σ hσ) :
    ∃ u : E, norm σ hσ u = 1 ∧
      ((∀ z, g.val (offDiagonal σ hσ z) = offDiagonal σ hσ (u * z)) ∨
        (∀ z, g.val (offDiagonal σ hσ z) = offDiagonal σ hσ (u * σ z))) := by
  have ha (z : E) : (coordinates σ hσ (g.val (offDiagonal σ hσ z))).1.1 = 0 := by
    have h := congrArg Subtype.val (polar_preserved σ hσ g (secondDiagonal σ hσ) (offDiagonal σ hσ z))
    rw [h1, coe_polar_coordinates, coe_polar_coordinates] at h
    apply Subtype.ext
    simpa [secondDiagonal] using h
  have hb (z : E) : (coordinates σ hσ (g.val (offDiagonal σ hσ z))).1.2 = 0 := by
    have h := congrArg Subtype.val (polar_preserved σ hσ g (firstDiagonal σ hσ) (offDiagonal σ hσ z))
    rw [h0, coe_polar_coordinates, coe_polar_coordinates] at h
    apply Subtype.ext
    simpa [firstDiagonal] using h
  let L : E →ₗ[fixedField σ] E :=
    { toFun := fun z => (coordinates σ hσ (g.val (offDiagonal σ hσ z))).2
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have hgL (z : E) : g.val (offDiagonal σ hσ z) = offDiagonal σ hσ (L z) := by
    apply (coordinates σ hσ).injective
    rw [coordinates_offDiagonal]
    exact Prod.ext (Prod.ext (ha z) (hb z)) rfl
  have hN (z : E) : norm σ hσ (L z) = norm σ hσ z := by
    have h := form_preserved_of_orthogonal σ hσ g (offDiagonal σ hσ z)
    rw [hgL] at h
    change form σ hσ ((coordinates σ hσ).symm ((0, 0), L z)) =
      form σ hσ ((coordinates σ hσ).symm ((0, 0), z)) at h
    rw [form_coordinates, form_coordinates] at h
    simpa only [zero_mul, zero_sub, neg_inj] using h
  obtain ⟨u, hu, h | h⟩ := norm_isometry_normal_form σ hσ L.toAddMonoidHom hN
  · exact ⟨u, hu, Or.inl (fun z => (hgL z).trans (congrArg (offDiagonal σ hσ) (h z)))⟩
  · exact ⟨u, hu, Or.inr (fun z => (hgL z).trans (congrArg (offDiagonal σ hσ) (h z)))⟩


private theorem diagonal_decomposition (X : Space σ hσ) :
    X = (coordinates σ hσ X).1.1 • firstDiagonal σ hσ +
      (coordinates σ hσ X).1.2 • secondDiagonal σ hσ + offDiagonal σ hσ (coordinates σ hσ X).2 := by
  apply (coordinates σ hσ).injective
  simp [firstDiagonal, secondDiagonal, Prod.ext_iff]

/-- The pair stabilizer consists of norm-plane rotations and their products with conjugation. -/
theorem diagonal_stabilizer_normal_form
    (g : Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ))
    (h0 : g.val (firstDiagonal σ hσ) = firstDiagonal σ hσ)
    (h1 : g.val (secondDiagonal σ hσ) = secondDiagonal σ hσ) :
    ∃ (u : E) (hu : norm σ hσ u = 1), g = normRotation σ hσ u hu ∨
      g = normRotation σ hσ u hu * conjugationOrthogonal σ hσ := by
  have hcoord (f : E → E)
      (hf : ∀ z, g.val (offDiagonal σ hσ z) = offDiagonal σ hσ (f z)) (X : Space σ hσ) :
      coordinates σ hσ (g.val X) = ((coordinates σ hσ X).1, f (coordinates σ hσ X).2) := by
    calc
      coordinates σ hσ (g.val X) = coordinates σ hσ (g.val
          ((coordinates σ hσ X).1.1 • firstDiagonal σ hσ +
            (coordinates σ hσ X).1.2 • secondDiagonal σ hσ +
              offDiagonal σ hσ (coordinates σ hσ X).2)) :=
        congrArg (fun Y => coordinates σ hσ (g.val Y)) (diagonal_decomposition σ hσ X)
      _ = _ := by
        simp only [map_add, map_smul, h0, h1, hf]
        simp [firstDiagonal, secondDiagonal, Prod.ext_iff]
  obtain ⟨u, hu, h | h⟩ := stabilizer_offDiagonal σ hσ g h0 h1
  · refine ⟨u, hu, Or.inl ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    apply (coordinates σ hσ).injective
    rw [coordinates_normRotation]
    exact hcoord (fun z => u * z) h X
  · refine ⟨u, hu, Or.inr ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    apply (coordinates σ hσ).injective
    change coordinates σ hσ (g.val X) =
      coordinates σ hσ ((normRotation σ hσ u hu).val ((conjugationOrthogonal σ hσ).val X))
    rw [coordinates_normRotation, coordinates_conjugation]
    exact hcoord (fun z => u * σ z) h X

end ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
