module

public import Theory.Representation.SL2FourProjectiveRecognition.Coordinates
public import Theory.Representation.SL2FourProjectiveRecognition.Field
public import Theory.Representation.SL2FourProjectiveRecognition.Generators

/-!
# Natural SL₂(4) modules from complementary root spaces

The upper-root coefficients define the four-element field on the first
root space. A basis over this field identifies the two complementary
root spaces with natural planes. The actual upper matrices and Weyl matrix
intertwine these coordinates, so their generation theorem proves
intertwining for every element of the original SL₂(4).

Source: Aschbacher–Smith, G.1.3 and G.1.7, printed pp.327–329.
-/

@[expose] public noncomputable section
namespace Representation.SL2FourNatural.ProjectiveRecognition
universe u
variable {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
variable {σ : Representation (ZMod 2) SL M} {A : Submodule (ZMod 2) M}

theorem coefficient_coordinates (h : RootPair σ weyl A)
    {s : ℕ} (e : A ≃ₗ[ZMod 2] (Fin s → F))
    (he : ∀ x i, e (coefficient h omega x) i = omega * e x i)
    (t : F) (x : A) (i : Fin s) : e (coefficient h t x) i = t * e x i := by
  have hz : coefficient h 0 = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [coefficient_val, upper_zero]
  have h1 := coefficient_one h weyl_mul_self upper_one_braid
  rcases field_cases t with rfl | rfl | rfl | rfl
  · simp [hz]
  · simp [h1]
  · exact he x i
  · rw [coefficient_add h omega 1 (upper_add _ _), h1]
    simp only [LinearMap.add_apply, Module.End.one_apply, map_add, Pi.add_apply, he,
      add_mul, one_mul]

theorem natural_coordinates [Finite M] (h : RootPair σ weyl A)
    (hdiag : ∀ x ∈ A, σ diagonalWord x ∈ A) :
    ∃ (s : ℕ) (e : M ≃ₗ[ZMod 2] (Fin s → Fin 2 → F)),
      ∀ g v i, e (σ g v) i = Matrix.mulVec g.val (e v i) := by
  have hquad : coefficient h omega * coefficient h omega = 1 + coefficient h omega :=
    coefficient_quadratic h weyl_mul_self upper_one_braid (upper_add _ _) hdiag
  obtain ⟨s, e, he⟩ := quadratic_coordinates (coefficient h omega) hquad
  let E := (pairCoordinates h).trans (pairPiCoordinates e)
  refine ⟨s, E, ?_⟩
  change ∀ g v i, E (σ g v) i = action g (E v i)
  intro g
  apply upper_weyl_induction (fun a => ∀ v i, E (σ a v) i = action a (E v i)) ?_ ?_ ?_ g
  · intro t v i
    change pairPiCoordinates e (pairCoordinates h (σ (upper t) v)) i =
      action (upper t) (pairPiCoordinates e (pairCoordinates h v) i)
    rw [pairCoordinates_upper, pairPiCoordinates_apply, pairPiCoordinates_apply, upper_action]
    funext j
    fin_cases j
    · simp [coefficient_coordinates h e he]
    · rfl
  · intro v i
    change pairPiCoordinates e (pairCoordinates h (σ weyl v)) i =
      specialLinearNatural 2 weyl (pairPiCoordinates e (pairCoordinates h v) i)
    rw [pairCoordinates_weyl h weyl_mul_self, pairPiCoordinates_apply,
      pairPiCoordinates_apply, weyl_action]
    rfl
  · intro a b ha hb v i
    rw [map_mul, Module.End.mul_apply, ha, hb, map_mul, LinearEquiv.mul_apply]

end Representation.SL2FourNatural.ProjectiveRecognition
