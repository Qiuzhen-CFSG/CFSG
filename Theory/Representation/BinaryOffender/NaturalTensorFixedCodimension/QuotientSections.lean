module
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Sections
import Mathlib.Tactic

/-!
# Bounds inflated from a component quotient

The component need not split over its center or its two-core. Its actual action
on the section factors through a surjective homomorphism to the matrix model.
An ambient conjugation compatible with this quotient gives the model intertwiner.
The resulting estimates use the literal section quotient and the ambient actor.

Source: GLS, vol. 2, Theorem 26.24, final paragraph; the model quotient and
section realization are supplied by Theorem 25.14, not constructed here.
-/
@[expose] public section
open Module
namespace Representation.BinaryOffender.NaturalTensor
variable {G H J V M : Type*} [Group G] [Group H] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup M] [Module (ZMod 2) M]

/-- Descend the actual actor through a surjective model quotient, without a splitting. -/
theorem quotient_actor_intertwines (ρ : Representation (ZMod 2) G V)
    (ℓ : H →* G) (q : H →* J) (hq : Function.Surjective q)
    (σ : Representation (ZMod 2) J M) (e : V ≃ₗ[ZMod 2] M)
    (he : ∀ h v, e (ρ (ℓ h) v) = σ (q h) (e v))
    (a : G) (α : H → H) (β : J → J)
    (ha : ∀ h, a * ℓ h * a⁻¹ = ℓ (α h)) (hβ : ∀ h, q (α h) = β (q h)) :
    ∀ j v, e.conj (ρ a) (σ j v) = σ (β j) (e.conj (ρ a) v) := by
  intro j v
  obtain ⟨h, rfl⟩ := hq j
  have hs : e.symm (σ (q h) v) = ρ (ℓ h) (e.symm v) := by
    apply e.injective
    simp [he]
  have hc : ρ a (ρ (ℓ h) (e.symm v)) = ρ (ℓ (α h)) (ρ a (e.symm v)) :=
    actor_intertwines ρ ℓ a α ha h (e.symm v)
  simp only [LinearEquiv.conj_apply_apply, hs, hc, he, hβ]

variable (F : Type*) [Field F] [Algebra (ZMod 2) F]

/-- Scalar restriction of the literal sum of natural matrix representations. -/
def binaryNaturalSumAction (ι : Type*) :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) (ι → NaturalSpace F) where
  toFun g := (naturalSumAction F ι g).restrictScalars (ZMod 2)
  map_one' := by ext v i j; simp
  map_mul' g h := by ext v i j; simp

variable [Finite F] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (U W : Subrepresentation ρ)

/-- Inner bound through an arbitrary surjective component quotient. -/
theorem quotient_natural_section_inner_bound [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    (ℓ : H →* G) (q : H →* Matrix.SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ h v, e (sectionRepresentation ρ U W (ℓ h) v) = naturalSumAction F ι (q h) (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A) (α : H → H)
    (hc : ∀ h, a * ℓ h * a⁻¹ = ℓ (α h))
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r * r = 1) (hne : r ≠ 1)
    (hα : ∀ h, q (α h) = r * q h * r⁻¹) :
    2 * n ≤ fixedCodim ρ A := by
  let T := sectionRepresentation ρ U W a
  have hi := quotient_actor_intertwines (sectionRepresentation ρ U W) ℓ q hq
    (binaryNaturalSumAction F ι) e he a α (fun g => r * g * r⁻¹) hc hα
  have hb := natural_sum_inner_bound F hF (binaryNaturalSumAction F ι)
    (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl) (e.conj T)
    (e.injective.comp (((sectionRepresentation ρ U W).apply_bijective a).injective.comp
      e.symm.injective)) r hr hne hi
  have hd := operatorFixedCodim_eq_of_equiv T (e.conj T) e (by simp)
  have ht := literal_section_operator_le ρ U W A ha
  have hm := Nat.mul_le_mul_right n hι
  dsimp only [T] at *
  omega

/-- Inner-field bound through the same quotient, with arbitrary summand mixing. -/
theorem quotient_natural_section_field_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    (ℓ : H →* G) (q : H →* Matrix.SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ h v, e (sectionRepresentation ρ U W (ℓ h) v) = naturalSumAction F ι (q h) (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A) (α : H → H)
    (hc : ∀ h, a * ℓ h * a⁻¹ = ℓ (α h))
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F) (hσ : ∃ t, σ t ≠ t)
    (hα : ∀ h, q (α h) = r * Matrix.SpecialLinearGroup.map σ (q h) * r⁻¹) :
    2 * n ≤ fixedCodim ρ A := by
  let T := sectionRepresentation ρ U W a
  have hi := quotient_actor_intertwines (sectionRepresentation ρ U W) ℓ q hq
    (binaryNaturalSumAction F ι) e he a α
    (fun g => r * Matrix.SpecialLinearGroup.map σ g * r⁻¹) hc hα
  have hb := natural_sum_field_bound F hF (binaryNaturalSumAction F ι)
    (LinearEquiv.refl (ZMod 2) _) (fun _ _ => rfl) (e.conj T) r σ hσ hi
  have hd := operatorFixedCodim_eq_of_equiv T (e.conj T) e (by simp)
  have ht := literal_section_operator_le ρ U W A ha
  have hm := Nat.mul_le_mul_right n hι
  dsimp only [T] at *
  omega

/-- A swapped tensor quotient gives the ambient rank-one exclusion bound. -/
theorem quotient_tensor_section_swap_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (ℓ : H →* G)
    (q : H →* (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F))
    (hq : Function.Surjective q)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2] TensorSpace F)
    (he : ∀ h v, e (sectionRepresentation ρ U W (ℓ h) v) = tensorAction F (q h) (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A) (α : H → H)
    (hc : ∀ h, a * ℓ h * a⁻¹ = ℓ (α h))
    (r s : Matrix.SpecialLinearGroup (Fin 2) F) (σ τ : F →+* F)
    (hα : ∀ h, q (α h) =
      (r * Matrix.SpecialLinearGroup.map σ (q h).2 * r⁻¹,
        s * Matrix.SpecialLinearGroup.map τ (q h).1 * s⁻¹)) :
    n ≤ fixedCodim ρ A := by
  let : FiniteDimensional (ZMod 2) (TensorSpace F) := Module.Finite.trans F (TensorSpace F)
  let T := sectionRepresentation ρ U W a
  have hi := quotient_actor_intertwines (sectionRepresentation ρ U W) ℓ q hq
    (binaryTensorAction F) e he a α
    (fun g => (r * Matrix.SpecialLinearGroup.map σ g.2 * r⁻¹,
      s * Matrix.SpecialLinearGroup.map τ g.1 * s⁻¹)) hc hα
  have hi' : ∀ g v, e.conj T (tensorAction F (1, g) v) =
      tensorAction F (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹, 1) (e.conj T v) := by
    intro g v
    simpa [T, binaryTensorAction] using hi (1, g) v
  have hb := swap_inner_field_bound F hF (e.conj T) r σ hi'
  have hd := operatorFixedCodim_eq_of_equiv T (e.conj T) e (by simp)
  have ht := literal_section_operator_le ρ U W A ha
  dsimp only [T] at *
  omega
end Representation.BinaryOffender.NaturalTensor
