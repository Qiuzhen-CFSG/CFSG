module

public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.QuotientSections
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Twists
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Projective

/-!
# Natural tensor fixed-codimension bounds and their offender applications

The genuine SL₂(F) natural module and its tensor square over F give displacement
bounds 2n for inner and nontrivial field intertwiners, and n for factor swaps,
where |F| = 2^n. Arbitrary multiplicity mixing and compatible field/inner twists
are permitted. Natural sums, canonical PSL₂ models, invariant quotients and
surjective component model maps are covered by the re-exported modules.

The applications below derive the three final numerical contradictions of GLS,
vol. 2, Theorem 26.24, ChapterG.tex lines 1240–1248. They take an actual natural
section realization and the actual conjugation/quotient data. They do not assert
existence of the section or classify the component or its automorphisms; those
are separate obligations of the source-theorem assembly owner.
-/

@[expose] public section
namespace Representation.BinaryOffender.NaturalTensor
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (F : Type*) [Field F] [Algebra (ZMod 2) F] [Finite F]
  (ρ : Representation (ZMod 2) G V) (U W : Subrepresentation ρ)

/-- The inner case contradicts the rank bound n+1 from source Step 5. -/
theorem not_offender_of_inner_natural_section [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    (ℓ : H →* G) (q : H →* Matrix.SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ h v, e (sectionRepresentation ρ U W (ℓ h) v) = naturalSumAction F ι (q h) (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A) (α : H → H)
    (hc : ∀ h, a * ℓ h * a⁻¹ = ℓ (α h))
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r * r = 1) (hne : r ≠ 1)
    (hα : ∀ h, q (α h) = r * q h * r⁻¹)
    (hn : 1 < n) (hbudget : rank A ≤ n + 1) : ¬ IsOffender ρ A := by
  intro hA
  have hb := quotient_natural_section_inner_bound F ρ U W hF hι ℓ q hq e he A ha α hc r hr hne hα
  have ha := hA.2
  omega

/-- A field actor gives codimension at least four and excludes a rank-two offender. -/
theorem not_offender_rank_two_of_field_natural_section {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    (ℓ : H →* G) (q : H →* Matrix.SpecialLinearGroup (Fin 2) F) (hq : Function.Surjective q)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ h v, e (sectionRepresentation ρ U W (ℓ h) v) = naturalSumAction F ι (q h) (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A) (α : H → H)
    (hc : ∀ h, a * ℓ h * a⁻¹ = ℓ (α h))
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F) (hσ : ∃ t, σ t ≠ t)
    (hα : ∀ h, q (α h) = r * Matrix.SpecialLinearGroup.map σ (q h) * r⁻¹)
    (hn : 1 < n) (hbudget : rank A ≤ 2) : ¬ IsOffender ρ A := by
  intro hA
  have hb := quotient_natural_section_field_bound F ρ U W hF hι ℓ q hq e he A ha α hc r σ hσ hα
  have ha := hA.2
  omega

/-- A swapped tensor gives codimension at least two and excludes the cyclic offender. -/
theorem not_offender_rank_one_of_swapped_tensor_section {n : ℕ} (hF : Nat.card F = 2 ^ n)
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
        s * Matrix.SpecialLinearGroup.map τ (q h).1 * s⁻¹))
    (hn : 1 < n) (hbudget : rank A ≤ 1) : ¬ IsOffender ρ A := by
  intro hA
  have hb := quotient_tensor_section_swap_bound F ρ U W hF ℓ q hq e he A ha α hc r s σ τ hα
  have ha := hA.2
  omega

end Representation.BinaryOffender.NaturalTensor
