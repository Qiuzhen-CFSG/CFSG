module
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Bounds
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Swap
public import Theory.Representation.BinaryOffender.SectionLinear
import Mathlib.Tactic

/-!
# Natural-section bounds for an ambient actor

The section is the literal quotient W/(U∩W) of invariant subrepresentations.
A group homomorphism marks the SL₂ component action. Conjugation by an ambient
actor induces the intertwiner, so the local model estimates pass to its cyclic
subgroup and then to any overgroup containing it. No section existence or
numerical fixed-codimension estimate is assumed.

Source: GLS, vol. 2, Theorem 26.24, final paragraph. The source's natural-section
existence and automorphism classification are separate inputs to these applications.
-/

@[expose] public section
open Module
namespace Representation.BinaryOffender.NaturalTensor
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module (ZMod 2) V]

/-- Conjugation in the actual acting group gives the required intertwiner. -/
theorem actor_intertwines (ρ : Representation (ZMod 2) G V)
    (ℓ : H →* G) (a : G) (α : H → H)
    (ha : ∀ g, a * ℓ g * a⁻¹ = ℓ (α g)) :
    ∀ g v, ρ a ((ρ.comp ℓ) g v) = (ρ.comp ℓ) (α g) (ρ a v) := by
  intro g v
  change ρ a (ρ (ℓ g) v) = ρ (ℓ (α g)) (ρ a v)
  simp only [← Module.End.mul_apply, ← map_mul]
  rw [mul_inv_eq_iff_eq_mul.mp (ha g)]

variable [FiniteDimensional (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V) (U W : Subrepresentation ρ)

/-- The actor estimate on a literal invariant quotient passes to an ambient overgroup. -/
theorem literal_section_operator_le (A : Subgroup G) {a : G} (ha : a ∈ A) :
    operatorFixedCodim (sectionRepresentation ρ U W a) ≤ fixedCodim ρ A := by
  exact (operatorFixedCodim_le_fixedCodim (sectionRepresentation ρ U W) A ha).trans
    (fixedCodim_section_le ρ U W A)

variable (F : Type*) [Field F] [Algebra (ZMod 2) F] [Finite F]

/-- Inner involutions on at least two natural summands give ambient codimension 2n.
Individual summands may be mixed or permuted by the actor. -/
theorem natural_section_inner_bound [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    (ℓ : Matrix.SpecialLinearGroup (Fin 2) F →* G)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2]
      (ι → NaturalSpace F))
    (he : ∀ g v, e (sectionRepresentation ρ U W (ℓ g) v) = naturalSumAction F ι g (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r * r = 1) (hne : r ≠ 1)
    (hc : ∀ g, a * ℓ g * a⁻¹ = ℓ (r * g * r⁻¹)) :
    2 * n ≤ fixedCodim ρ A := by
  have hb := natural_sum_inner_bound F hF ((sectionRepresentation ρ U W).comp ℓ) e he
    (sectionRepresentation ρ U W a) ((sectionRepresentation ρ U W).apply_bijective a).injective
    r hr hne (actor_intertwines (sectionRepresentation ρ U W) ℓ a _ hc)
  exact (Nat.mul_le_mul_right n hι).trans (hb.trans (literal_section_operator_le ρ U W A ha))

/-- A nontrivial field twist on the preserved component gives the same estimate. -/
theorem natural_section_field_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    (ℓ : Matrix.SpecialLinearGroup (Fin 2) F →* G)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2]
      (ι → NaturalSpace F))
    (he : ∀ g v, e (sectionRepresentation ρ U W (ℓ g) v) = naturalSumAction F ι g (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F) (hσ : ∃ t, σ t ≠ t)
    (hc : ∀ g, a * ℓ g * a⁻¹ = ℓ (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹)) :
    2 * n ≤ fixedCodim ρ A := by
  have hb := natural_sum_field_bound F hF ((sectionRepresentation ρ U W).comp ℓ) e he
    (sectionRepresentation ρ U W a) r σ hσ
    (actor_intertwines (sectionRepresentation ρ U W) ℓ a _ hc)
  exact (Nat.mul_le_mul_right n hι).trans (hb.trans (literal_section_operator_le ρ U W A ha))

/-- A tensor section supplies the two natural copies required by the inner bound. -/
theorem tensor_section_inner_bound [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (ℓ : Matrix.SpecialLinearGroup (Fin 2) F →* G)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2] TensorSpace F)
    (he : ∀ g v, e (sectionRepresentation ρ U W (ℓ g) v) = tensorAction F (g, 1) (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r * r = 1) (hne : r ≠ 1)
    (hc : ∀ g, a * ℓ g * a⁻¹ = ℓ (r * g * r⁻¹)) :
    2 * n ≤ fixedCodim ρ A := by
  have hb := tensor_inner_bound F hF ((sectionRepresentation ρ U W).comp ℓ) e he
    (sectionRepresentation ρ U W a) ((sectionRepresentation ρ U W).apply_bijective a).injective
    r hr hne (actor_intertwines (sectionRepresentation ρ U W) ℓ a _ hc)
  exact hb.trans (literal_section_operator_le ρ U W A ha)

/-- Field twists on a tensor factor give the full 2n bound in the ambient module. -/
theorem tensor_section_field_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (ℓ : Matrix.SpecialLinearGroup (Fin 2) F →* G)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2] TensorSpace F)
    (he : ∀ g v, e (sectionRepresentation ρ U W (ℓ g) v) = tensorAction F (g, 1) (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F) (hσ : ∃ t, σ t ≠ t)
    (hc : ∀ g, a * ℓ g * a⁻¹ = ℓ (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹)) :
    2 * n ≤ fixedCodim ρ A := by
  have hb := tensor_field_intertwiner_bound F hF ((sectionRepresentation ρ U W).comp ℓ) e he
    (sectionRepresentation ρ U W a) r σ hσ
    (actor_intertwines (sectionRepresentation ρ U W) ℓ a _ hc)
  exact hb.trans (literal_section_operator_le ρ U W A ha)

/-- Exchanging disjoint natural summands of the section gives ambient codimension 2n. -/
theorem moved_natural_section_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (A : Subgroup G) {a : G} (ha : a ∈ A)
    (P : Submodule (ZMod 2) (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule))
    (e : NaturalSpace F ≃ₗ[ZMod 2] P)
    (hP : Disjoint P (P.map (sectionRepresentation ρ U W a))) :
    2 * n ≤ fixedCodim ρ A :=
  (moved_natural_summand_bound F hF _ P e hP).trans (literal_section_operator_le ρ U W A ha)

/-- Exchanging the two tensor factors, including inner and field twists,
forces ambient codimension at least n. -/
theorem tensor_section_swap_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (ℓ : (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) →* G)
    (e : (W.toSubmodule ⧸ (sectionLower ρ U W).toSubmodule) ≃ₗ[ZMod 2] TensorSpace F)
    (he : ∀ g v, e (sectionRepresentation ρ U W (ℓ g) v) = tensorAction F g (e v))
    (A : Subgroup G) {a : G} (ha : a ∈ A)
    (r : Matrix.SpecialLinearGroup (Fin 2) F) (σ : F →+* F)
    (hc : ∀ g, a * ℓ (1, g) * a⁻¹ = ℓ (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹, 1)) :
    n ≤ fixedCodim ρ A := by
  have ht : ∀ g v, sectionRepresentation ρ U W a
      (sectionRepresentation ρ U W (ℓ (1, g)) v) =
      sectionRepresentation ρ U W (ℓ (r * Matrix.SpecialLinearGroup.map σ g * r⁻¹, 1))
        (sectionRepresentation ρ U W a v) := by
    intro g v
    simp only [← Module.End.mul_apply, ← map_mul]
    rw [mul_inv_eq_iff_eq_mul.mp (hc g)]
  have hb := swap_bound_of_realization F hF ((sectionRepresentation ρ U W).comp ℓ)
    e he (sectionRepresentation ρ U W a) r σ ht
  exact hb.trans (literal_section_operator_le ρ U W A ha)

end Representation.BinaryOffender.NaturalTensor
