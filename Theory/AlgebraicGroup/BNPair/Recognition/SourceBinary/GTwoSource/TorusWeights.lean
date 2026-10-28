module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.WeylCoefficient
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# The source two-parameter torus and the square field twist

Fong--Seitz II (9A), printed pp.215--216, obtains the square twist from
the two rank-one torus actions on the four-dimensional module. The helper
`twist_eq_square` formalizes the scalar comparison on two nonzero weight
lines. `SourceTorusData` then records the actual two rank-one torus maps and
proves that their product is the consumer's torus, with all six A--F weights
in the required left-conjugation convention.

The rank-one maps, their commuting Cartan complements, and the two module
weight equations remain source premises. This module only transports those
genuine inputs; it does not infer them from cardinalities or a model tag.
-/

@[expose] public noncomputable section
open Atlas.G2.RootPresentationRecognition
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
variable {K Y V : Type*} [Field K] [CharP K 2] [Group Y]
  [AddCommGroup V] [Module K V]

/-- The two distinct root lines in the four-dimensional source module
force the field twist from the scalar action of the Cartan kernel. -/
theorem twist_eq_square (σ : K ≃+* K) (H : Subgroup Y)
    (h₁ h₂ : Kˣ →* H) (ρ : H →* V ≃ₗ[K] V)
    (v w : V) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvweight : ∀ a : Kˣ, ρ ((h₁ a * h₂ (a^2))⁻¹) v =
      (σ (a : K) / (a : K)^3) • v)
    (hwweight : ∀ a : Kˣ, ρ ((h₁ a * h₂ (a^2))⁻¹) w =
      ((a : K) / σ (a : K)) • w)
    (hscalar : ∀ a : Kˣ, ∃ c : K, ∀ u : V,
      ρ ((h₁ a * h₂ (a^2))⁻¹) u = c • u) :
    ∀ a : K, σ a = a^2 := by
  intro a
  by_cases ha : a = 0
  · simp [ha]
  let a' := Units.mk0 a ha
  obtain ⟨c,hc⟩ := hscalar a'
  have he : σ a / a^3 = a / σ a := by
    exact (smul_left_injective K hv ((hvweight a').symm.trans (hc v))).trans
      (smul_left_injective K hw ((hwweight a').symm.trans (hc w))).symm
  have hs : σ a ≠ 0 := by simpa using ha
  have heq : σ a ^ 2 = (a^2)^2 := by
    field_simp at he
    linear_combination he
  exact CharTwo.sq_injective heq

/-- The literal right-conjugation weights before the twist is determined,
in the consumer's A,B,C,D,E,F order. -/
def firstWeight (σ : K ≃+* K) (a : Kˣ) : Fin 6 → K :=
  ![1, ((a : K) * σ a)⁻¹, (a : K) / σ a, σ a / (a : K),
    (a : K) * σ a, (a : K)⁻¹^2]
def secondWeight (b : Kˣ) : Fin 6 → K :=
  ![(b : K)⁻¹, b, 1, (b : K)⁻¹, (b : K)⁻¹^2, b]

structure SourceTorusData (L : PositiveRoots K Y) where
  twist : K ≃+* K
  h₁ : Kˣ →* Y
  h₂ : Kˣ →* Y
  commute : ∀ a b, Commute (h₁ a) (h₂ b)
  first : ∀ a i t, (h₁ a)⁻¹ * L.x i t * h₁ a = L.x i (firstWeight twist a i * t)
  second : ∀ b i t, (h₂ b)⁻¹ * L.x i t * h₂ b = L.x i (secondWeight b i * t)

namespace SourceTorusData
variable {L : PositiveRoots K Y} (d : SourceTorusData L)

def torus : Kˣ × Kˣ →* Y where
  toFun p := d.h₁ p.1 * d.h₂ (p.1 * p.2)
  map_one' := by simp
  map_mul' p q := by
    dsimp
    rw [show p.1*q.1*(p.2*q.2) = (p.1*p.2)*(q.1*q.2) by ac_rfl]
    rw [map_mul, map_mul]
    exact (d.commute q.1 (p.1*p.2)).mul_mul_mul_comm _ _

omit [CharP K 2] in
@[simp] theorem torus_apply (l m : Kˣ) : d.torus (l,m) = d.h₁ l * d.h₂ (l*m) := rfl

include d in
omit [CharP K 2] in
theorem torus_root (hσ : ∀ a, d.twist a = a^2) (l m : Kˣ) (i : Fin 6) (t : K) :
    d.torus (l,m) * L.x i t * (d.torus (l,m))⁻¹ =
      L.x i (BorelWeylData.weight l m i * t) := by
  have h₁ (a : Kˣ) (x : K) :
      d.h₁ a * L.x i x * (d.h₁ a)⁻¹ = L.x i (firstWeight d.twist a⁻¹ i * x) := by
    simpa only [map_inv, inv_inv] using d.first a⁻¹ i x
  have h₂ (b : Kˣ) (x : K) :
      d.h₂ b * L.x i x * (d.h₂ b)⁻¹ = L.x i (secondWeight b⁻¹ i * x) := by
    simpa only [map_inv, inv_inv] using d.second b⁻¹ i x
  rw [torus_apply, mul_inv_rev]
  have he : d.h₁ l * d.h₂ (l*m) * L.x i t * ((d.h₂ (l*m))⁻¹ * (d.h₁ l)⁻¹) =
      d.h₁ l * (d.h₂ (l*m)*L.x i t*(d.h₂ (l*m))⁻¹) * (d.h₁ l)⁻¹ := by group
  rw [he, h₂, h₁]
  congr 1
  fin_cases i <;>
    dsimp [firstWeight, secondWeight, BorelWeylData.weight] <;>
    simp only [hσ, Units.val_inv_eq_inv_val, Units.val_mul] <;> field_simp
omit [CharP K 2] in
/-- The constructed torus stays inside the original full Cartan. -/
theorem torus_range_le (H : Subgroup Y) (h₁ : d.h₁.range ≤ H) (h₂ : d.h₂.range ≤ H) :
    d.torus.range ≤ H := by
  rintro y ⟨⟨l,m⟩,rfl⟩
  exact H.mul_mem (h₁ ⟨l,rfl⟩) (h₂ ⟨l*m,rfl⟩)

/-- Scalar action on the same Cartan module forces all six consumer weights.
The two rank-one maps into H are the literal restrictions of this torus data. -/
theorem torus_root_of_scalar_action (H : Subgroup Y)
    (h₁ h₂ : Kˣ →* H) (hh₁ : ∀ a, (h₁ a : Y) = d.h₁ a)
    (hh₂ : ∀ a, (h₂ a : Y) = d.h₂ a) (ρ : H →* V ≃ₗ[K] V)
    (v w : V) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvweight : ∀ a : Kˣ, ρ ((h₁ a * h₂ (a^2))⁻¹) v =
      (d.twist (a : K) / (a : K)^3) • v)
    (hwweight : ∀ a : Kˣ, ρ ((h₁ a * h₂ (a^2))⁻¹) w =
      ((a : K) / d.twist (a : K)) • w)
    (hscalar : ∀ a : Kˣ, ∃ c : K, ∀ u : V,
      ρ ((h₁ a * h₂ (a^2))⁻¹) u = c • u) :
    d.torus.range ≤ H ∧ ∀ l m i t,
      d.torus (l,m) * L.x i t * (d.torus (l,m))⁻¹ =
        L.x i (BorelWeylData.weight l m i * t) := by
  refine ⟨d.torus_range_le H ?_ ?_, ?_⟩
  · rintro y ⟨a,rfl⟩
    rw [← hh₁]
    exact (h₁ a).property
  · rintro y ⟨a,rfl⟩
    rw [← hh₂]
    exact (h₂ a).property
  · exact d.torus_root (twist_eq_square d.twist H h₁ h₂ ρ v w hv hw hvweight hwweight hscalar)
end SourceTorusData
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
