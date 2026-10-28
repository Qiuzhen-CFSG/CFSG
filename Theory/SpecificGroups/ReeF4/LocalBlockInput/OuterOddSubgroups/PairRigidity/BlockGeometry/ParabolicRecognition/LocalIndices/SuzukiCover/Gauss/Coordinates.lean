module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.RankOne
public import BenderSuzuki.External.Huppert.XI.theorem_3_3

/-!
# Scalar data for the local Suzuki Gauss identity

Write θ = 2^m and π = 2^(m+1). The change from the GLS3 parameters (t,u)
to the standard upper-triangular Suzuki parameters is
`(θ(t), t*θ(t)+θ(u))`. Its standard norm becomes
`N(t,u) = u + t*π(t) + θ(t)*θ(u)` and vanishes exactly at (0,0).
The norm proof reuses the checked finite-field norm theorem of
Huppert--Blackburn XI.3.3 after proving this change of coordinates.

The reciprocal negative parameters are `u/π(N), t/π(N)`. Explicit positive
parameters complete the four-dimensional factorization in `FourDimensional`.
The corresponding split torus factor is the literal product of the long
coroot at π(N) and the short coroot at N, so its torus membership is immediate.
`SplitIdentity` states the remaining equality in the full Ree matrix carrier;
no four-dimensional faithfulness assertion or parabolic cover is assumed.

Source: GLS3, 2.3.4--8, Table 2.4 type V, and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`; Huppert--Blackburn III, XI.3.3,
`BenderSuzuki/External/Huppert/XI/theorem_3_3.lean`.
-/

set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
open BlockParameters.FieldRecovery
variable {m : ℕ}

theorem theta_tits (x : CoefficientField m) : theta m (titsEnd m x) = x := by
  apply CharTwo.sq_injective
  change (theta m (titsEnd m x)) ^ 2 = x ^ 2
  rw [theta_sq, titsEnd_twice]

theorem tits_theta (x : CoefficientField m) : titsEnd m (theta m x) = x := by
  apply (theta m).injective
  rw [theta_tits]

def norm (t u : CoefficientField m) : CoefficientField m :=
  u + t * titsEnd m t + theta m t * theta m u

theorem norm_eq_standard (t u : CoefficientField m) :
    norm t u =
      (theta m t) * (t * theta m t + theta m u) +
        titsEnd m (theta m t) * (theta m t)^2 +
        titsEnd m (t * theta m t + theta m u) := by
  simp only [map_add, map_mul, tits_theta, theta_sq, norm]
  have htwo : (2 : CoefficientField m) = 0 := CharP.cast_eq_zero _ 2
  rw [← theta_sq]
  linear_combination -(t * (theta m t)^2) * htwo

theorem norm_eq_zero (t u : CoefficientField m) : norm t u = 0 ↔ t = 0 ∧ u = 0 := by
  rw [norm_eq_standard]
  have h := BenderSuzuki.External.suzukiOvoidNorm_eq_zero m (titsAutomorphism m)
    (titsAutomorphism_twice m) (theta m t) (t * theta m t + theta m u)
  change (theta m t) * (t * theta m t + theta m u) +
    titsEnd m (theta m t) * (theta m t)^2 +
    titsEnd m (t * theta m t + theta m u) = 0 ↔
      theta m t = 0 ∧ t * theta m t + theta m u = 0 at h
  rw [h]
  simp only [map_eq_zero]
  constructor
  · rintro ⟨rfl, hu⟩
    simpa using hu
  · rintro ⟨rfl, rfl⟩
    simp

theorem norm_ne_zero (t u : CoefficientField m) (h : t ≠ 0 ∨ u ≠ 0) :
    norm t u ≠ 0 := by
  intro hz
  obtain ⟨ht, hu⟩ := (norm_eq_zero t u).mp hz
  exact h.elim (fun ht' => ht' ht) (fun hu' => hu' hu)

def standardPair : CoefficientField m × CoefficientField m ≃
    CoefficientField m × CoefficientField m where
  toFun p := (theta m p.1, p.1 * theta m p.1 + theta m p.2)
  invFun p := (titsEnd m p.1, titsEnd m p.2 + titsEnd m p.1 * p.1^2)
  left_inv p := by
    rcases p with ⟨t,u⟩
    dsimp only
    simp only [map_add, map_mul, tits_theta, theta_sq]
    congr 1
    simp [mul_comm, add_comm, add_left_comm, add_assoc, CharTwo.add_self_eq_zero]
  right_inv p := by
    rcases p with ⟨a,b⟩
    dsimp only
    simp only [map_add, map_mul, map_pow, theta_tits, theta_sq]
    congr 1
    rw [mul_comm (titsEnd m a) a, ← add_assoc, add_right_comm,
      CharTwo.add_self_eq_zero, zero_add]

theorem norm_shift (t u : CoefficientField m) :
    norm t (u + t * titsEnd m t) = norm t u := by
  simp only [norm, map_add, map_mul, theta_tits]
  rw [← theta_sq (t := t)]
  have htwo : (2 : CoefficientField m) = 0 := CharP.cast_eq_zero _ 2
  linear_combination (t * (theta m t)^2) * htwo

theorem tits_norm (t u : CoefficientField m) :
    titsEnd m (norm t u) = (theta m u)^2 + t^2 * (theta m t)^2 + t*u := by
  simp only [norm, map_add, map_mul, titsEnd_twice, tits_theta]
  rw [← theta_sq (t := t), ← theta_sq (t := u)]
  ring

theorem norm_reciprocal (t u : CoefficientField m) (hn : norm t u ≠ 0) :
    norm (u / titsEnd m (norm t u)) (t / titsEnd m (norm t u)) = (norm t u)⁻¹ := by
  have hM : titsEnd m (norm t u) ≠ 0 := (map_ne_zero (titsEnd m)).mpr hn
  simp only [norm, map_div₀, titsEnd_twice, theta_tits]
  change t / titsEnd m (norm t u) +
    u / titsEnd m (norm t u) * (titsEnd m u / (norm t u)^2) +
    theta m u / norm t u * (theta m t / norm t u) = (norm t u)⁻¹
  apply (mul_right_injective₀ (mul_ne_zero hM (pow_ne_zero 2 hn)))
  suffices h :
      t * (norm t u)^2 + u * titsEnd m u + theta m u * theta m t * titsEnd m (norm t u) =
        titsEnd m (norm t u) * norm t u by
    field_simp [hn, hM] at h ⊢
    linear_combination h
  rw [tits_norm, ← theta_sq (t := u)]
  unfold norm
  rw [← theta_sq (t := t)]
  have htwo : (2 : CoefficientField m) = 0 := CharP.cast_eq_zero _ 2
  linear_combination
    (t*u*theta m t*theta m u + t^2*(theta m t)^3*theta m u) * htwo

/-- Affine parameters after inversion by the middle Weyl word. -/
def negativeFirst (t u : CoefficientField m) := u / titsEnd m (norm t u)
def negativeSecond (t u : CoefficientField m) := t / titsEnd m (norm t u)
def positiveFirst (t u : CoefficientField m) :=
  (t * titsEnd m t + u) / titsEnd m (norm t u)
def positiveSecond (t u : CoefficientField m) :=
  negativeSecond t u + positiveFirst t u * titsEnd m (positiveFirst t u)

theorem theta_negativeFirst (t u : CoefficientField m) :
    theta m (negativeFirst t u) = theta m u / norm t u := by
  simp only [negativeFirst, map_div₀, theta_tits]

theorem theta_negativeSecond (t u : CoefficientField m) :
    theta m (negativeSecond t u) = theta m t / norm t u := by
  simp only [negativeSecond, map_div₀, theta_tits]

theorem theta_positiveFirst (t u : CoefficientField m) :
    theta m (positiveFirst t u) = (t * theta m t + theta m u) / norm t u := by
  simp only [positiveFirst, map_div₀, map_add, map_mul, theta_tits]
  rw [mul_comm (theta m t) t]

theorem theta_positiveSecond (t u : CoefficientField m) :
    theta m (positiveSecond t u) = theta m t / norm t u +
      (t * theta m t + theta m u) / norm t u * positiveFirst t u := by
  simp only [positiveSecond, map_add, map_mul, theta_tits,
    theta_positiveFirst, theta_negativeSecond]

theorem norm_negative (t u : CoefficientField m) (hn : norm t u ≠ 0) :
    norm (negativeFirst t u) (negativeSecond t u) = (norm t u)⁻¹ :=
  norm_reciprocal t u hn

theorem norm_positive (t u : CoefficientField m) (hn : norm t u ≠ 0) :
    norm (positiveFirst t u) (positiveSecond t u) = (norm t u)⁻¹ := by
  rw [positiveSecond, norm_shift]
  have hn' : norm t (u + t * titsEnd m t) ≠ 0 := by rwa [norm_shift]
  have h := norm_reciprocal t (u + t * titsEnd m t) hn'
  rw [norm_shift] at h
  simpa only [positiveFirst, negativeSecond, add_comm u] using h

open Parabolics Theory.AlgebraicGroup.StandardRootSystem

/-- The literal two-coroot word corresponding to the diagonal Gauss factor. -/
def torusFactor (n : (CoefficientField m)ˣ) : SplitGroup m :=
  torusWord m (typeF4SimpleRootIndex 1) (Units.map (titsEnd m).toMonoidHom n) *
    torusWord m (typeF4SimpleRootIndex 2) n

theorem torusFactor_mem (n : (CoefficientField m)ˣ) : torusFactor n ∈ splitTorus m := by
  apply (splitTorus m).mul_mem
  · exact Subgroup.subset_closure ⟨_, _, rfl⟩
  · exact Subgroup.subset_closure ⟨_, _, rfl⟩

/-- The remaining identity in the full split Ree carrier. Its four-dimensional
matrix counterpart is proved in `FourDimensional`; no faithfulness implication is assumed. -/
def SplitIdentity (m : ℕ) : Prop :=
  ∀ (t u : CoefficientField m) (hn : norm t u ≠ 0),
    Binary.FixedGeometry.simpleWord m [1,2,1,2] * suzukiWord m false t u =
      suzukiWord m false (negativeFirst t u) (negativeSecond t u) *
        torusFactor (Units.mk0 (norm t u) hn) *
          suzukiWord m true (positiveFirst t u) (positiveSecond t u)

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
end
