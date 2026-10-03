module

public import Theory.Character.ModularBlock.TwoElementColumnOrthogonality
public import Theory.Character.ScalarProductMultiplicity

/-!
# Integer restriction columns in the principal block

Restriction and ordinary character multiplicities give genuine integer columns
for any generalized character of a subgroup. Coefficients are zero outside the
prescribed principal block. Expanding their scalar products expresses weighted
character sums as integrals of the actual block column kernel. For a two-group
subgroup, off-diagonal orthogonality then proves vanishing whenever the support
misses the conjugacy class of the evaluation element.

Source: Brauer, *Some applications of the theory of blocks of characters of
finite groups. II* (1964), §V (5.1), Lemmas 3–4.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.RestrictionColumn
open PrincipalBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- Restriction of the prescribed ordinary character to the actual subgroup. -/
@[expose] def restriction (d : PrincipalCongruenceBlockData G) (H : Subgroup G) (i : d.I) :
    ClassFunction H := fun h => d.chi i (ConjClasses.mk (h : G))
/-- Ordinary characters remain characters upon restriction. -/
theorem restriction_isCharacter (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (i : d.I) : IsCharacter (restriction d H i) := by
  obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
  exact ⟨n, ρ.comp H.subtype, by funext h; change d.chi i (ConjClasses.mk (h : G)) = _; rw [hρ]; rfl⟩

/-- The integer restriction coefficient, extended by zero outside the block. -/
def coefficient (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ) (i : d.I) : ℤ :=
  if i ∈ d.block then
    (IsCharacter.scalarProduct_generalized_int (restriction_isCharacter d H i) hθ).choose
  else 0

/-- The actual coefficient identity on the prescribed principal block. -/
theorem coefficient_cast (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ) {i : d.I} (hi : i ∈ d.block) :
    (coefficient d H θ hθ i : ℂ) = scalarProduct H (restriction d H i) θ := by
  rw [coefficient, if_pos hi]
  exact (IsCharacter.scalarProduct_generalized_int (restriction_isCharacter d H i) hθ).choose_spec.symm

/-- A weighted coefficient sum is the finite integral of the block column kernel. -/
theorem coefficient_sum_eq (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ) (y : G) :
    ∑ i ∈ d.block, (coefficient d H θ hθ i : ℂ) * d.chi i (ConjClasses.mk y) =
    (Nat.card H : ℂ)⁻¹ * ∑ s : H, θ s *
      (∑ i ∈ d.block, d.chi i (ConjClasses.mk y) * star (d.chi i (ConjClasses.mk (s:G)))) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hc (i : d.I) (hi : i ∈ d.block) :
      (coefficient d H θ hθ i : ℂ) = scalarProduct H θ (restriction d H i) := by
    have := congrArg star (coefficient_cast d H θ hθ hi)
    simpa only [star_intCast, scalarProduct_conj] using this
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i hi, scalarProduct, mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  dsimp [restriction]
  ring

/-- Orthogonality kills a coefficient sum when the generalized character
vanishes on the ambient conjugates of the two-element in question. -/
theorem coefficient_sum_eq_zero (d : PrincipalCongruenceBlockData G) (H : Subgroup G) (hH : IsPGroup 2 H)
    (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ) (y : G)
    (hy : ∃ n : ℕ, y ^ (2^n) = 1)
    (hsupport : ∀ s : H, IsConj y (s:G) → θ s = 0) :
    ∑ i ∈ d.block, (coefficient d H θ hθ i : ℂ) * d.chi i (ConjClasses.mk y) = 0 := by
  rw [coefficient_sum_eq]
  suffices (∑ s : H, θ s * (∑ i ∈ d.block,
      d.chi i (ConjClasses.mk y) * star (d.chi i (ConjClasses.mk (s:G))))) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hys : IsConj y (s:G)
  · rw [hsupport s hys, zero_mul]
  · have hs : ∃ n : ℕ, (s:G) ^ (2^n) = 1 := by
      obtain ⟨n, hn⟩ := hH.exists_pow_pow_eq_one s
      exact ⟨n, by exact_mod_cast hn⟩
    rw [ModularBlock.TwoElementColumnOrthogonality.principalBlock_column_orthogonal d y s hy hs hys, mul_zero]

/-- Coefficients vanish off the prescribed block. -/
theorem coefficient_eq_zero_of_not_mem (d : PrincipalCongruenceBlockData G)
    (H : Subgroup G) (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ)
    {i : d.I} (hi : i ∉ d.block) : coefficient d H θ hθ i = 0 := by
  rw [coefficient, if_neg hi]

/-- The principal-row coefficient is the scalar product with the constant function one. -/
theorem coefficient_principal_cast (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ) :
    (coefficient d H θ hθ d.principal : ℂ) = scalarProduct H 1 θ := by
  rw [coefficient_cast d H θ hθ d.principal_mem]
  have h : restriction d H d.principal = 1 := by
    funext s
    change d.chi d.principal (ConjClasses.mk (s:G)) = 1
    rw [d.principal_eq]
    rfl
  rw [h]

/-- A nonprincipal irreducible minus one has principal-row coefficient `-1`. -/
theorem coefficient_principal_sub_one (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ) (ψ : ClassFunction H)
    (hψ : IsIrreducibleCharacter ψ) (hne : ψ ≠ 1) (heq : θ = ψ - 1) :
    coefficient d H θ hθ d.principal = -1 := by
  have h : (coefficient d H θ hθ d.principal : ℂ) = -1 := by
    rw [coefficient_cast d H θ hθ d.principal_mem]
    have hp : restriction d H d.principal = 1 := by
      funext s
      change d.chi d.principal (ConjClasses.mk (s:G)) = 1
      rw [d.principal_eq]
      rfl
    rw [hp, heq]
    exact hψ.scalarProduct_one_sub_one hne
  exact_mod_cast h

/-- A generalized character zero at the identity gives a degree-weighted zero sum. -/
theorem coefficient_sum_degree_eq_zero (d : PrincipalCongruenceBlockData G) (H : Subgroup G) (hH : IsPGroup 2 H)
    (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ) (hzero : θ 1 = 0) :
    ∑ i ∈ d.block, (coefficient d H θ hθ i : ℂ) * d.chi i (ConjClasses.mk 1) = 0 := by
  apply coefficient_sum_eq_zero d H hH θ hθ 1 ⟨0, by simp⟩
  intro s hs
  have hs' : s = 1 := Subtype.ext (isConj_one_right.mp hs)
  rw [hs', hzero]

/-- Vanishing on elements whose square is one gives zero weighted value at every such ambient element. -/
theorem coefficient_sum_square_one_eq_zero (d : PrincipalCongruenceBlockData G) (H : Subgroup G) (hH : IsPGroup 2 H)
    (θ : ClassFunction H) (hθ : IsGeneralizedCharacter θ)
    (hzero : ∀ s : H, s^2 = 1 → θ s = 0) (y : G) (hy : y^2 = 1) :
    ∑ i ∈ d.block, (coefficient d H θ hθ i : ℂ) * d.chi i (ConjClasses.mk y) = 0 := by
  apply coefficient_sum_eq_zero d H hH θ hθ y ⟨1, by simpa using hy⟩
  intro s hs
  apply hzero s
  have hh := hs.pow 2
  rw [hy, isConj_one_right] at hh
  exact_mod_cast hh

/-- A pairing of integer columns is a scalar product with the associated
weighted character restriction. -/
theorem coefficient_pairing_eq_sum (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (θ η : ClassFunction H) (hθ : IsGeneralizedCharacter θ) (hη : IsGeneralizedCharacter η) :
    ∑ i ∈ d.block, (coefficient d H θ hθ i : ℂ) * (coefficient d H η hη i : ℂ) =
    (Nat.card H : ℂ)⁻¹ * ∑ s : H, star (θ s) *
      (∑ i ∈ d.block, (coefficient d H η hη i : ℂ) * d.chi i (ConjClasses.mk (s:G))) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coefficient_cast d H θ hθ hi, scalarProduct, mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  dsimp [restriction]
  ring

/-- Summing a column pairing over the full ordinary family equals summing
over the block, since the constructed coefficients have zero extension. -/
theorem coefficient_pairing_eq_sum_block (d : PrincipalCongruenceBlockData G) (H : Subgroup G)
    (θ η : ClassFunction H) (hθ : IsGeneralizedCharacter θ) (hη : IsGeneralizedCharacter η) :
    ∑ i : d.I, coefficient d H θ hθ i * coefficient d H η hη i =
      ∑ i ∈ d.block, coefficient d H θ hθ i * coefficient d H η hη i := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [coefficient_eq_zero_of_not_mem d H θ hθ hi, zero_mul]

end ModularBlock.RestrictionColumn
