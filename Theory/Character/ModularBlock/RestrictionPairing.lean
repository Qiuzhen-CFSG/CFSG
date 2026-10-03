module

public import Theory.Character.ModularBlock.RestrictionColumn

/-!
# Restriction pairings from nonidentity principal-block column norms

Off-diagonal orthogonality reduces a pairing of integral restriction columns to
the diagonal principal-block norms on the nonidentity elements of a two-subgroup.
The weights need not be constant.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
equations (3.2)--(3.5), pp. 83--84.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace ModularBlock.RestrictionColumn
open PrincipalBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The kernel on a two-subgroup is determined by its nonidentity diagonal. -/
theorem column_inner_of_norm (d : PrincipalCongruenceBlockData G)
    (H : Subgroup G) (hH : IsPGroup 2 H) (c : H → ℕ)
    (hnorm : ∀ s : H, s ≠ 1 →
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk (s : G)) *
        star (d.chi i (ConjClasses.mk (s : G))) = (c s : ℂ))
    (s t : H) (hs : s ≠ 1) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk (s : G)) *
      star (d.chi i (ConjClasses.mk (t : G))) =
      if IsConj (s : G) (t : G) then (c s : ℂ) else 0 := by
  classical
  by_cases hst : IsConj (s : G) (t : G)
  · rw [if_pos hst, ← ConjClasses.mk_eq_mk_iff_isConj.mpr hst]
    exact hnorm s hs
  · rw [if_neg hst]
    have hp (u : H) : ∃ m : ℕ, (u : G) ^ (2 ^ m) = 1 := by
      obtain ⟨m, hm⟩ := hH.exists_pow_pow_eq_one u
      exact ⟨m, congrArg Subtype.val hm⟩
    exact TwoElementColumnOrthogonality.principalBlock_column_orthogonal
      d s t (hp s) (hp t) hst

/-- A degree-zero first column pairs through the actual diagonal norms and
ambient conjugacy classes. -/
theorem coefficient_pairing_eq_of_column_norm (d : PrincipalCongruenceBlockData G)
    (H : Subgroup G) (hH : IsPGroup 2 H) (c : H → ℕ)
    (hnorm : ∀ s : H, s ≠ 1 →
      ∑ i ∈ d.block, d.chi i (ConjClasses.mk (s : G)) *
        star (d.chi i (ConjClasses.mk (s : G))) = (c s : ℂ))
    (θ η : ClassFunction H) (hθ : IsGeneralizedCharacter θ)
    (hη : IsGeneralizedCharacter η) (hzero : θ 1 = 0) :
    ∑ i ∈ d.block, (coefficient d H θ hθ i : ℂ) *
      (coefficient d H η hη i : ℂ) =
    (Nat.card H : ℂ)⁻¹ * ∑ s : H, star (θ s) *
      ((Nat.card H : ℂ)⁻¹ * ∑ t : H,
        if IsConj (s : G) (t : G) then η t * (c s : ℂ) else 0) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  rw [coefficient_pairing_eq_sum]
  apply congrArg (fun z => (Nat.card H : ℂ)⁻¹ * z)
  apply Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _)
  intro s _
  rw [coefficient_sum_eq d H η hη s]
  by_cases hs : s = 1
  · simp [hs, hzero]
  simp_rw [column_inner_of_norm d H hH c hnorm s _ hs, mul_ite, mul_zero]
  congr 3
  ext x
  simp

end ModularBlock.RestrictionColumn
