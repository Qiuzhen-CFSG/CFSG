module

public import Glauberman.SuzukiCharacterization.NormalizerCharacterAction
public import Theory.Character.Transport

/-!
# Ordinary pairing of normalizer-orbit difference characters

For a nonprincipal orbit representative `ψⱼ`, the difference
`ψⱼ - zⱼ θ` is a generalized character, vanishes at the identity, and has
normalizer self-pairing `|PK| (1 + zⱼ²)`. The proof is ordinary irreducible
orthogonality: the four terms in the expanded scalar product survive exactly
when the representative indices agree and the normalizer element lies in
`normalizerSylowCore P`.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 3.3 and equation (3.13), pp. 84–86, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

open Subgroup BenderGlauberman
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable

namespace Glauberman.SuzukiCharacterization.NormalizerCharacterOrbitData
variable {G : Type*} [Group G] [Finite G]
variable {P : Sylow 2 G} {s : CommutatorSupportData P}

omit [Finite G] in
private theorem character_nat_multiple (k : ℕ) {χ : ClassFunction P}
    (hχ : IsCharacter χ) : IsCharacter ((k : ℂ) • χ) := by
  induction k with
  | zero => simpa using (isCharacter_zero (G := P))
  | succ k ih =>
    simpa only [Nat.cast_add, Nat.cast_one, add_smul, one_smul] using
      isCharacter_add ih hχ

public theorem difference_isGeneralizedCharacter
    (o : NormalizerCharacterOrbitData P s) (j : Fin o.r) :
    IsGeneralizedCharacter (o.psi j - (o.degree j : ℂ) • s.theta) := by
  exact ⟨_, _, isCharacter_of_isIrreducibleCharacter (o.psi_irreducible j),
    character_nat_multiple _ (isCharacter_of_isIrreducibleCharacter s.linear.1), rfl⟩

public theorem difference_one (o : NormalizerCharacterOrbitData P s) (j : Fin o.r) :
    (o.psi j - (o.degree j : ℂ) • s.theta) 1 = 0 := by
  simp [o.psi_one, s.linear.2]

private theorem psi_conjugate_scalarProduct
    (o : NormalizerCharacterOrbitData P s) (h : Hypotheses P)
    (i j : Fin o.r) (n : normalizer (P : Set G)) :
    scalarProduct P (fun x => o.psi i ((P : Subgroup G).normalizerMonoidHom n x))
      (o.psi j) = if i = j ∧ n ∈ normalizerSylowCore P then 1 else 0 := by
  rw [scalarProduct_irr_ite
    (isIrreducibleCharacter_comp_mulEquiv _ (o.psi_irreducible i))
    (o.psi_irreducible j)]
  have heq : (fun x : P => o.psi i ((P : Subgroup G).normalizerMonoidHom n x)) = o.psi j ↔
      i = j ∧ n ∈ normalizerSylowCore P := o.psi_conjugate_eq_iff h i j n
  by_cases h1 : (fun h : P => o.psi i ((P : Subgroup G).normalizerMonoidHom n h)) = o.psi j
  · by_cases h2 : i = j ∧ n ∈ normalizerSylowCore P
    · rw [if_pos h2]
      split <;> rename_i hx
      · rfl
      · exact False.elim (hx h1)
    · exact False.elim (h2 (heq.mp h1))
  · by_cases h2 : i = j ∧ n ∈ normalizerSylowCore P
    · exact False.elim (h1 (heq.mpr h2))
    · rw [if_neg h2]
      split <;> rename_i hx
      · exact False.elim (h1 hx)
      · rfl

private theorem difference_conjugate_scalarProduct
    (o : NormalizerCharacterOrbitData P s) (h : Hypotheses P)
    (j : Fin o.r) (hj : j ≠ o.firstIndex) (n : normalizer (P : Set G)) :
    scalarProduct P
      (fun x => (o.psi j - (o.degree j : ℂ) • s.theta)
        ((P : Subgroup G).normalizerMonoidHom n x))
      (o.psi j - (o.degree j : ℂ) • s.theta) =
        if n ∈ normalizerSylowCore P then 1 + (o.degree j : ℂ)^2 else 0 := by
  rw [← o.psi_first]
  change scalarProduct P
    ((fun x => o.psi j ((P : Subgroup G).normalizerMonoidHom n x)) -
      (o.degree j : ℂ) • (fun x => o.psi o.firstIndex
        ((P : Subgroup G).normalizerMonoidHom n x)))
    (o.psi j - (o.degree j : ℂ) • o.psi o.firstIndex) = _
  rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right,
    scalarProduct_smul_right, scalarProduct_smul_left, scalarProduct_smul_left,
    scalarProduct_smul_right]
  simp only [o.psi_conjugate_scalarProduct h, hj, Ne.symm hj, false_and,
    if_false, true_and, star_natCast, zero_mul, mul_zero, sub_zero]
  split_ifs <;> ring

public theorem difference_normalizer_pairing
    (o : NormalizerCharacterOrbitData P s) (h : Hypotheses P)
    (j : Fin o.r) (hj : j ≠ o.firstIndex) :
    (∑ n : normalizer (P : Set G), scalarProduct P
      (fun x => (o.psi j - (o.degree j : ℂ) • s.theta)
        ((P : Subgroup G).normalizerMonoidHom n x))
      (o.psi j - (o.degree j : ℂ) • s.theta)) =
    (Nat.card (normalizerSylowCore P) : ℂ) * (1 + (o.degree j : ℂ)^2) := by
  simp_rw [o.difference_conjugate_scalarProduct h j hj]
  simp [Finset.sum_ite, Nat.card_eq_fintype_card, Fintype.card_subtype, mul_add]

end Glauberman.SuzukiCharacterization.NormalizerCharacterOrbitData
