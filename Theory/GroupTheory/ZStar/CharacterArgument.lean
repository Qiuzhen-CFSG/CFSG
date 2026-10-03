module

public import Theory.Character.ClassProducts
public import Theory.GroupTheory.ZStar.CharacterKernel

/-!
# Ordinary-character contradiction in the Z-star argument

The class-sum identities in step (VI) force the character value at the
distinguished involution to be the degree or its negative. The proper-kernel
argument excludes the positive sign for nonprincipal characters. Adding
the two weak section-orthogonality identities then cancels every
nonprincipal contribution; the principal character contributes two.
This contradicts the claimed zero sums over the complex numbers.

The imported modules supply class-product multiplication and the
proper-kernel step. This assembly retains their historical public names and
proves the final elementary algebra, including both forms of the section
orthogonality contradiction. It re-exports the shared ordinary principal
character instead of introducing a second definition.

Ported from `Submission/ZStar/CharacterArgument.lean` at historical
commit `c3503435`, formalizing steps (VI)--(VII) of Glauberman's Z-star proof.
The modular principal-block identities remain explicit hypotheses here.
-/

public section
noncomputable section
open scoped BigOperators
namespace Glauberman.ZStar.CharacterArgument
universe u v

export CharacterClassProducts (classProductCoeff classProductCoeff_spec
  classProductCoeff_weighted_sum characterRatio_mul_eq_of_classProducts_constant
  irreducibleCharacterRatio_mul_eq_of_classProducts_constant)
export ModularBlock.PrincipalBlockConstruction
  (ordinaryPrincipalCharacter ordinaryPrincipalCharacter_apply)

/-- The elementary algebra at the end of Glauberman Step (VI): the two
normalized product identities and a nonzero value at `s` force the value at
`t` to be either the degree or its negative. -/
theorem value_eq_degree_or_neg_degree_of_ratio_relations
    {a b c d : ℂ} (hd : d ≠ 0) (hb : b ≠ 0)
    (h1 : (a / d) * (b / d) = c / d)
    (h2 : (a / d) * (c / d) = b / d) :
    a = d ∨ a = -d := by
  field_simp [hd] at h1 h2
  have hsquare_mul : b * a ^ 2 = b * d ^ 2 := by
    calc
      b * a ^ 2 = a * (a * b) := by ring
      _ = a * (d * c) := by rw [h1]
      _ = d * (a * c) := by ring
      _ = d * (d * b) := by rw [h2]
      _ = b * d ^ 2 := by ring
  have hsquare : a ^ 2 = d ^ 2 := mul_left_cancel₀ hb hsquare_mul
  have hfactor : (a - d) * (a + d) = 0 := by
    calc
      (a - d) * (a + d) = a ^ 2 - d ^ 2 := by ring
      _ = 0 := by rw [hsquare, sub_self]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- The purely algebraic final contradiction in Glauberman Step (VII).

`valueS`, `valueT`, and `degree` are the values at `s`, `t`, and `1` of the
ordinary characters in a proposed principal block.  The distinguished index
`principal` is the principal character. -/
theorem false_of_principalSectionOrthogonality
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Finset I) (principal : I)
    (valueS valueT degree : I → ℂ)
    (hprincipal_mem : principal ∈ B)
    (hprincipalS : valueS principal = 1)
    (hprincipalT : valueT principal = 1)
    (hprincipalDegree : degree principal = 1)
    (hnegative : ∀ i ∈ B, i ≠ principal → valueS i ≠ 0 →
      valueT i = -degree i)
    (horthT : ∑ i ∈ B, valueS i * valueT i = 0)
    (horthOne : ∑ i ∈ B, valueS i * degree i = 0) : False := by
  let f : I → ℂ := fun i => valueS i * (valueT i + degree i)
  have hsum_zero : ∑ i ∈ B, f i = 0 := by
    calc
      (∑ i ∈ B, f i) =
          (∑ i ∈ B, valueS i * valueT i) +
            ∑ i ∈ B, valueS i * degree i := by
              simp only [f, mul_add, Finset.sum_add_distrib]
      _ = 0 := by rw [horthT, horthOne, add_zero]
  have hsum_two : ∑ i ∈ B, f i = 2 := by
    rw [Finset.sum_eq_single principal]
    · norm_num [f, hprincipalS, hprincipalT, hprincipalDegree]
    · intro i hi hne
      by_cases his : valueS i = 0
      · simp [f, his]
      · simp [f, hnegative i hi hne his]
    · exact fun hnot => (hnot hprincipal_mem).elim
  have : (2 : ℂ) = 0 := hsum_two.symm.trans hsum_zero
  norm_num at this

/-- A weaker-orthogonality variant of the final contradiction in Glauberman
Step (VII).

Here `valueS` and `valueTS` are the character values at `s` and `t * s`.
The ordinary class-sum argument makes these values negatives of one another
for every nonprincipal character.  Consequently weak block orthogonality of
each involution against the identity is enough: after adding the two sums,
only the principal character contributes, and it contributes `2`. -/
theorem false_of_principalWeakSectionOrthogonality
    {I : Type v} [Fintype I] [DecidableEq I]
    (B : Finset I) (principal : I)
    (valueS valueTS degree : I → ℂ)
    (hprincipal_mem : principal ∈ B)
    (hprincipalS : valueS principal = 1)
    (hprincipalTS : valueTS principal = 1)
    (hprincipalDegree : degree principal = 1)
    (hnegativeTS : ∀ i ∈ B, i ≠ principal → valueTS i = -valueS i)
    (horthS : ∑ i ∈ B, valueS i * degree i = 0)
    (horthTS : ∑ i ∈ B, valueTS i * degree i = 0) :
    False := by
  let f : I → ℂ := fun i => (valueS i + valueTS i) * degree i
  have hsum_zero : ∑ i ∈ B, f i = 0 := by
    calc
      (∑ i ∈ B, f i) =
          (∑ i ∈ B, valueS i * degree i) +
            ∑ i ∈ B, valueTS i * degree i := by
              simp only [f, add_mul, Finset.sum_add_distrib]
      _ = 0 := by rw [horthS, horthTS, add_zero]
  have hsum_two : ∑ i ∈ B, f i = 2 := by
    rw [Finset.sum_eq_single principal]
    · norm_num [f, hprincipalS, hprincipalTS, hprincipalDegree]
    · intro i hi hne
      simp [f, hnegativeTS i hi hne]
    · exact fun hnot => (hnot hprincipal_mem).elim
  have : (2 : ℂ) = 0 := hsum_two.symm.trans hsum_zero
  norm_num at this


end Glauberman.ZStar.CharacterArgument


