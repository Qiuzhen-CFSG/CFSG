module

public import Theory.Character.ModularBlock.SectionOrthogonality
public import Theory.Character.InvolutionSectionVanishing

/-!
# Blockwise involution-pair vanishing at nonreal two-elements

The product of two involutions is inverted by either factor. Its two-part
is a power of that product, so an involution class product vanishes throughout
the two-section of a nonreal two-element.

Project the class-pair counting function onto the principal block. Interchanging
the finite sums expresses this projection using the block's two-column kernel.
Two-section column orthogonality makes the projection vanish at the nonreal
two-element. The scalar-product formula for the class-pair count
then gives the precise degree-denominator identity, with no star on its values.

The modular input comes from `SectionOrthogonality`: the integral principal
selector and the odd-order twisted permutation trace prove kernel support on
two-sections. The intermediate lemmas expose the separation step explicitly.
Source: Alperin--Brauer--Gorenstein, Chapter III, Section 7, equation (1),
article p.101, citing Brauer [6, II, Proposition 4].
-/

public section
noncomputable section
namespace ModularBlock.InvolutionPairVanishing

open scoped BigOperators
open Theory.Character ModularBlock.PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

private theorem projection_zero_of_kernel (d : PrincipalCongruenceBlockData G)
    (f : ClassFunction G) (u : G)
    (h : ∀ g : G, f g ≠ 0 →
      ∑ i ∈ d.block, star (d.chi i (ConjClasses.mk g)) *
        d.chi i (ConjClasses.mk u) = 0) :
    ∑ i ∈ d.block, scalarProduct G f (ofConjClassFunction (d.chi i)) *
      d.chi i (ConjClasses.mk u) = 0 := by
  simp only [scalarProduct, ofConjClassFunction_apply]
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro g _
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  by_cases hg : f g = 0
  · rw [hg, zero_mul]
  · rw [h g hg, mul_zero]

/-- A zero block column kernel on the support of the pair count forces the
involution-weighted block sum to vanish. The scalar-product calculation also
removes the complex conjugation from the involution values and the degrees. -/
theorem principalBlock_pairSum_eq_zero_of_column_support
    (d : PrincipalCongruenceBlockData G) (x u : G)
    (hx : x * x = 1)
    (h : ∀ g : G,
      classSumPairCountMul (ConjClasses.mk x) (ConjClasses.mk x) g ≠ 0 →
      ∑ i ∈ d.block, star (d.chi i (ConjClasses.mk g)) *
        d.chi i (ConjClasses.mk u) = 0) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk x)^2 *
      d.chi i (ConjClasses.mk u) / d.chi i (ConjClasses.mk 1) = 0 := by
  have hproj := projection_zero_of_kernel d
    (fun g => (classSumPairCountMul (ConjClasses.mk x) (ConjClasses.mk x) g : ℂ)) u
    (fun g hg => h g (by exact_mod_cast hg))
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
  have hcoeff (i : d.I) :
      scalarProduct G
        (fun g => (classSumPairCountMul (ConjClasses.mk x) (ConjClasses.mk x) g : ℂ))
        (ofConjClassFunction (d.chi i)) =
      ((Nat.card (ConjClasses.mk x).carrier : ℂ)^2 / Nat.card G) *
        (d.chi i (ConjClasses.mk x)^2 / d.chi i (ConjClasses.mk 1)) := by
    rw [scalarProduct_classSumPairCountMul_irreducible _ _ x x
      ConjClasses.mem_carrier_mk ConjClasses.mem_carrier_mk _ (d.complete.1 i)]
    simp only [star_div₀, star_mul, star_conjChar_apply_inv (d.complete.1 i).1,
      hinv, inv_one]
    simp only [pow_two]
  simp_rw [hcoeff, mul_assoc] at hproj
  rw [← Finset.mul_sum] at hproj
  let : Nonempty (ConjClasses.mk x).carrier := ⟨⟨x, ConjClasses.mem_carrier_mk⟩⟩
  have hc : (Nat.card (ConjClasses.mk x).carrier : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := (ConjClasses.mk x).carrier)).ne'
  have hg : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hs := (mul_eq_zero.mp hproj).resolve_left (div_ne_zero (pow_ne_zero 2 hc) hg)
  convert hs using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- An involution-pair column vanishes at a two-element if the entire two-section
avoids products of two members of that involution class. This support form
also applies when the two-element is real. -/
theorem principalBlock_pairSum_eq_zero_of_twoSection_support
    (d : PrincipalCongruenceBlockData G) (v x : G)
    (hv : v * v = 1) (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1)
    (hsupport : ∀ y : G, Odd (orderOf y) → Commute x y →
      classSumPairCountMul (ConjClasses.mk v) (ConjClasses.mk v) (x * y) = 0) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk v)^2 *
      d.chi i (ConjClasses.mk x) / d.chi i (ConjClasses.mk 1) = 0 := by
  apply principalBlock_pairSum_eq_zero_of_column_support d v x hv
  intro g hg
  apply (show (∑ i ∈ d.block, star (d.chi i (ConjClasses.mk g)) *
      d.chi i (ConjClasses.mk x)) = _ from Finset.sum_congr rfl (fun _ _ => mul_comm _ _)).trans
  apply ModularBlock.SectionOrthogonality.principalBlock_column_eq_zero_of_not_mem_twoSection d x hx
  rintro ⟨y, hy, hxy, hc⟩
  obtain ⟨t, rfl⟩ := isConj_iff.mp hc
  have he := classSumPairCountMul_isClassFunction (ConjClasses.mk v) (ConjClasses.mk v) (x * y) t
  have hz := hsupport y hy hxy
  dsimp only at he
  rw [hz, Nat.cast_zero] at he
  exact hg (by exact_mod_cast he)

omit [Finite G] in
/-- No product of two members of an involution class lies in the two-section
of a nonreal two-element, including all conjugates of that section. -/
theorem classSumPairCount_eq_zero_of_nonreal_twoSection (x u g : G)
    (hx : x * x = 1) (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1)
    (hnonreal : ¬ IsConj u u⁻¹)
    (hsection : ∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u * v) g) :
    classSumPairCountMul (ConjClasses.mk x) (ConjClasses.mk x) g = 0 := by
  obtain ⟨v, hv, hc, hconj⟩ := hsection
  have hz := classSumPairCount_eq_zero_on_twoSection u x hu hx
    (fun t _ ht => hnonreal (isConj_iff.mpr ⟨t, ht⟩)) v hv hc
  obtain ⟨t, rfl⟩ := isConj_iff.mp hconj
  have he := classSumPairCountMul_isClassFunction
    (ConjClasses.mk x) (ConjClasses.mk x) (u * v) t
  dsimp only at he
  rw [hz, Nat.cast_zero] at he
  exact_mod_cast he

/-- Two-section column orthogonality implies the desired vanishing for every
nonreal two-element. Only orthogonality against the one specified column is needed. -/
theorem principalBlock_pairSum_eq_zero_of_twoSection_orthogonality
    (d : PrincipalCongruenceBlockData G)
    (x u : G) (hx : x * x = 1) (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1)
    (hnonreal : ¬ IsConj u u⁻¹)
    (hsep : ∀ g : G,
      (¬ ∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u * v) g) →
      ∑ i ∈ d.block, star (d.chi i (ConjClasses.mk g)) *
        d.chi i (ConjClasses.mk u) = 0) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk x)^2 *
      d.chi i (ConjClasses.mk u) / d.chi i (ConjClasses.mk 1) = 0 := by
  apply principalBlock_pairSum_eq_zero_of_column_support d x u hx
  intro g hg
  apply hsep g
  intro hsection
  exact hg (classSumPairCount_eq_zero_of_nonreal_twoSection x u g hx hu hnonreal hsection)

/-- The order-eight form used in ABG III.7, conditional only on the stated
block two-section orthogonality theorem. -/
theorem principalBlock_pairSum_eq_zero_order_eight_of_twoSection_orthogonality
    (d : PrincipalCongruenceBlockData G)
    (x u : G) (hx : orderOf x = 2) (hu : orderOf u = 8)
    (hnonreal : ¬ IsConj u u⁻¹)
    (hsep : ∀ g : G,
      (¬ ∃ v : G, Odd (orderOf v) ∧ Commute u v ∧ IsConj (u * v) g) →
      ∑ i ∈ d.block, star (d.chi i (ConjClasses.mk g)) *
        d.chi i (ConjClasses.mk u) = 0) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk x)^2 *
      d.chi i (ConjClasses.mk u) / d.chi i (ConjClasses.mk 1) = 0 := by
  apply principalBlock_pairSum_eq_zero_of_twoSection_orthogonality d x u _ _ hnonreal hsep
  · simpa only [hx, pow_two] using pow_orderOf_eq_one x
  · exact ⟨3, by simpa only [hu, show (2 : ℕ)^3 = 8 by norm_num] using
      pow_orderOf_eq_one u⟩

/-- The principal-block involution-pair sum vanishes at every nonreal two-element.
The block restriction follows from the actual two-section kernel-support theorem. -/
theorem principalBlock_pairSum_eq_zero_of_nonreal_twoElement
    (d : PrincipalCongruenceBlockData G) (x u : G)
    (hx : x * x = 1) (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1)
    (hnonreal : ¬ IsConj u u⁻¹) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk x)^2 *
      d.chi i (ConjClasses.mk u) / d.chi i (ConjClasses.mk 1) = 0 := by
  apply principalBlock_pairSum_eq_zero_of_twoSection_orthogonality d x u hx hu hnonreal
  intro g hg
  simpa only [mul_comm] using
    SectionOrthogonality.principalBlock_column_eq_zero_of_not_mem_twoSection d u hu g hg

/-- ABG III.7 equation (1) for a nonreal element of order eight in the actual
principal two-block, with the paper's character-value convention. -/
theorem principalBlock_pairSum_eq_zero_of_nonreal_order_eight
    (d : PrincipalCongruenceBlockData G) (x u : G)
    (hx : orderOf x = 2) (hu : orderOf u = 8) (hnonreal : ¬ IsConj u u⁻¹) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk x)^2 *
      d.chi i (ConjClasses.mk u) / d.chi i (ConjClasses.mk 1) = 0 := by
  apply principalBlock_pairSum_eq_zero_of_nonreal_twoElement d x u _ _ hnonreal
  · simpa only [hx, pow_two] using pow_orderOf_eq_one x
  · exact ⟨3, by simpa only [hu, show (2 : ℕ)^3 = 8 by norm_num] using
      pow_orderOf_eq_one u⟩

end ModularBlock.InvolutionPairVanishing
