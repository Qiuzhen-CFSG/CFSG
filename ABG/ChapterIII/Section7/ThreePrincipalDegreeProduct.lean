module

public import ABG.ChapterIII.Section2.ThreePrincipalSectionData
public import BenderGlauberman.ClassFunction

/-!
# The degree product from blockwise involution-pair vanishing

Adding the order-eight generator column and its inverse cancels the three
exceptional rows. The involution values then give the reciprocal signed-degree
identity. Clearing denominators and using the odd-order relation proves the
degree product, and the section-data adapter resolves the signs and constructs
the original `ThreePrincipalData`.

The two blockwise vanishing assertions are explicit hypotheses. Their general
block-theoretic proof is independent of this calculation.
Source: ABG III.7 equations (1)--(4), article pp.101--102.
-/

namespace ABG.ThreePrincipalSectionData
open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction BenderGlauberman
noncomputable section

variable {G : Type*} [Group G] [Finite G] {x : G} (c : ThreePrincipalSectionData G x)

/-- The principal-block part of the involution-pair character sum. -/
@[expose] public def pairSum (g : G) : ℂ :=
  ∑ i ∈ c.blockData.block,
    c.blockData.chi i (ConjClasses.mk x)^2 * c.blockData.chi i (ConjClasses.mk g) /
      c.blockData.chi i (ConjClasses.mk 1)

private theorem root_two_add_neg_two : c.root ^ (2 : ℤ) + c.root ^ (-2 : ℤ) = 0 := by
  have h4 : c.root ^ (4 : ℕ) = -1 :=
    (c.root_primitive.pow (by decide) (by decide : 8 = 4 * 2)).eq_neg_one_of_two_right
  have hn : c.root ≠ 0 := c.root_primitive.ne_zero (by decide)
  norm_num [zpow_neg]
  field_simp
  linear_combination h4

/-- The inverse pair of generator columns is supported on the four odd rows. -/
public theorem generator_column_add_inverse (i : Fin 8) :
    c.blockData.chi (c.row i).val (ConjClasses.mk c.generator) +
      c.blockData.chi (c.row i).val (ConjClasses.mk c.generator⁻¹) =
        (![2, 2 * (c.sign 0 : ℂ), 2 * (c.sign 1 : ℂ),
          2 * (c.sign 2 : ℂ), 0, 0, 0, 0] i : ℂ) := by
  have h1 := c.cyclic_section 1 (by norm_num) 1 (by simp) i
  have hn1 := c.cyclic_section (-1) (by norm_num) 1 (by simp) i
  simp only [OneMemClass.coe_one, mul_one, zpow_one, zpow_neg_one] at h1 hn1
  rw [h1, hn1]
  have h2 := c.root_two_add_neg_two
  fin_cases i <;> norm_num [threeSignedPrincipalCyclicSection, zpow_neg] at *
  · ring
  · ring
  · ring
  · simp only [← inv_pow] at h2
    linear_combination 2 * (c.sign 0 : ℂ) * h2
  · ring
  · ring

/-- Squaring removes the unresolved signs from the involution column. -/
public theorem involution_value_sq (i : Fin 8) :
    c.blockData.chi (c.row i).val (ConjClasses.mk x)^2 =
      (![1, 9, 9, 1, 16, 4, 4, 4] i : ℂ) := by
  have h := c.involution_section 1 (by simp) i
  simp only [OneMemClass.coe_one, mul_one, c.local_degree] at h
  rw [h]
  have hs (j : Fin 3) : (c.sign j : ℂ)^2 = 1 := by
    rcases c.sign_unit j with hj | hj <;> simp [hj]
  fin_cases i <;> norm_num [threeSignedPrincipalInvolutionSection, mul_pow, hs]

/-- An exceptional row distinguishes the generator from its inverse. -/
public theorem generator_not_isConj_inverse : ¬ IsConj c.generator c.generator⁻¹ := by
  intro hc
  have h := congrArg (c.blockData.chi (c.row 6).val)
    (ConjClasses.mk_eq_mk_iff_isConj.mpr hc)
  have h1 := c.cyclic_section 1 (by norm_num) 1 (by simp) 6
  have hm := c.cyclic_section (-1) (by norm_num) 1 (by simp) 6
  simp only [OneMemClass.coe_one, mul_one, zpow_one, zpow_neg_one] at h1 hm
  rw [h1, hm] at h
  change (c.sign 0 : ℂ) * (c.root ^ (1 : ℤ) + (-c.root) ^ (-1 : ℤ)) =
    (c.sign 0 : ℂ) * (c.root ^ (-1 : ℤ) + (-c.root) ^ (1 : ℤ)) at h
  norm_num [zpow_neg] at h
  have he : c.root = c.root⁻¹ := by
    rcases c.sign_unit 0 with hs | hs <;> norm_num [hs] at h
    · linear_combination h / 2
    · linear_combination h / 2
  have hn := c.root_primitive.ne_zero (by decide)
  have hsq : c.root ^ 2 = 1 := by
    calc
      c.root ^ 2 = c.root * c.root := pow_two _
      _ = c.root * c.root⁻¹ := congrArg (c.root * ·) he
      _ = 1 := mul_inv_cancel₀ hn
  exact c.root_primitive.pow_ne_one_of_pos_of_lt (by decide) (by decide : 2 < 8) hsq

private theorem degree_ne_zero (i : Fin 5) : (c.degree i : ℂ) ≠ 0 := by
  let j : Fin 8 := ⟨i.val + 1, by omega⟩
  have hirr := c.blockData.complete.1 (c.row j).val
  obtain ⟨n, ρ, hρ⟩ := hirr.1
  have hi : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one ρ).mpr (by simpa [hρ] using hirr.2)
  have hn := irreducible_char_one_ne_zero (show IsIrreducibleCharacter ρ.character from
    ⟨n, ρ, hi, rfl⟩)
  have he := c.degree_value j
  rw [hρ] at he
  change ρ.character 1 = _ at he
  rw [he] at hn
  fin_cases i <;> exact hn

/-- The two blockwise zero sums give the reciprocal signed-degree relation. -/
public theorem reciprocal_identity_of_pairSum_zero
    (hp : c.pairSum c.generator = 0) (hm : c.pairSum c.generator⁻¹ = 0) :
    1 + 9 * (c.sign 0 : ℂ) / (c.degree 0 : ℂ) +
      9 * (c.sign 1 : ℂ) / (c.degree 1 : ℂ) +
      (c.sign 2 : ℂ) / (c.degree 2 : ℂ) = 0 := by
  classical
  have h : c.pairSum c.generator + c.pairSum c.generator⁻¹ = 0 := by rw [hp, hm]; ring
  simp only [pairSum] at h
  rw [← Finset.sum_add_distrib] at h
  simp_rw [← add_div, ← mul_add] at h
  rw [← Finset.sum_coe_sort, ← c.row.sum_comp] at h
  simp only [c.generator_column_add_inverse, c.involution_value_sq, c.degree_value] at h
  norm_num [Fin.sum_univ_succ] at h
  linear_combination h / 2

/-- The blockwise vanishing inputs imply the signed degree product. -/
public theorem degree_product_of_pairSum_zero
    (hp : c.pairSum c.generator = 0) (hm : c.pairSum c.generator⁻¹ = 0) :
    c.signedDegree 0 * c.signedDegree 1 = 9 * c.signedDegree 2 := by
  apply c.signedDegree_product_of_pairing
  have h := c.reciprocal_identity_of_pairSum_zero hp hm
  have h0 := c.degree_ne_zero 0
  have h1 := c.degree_ne_zero 1
  have h2 := c.degree_ne_zero 2
  field_simp at h
  have hp : (c.signedDegree 0 : ℂ) * c.signedDegree 1 * c.signedDegree 2 +
      9 * c.signedDegree 1 * c.signedDegree 2 +
      9 * c.signedDegree 0 * c.signedDegree 2 + c.signedDegree 0 * c.signedDegree 1 = 0 := by
    rcases c.sign_unit 0 with hs0 | hs0 <;> rcases c.sign_unit 1 with hs1 | hs1 <;>
      rcases c.sign_unit 2 with hs2 | hs2
    all_goals simp only [hs0, hs1, hs2, Int.cast_one, Int.cast_neg, mul_one, mul_neg] at h
    all_goals simp only [signedDegree, hs0, hs1, hs2, one_mul, neg_one_mul,
      Int.cast_neg, Int.cast_natCast]
    all_goals simp only [show (0 : Fin 3).castSucc.castSucc = (0 : Fin 5) from rfl,
      show (1 : Fin 3).castSucc.castSucc = (1 : Fin 5) from rfl,
      show (2 : Fin 3).castSucc.castSucc = (2 : Fin 5) from rfl]
    all_goals first | linear_combination h | linear_combination -h
  exact_mod_cast hp

/-- The original principal-block package follows from sections and the two zero sums. -/
public def toPrincipalDataOfPairSumZero
    (hp : c.pairSum c.generator = 0) (hm : c.pairSum c.generator⁻¹ = 0) :
    ThreePrincipalData G x :=
  c.toPrincipalData (c.degree_product_of_pairSum_zero hp hm)

/-- A blockwise vanishing theorem for nonreal elements of order eight supplies
both sums; the section formulas themselves establish nonreality. -/
public def toPrincipalDataOfNonrealVanishing
    (hvan : ∀ g : G, orderOf g = 8 → ¬ IsConj g g⁻¹ → c.pairSum g = 0) :
    ThreePrincipalData G x := by
  apply c.toPrincipalDataOfPairSumZero
  · exact hvan c.generator c.generator_order c.generator_not_isConj_inverse
  · apply hvan c.generator⁻¹
    · simpa using c.generator_order
    · intro h
      apply c.generator_not_isConj_inverse
      simpa using h.symm

end
end ABG.ThreePrincipalSectionData
