module

public import ABG.ChapterIII.Section2.ThreePrincipalData

/-!
# The principal-block section data before resolving signs

This is the characteristic-three specialization of the section calculations
in ABG III.5--6. It retains the actual principal block, the compatible local
degree-three character, the two-singular restrictions, and the odd-order
relations, with the three odd-degree signs still unresolved. The congruences
are for signed degrees. No degree product or numerical table is a field.

The interface separates the section construction from the blockwise
involution-pair argument in III.7. It is an input interface, not an existence
assertion. Source: ABG III.2 Propositions 1--4, Proposition 6 (6), and
Corollary 2; proved in III.5--6, especially III.6 Corollaries 3--6.
-/

namespace ABG
open ModularBlock.PrincipalBlockConstruction ModularBlock.CompatibleBrauerBlock
noncomputable section

/-- The involution section with `ε = -1` and unresolved odd-degree signs. -/
@[expose] public def threeSignedPrincipalInvolutionSection (δ : Fin 3 → ℤ)
    (v : ℂ) : Fin 8 → ℂ :=
  ![1, -(δ 0 : ℂ) * v, (δ 1 : ℂ) * v, -(δ 2 : ℂ),
    -(δ 1 : ℂ) * (v + 1), (δ 0 : ℂ) * (1 - v),
    (δ 0 : ℂ) * (v - 1), (δ 0 : ℂ) * (v - 1)]

/-- The cyclic sections before the signs are resolved. -/
@[expose] public def threeSignedPrincipalCyclicSection (δ : Fin 3 → ℤ)
    (ζ : ℂ) (h : ℤ) : Fin 8 → ℂ :=
  ![1, (δ 0 : ℂ), -(δ 1 : ℂ) * (-1)^h, -(δ 2 : ℂ) * (-1)^h, 0,
    (δ 0 : ℂ) * (ζ^(2*h) + (-ζ)^(-(2*h))),
    (δ 0 : ℂ) * (ζ^h + (-ζ)^(-h)),
    (δ 0 : ℂ) * (ζ^(-h) + (-ζ)^h)]

/-- Actual principal-block section data without the III.7 degree product. -/
public structure ThreePrincipalSectionData (G : Type*) [Group G] [Finite G] (x : G) where
  blockData : PrincipalCongruenceBlockData G
  row : Fin 8 ≃ {i : blockData.I // i ∈ blockData.block}
  principal : (row 0).val = blockData.principal
  degree : Fin 5 → ℕ
  degree_value : ∀ i : Fin 8, blockData.chi (row i).val (ConjClasses.mk 1) =
    ((![1, degree 0, degree 1, degree 2, degree 3,
      degree 4, degree 4, degree 4] i : ℕ) : ℂ)
  sign : Fin 3 → ℤ
  sign_unit : ∀ i, sign i = 1 ∨ sign i = -1
  rational : ∀ (i : Fin 5) (g : G), ∃ q : ℚ,
    blockData.chi (row ⟨i.val, by omega⟩).val (ConjClasses.mk g) = (q : ℂ)
  localRow : (localData blockData (Subgroup.centralizer ({x} : Set G))).I
  local_mem : localRow ∈ (localData blockData (Subgroup.centralizer ({x} : Set G))).block
  local_degree :
    (localData blockData (Subgroup.centralizer ({x} : Set G))).chi localRow
      (ConjClasses.mk 1) = 3
  involution_section : ∀ (r : Subgroup.centralizer ({x} : Set G)),
    Odd (orderOf r) → ∀ i : Fin 8,
      blockData.chi (row i).val (ConjClasses.mk (x * (r : G))) =
        threeSignedPrincipalInvolutionSection sign
          ((localData blockData (Subgroup.centralizer ({x} : Set G))).chi localRow
            (ConjClasses.mk r)) i
  generator : G
  generator_order : orderOf generator = 8
  generator_four : generator ^ 4 = x
  root : ℂ
  root_primitive : IsPrimitiveRoot root 8
  cyclic_section : ∀ (h : ℤ), ¬ 4 ∣ h →
    ∀ (r : Subgroup.centralizer ({generator ^ h} : Set G)), Odd (orderOf r) →
      ∀ i : Fin 8,
        blockData.chi (row i).val (ConjClasses.mk (generator ^ h * (r : G))) =
          threeSignedPrincipalCyclicSection sign root h i
  odd_relations : ∀ (r : G), Odd (orderOf r) →
    1 + (sign 0 : ℂ) * blockData.chi (row 1).val (ConjClasses.mk r) +
      (sign 1 : ℂ) * blockData.chi (row 2).val (ConjClasses.mk r) +
      (sign 2 : ℂ) * blockData.chi (row 3).val (ConjClasses.mk r) = 0
  odd_fourth : ∀ (r : G), Odd (orderOf r) →
    blockData.chi (row 4).val (ConjClasses.mk r) =
      blockData.chi (row 2).val (ConjClasses.mk r) + (sign 1 : ℂ)
  odd_exceptional : ∀ (r : G), Odd (orderOf r) → ∀ j : Fin 3,
    blockData.chi (row ⟨j.val + 5, by omega⟩).val (ConjClasses.mk r) =
      blockData.chi (row 1).val (ConjClasses.mk r) + (sign 0 : ℂ)
  degree_first_congruence : 16 ∣ sign 0 * (degree 0 : ℤ) - 5
  degree_second_congruence : 16 ∣ sign 1 * (degree 1 : ℤ) - 3

namespace ThreePrincipalSectionData
variable {G : Type*} [Group G] [Finite G] {x : G} (c : ThreePrincipalSectionData G x)

/-- The signed odd degrees, retaining their actual character witnesses. -/
@[expose] public def signedDegree (i : Fin 3) : ℤ := c.sign i * (c.degree i.castSucc.castSucc : ℤ)

/-- Evaluation of the odd-order relation at the identity. -/
public theorem signedDegree_sum :
    1 + c.signedDegree 0 + c.signedDegree 1 + c.signedDegree 2 = 0 := by
  have h := c.odd_relations 1 (by simp)
  simp only [c.degree_value, Matrix.cons_val] at h
  exact_mod_cast h

/-- The blockwise pairing polynomial is the sole extra degree input needed. -/
public theorem signedDegree_product_of_pairing
    (hpair : c.signedDegree 0 * c.signedDegree 1 * c.signedDegree 2 +
      9 * c.signedDegree 1 * c.signedDegree 2 +
      9 * c.signedDegree 0 * c.signedDegree 2 + c.signedDegree 0 * c.signedDegree 1 = 0) :
    c.signedDegree 0 * c.signedDegree 1 = 9 * c.signedDegree 2 :=
  three_principal_product_of_pairing _ _ _ c.signedDegree_sum
    c.degree_first_congruence c.degree_second_congruence hpair

/-- The III.7 product and the section congruences force the two signed degree lists. -/
public theorem signedDegree_alternatives
    (hprod : c.signedDegree 0 * c.signedDegree 1 = 9 * c.signedDegree 2) :
    (c.signedDegree 0 = -11 ∧ c.signedDegree 1 = -45 ∧ c.signedDegree 2 = 55) ∨
      (c.signedDegree 0 = -27 ∧ c.signedDegree 1 = -13 ∧ c.signedDegree 2 = 39) :=
  three_principal_signed_degrees _ _ _ c.signedDegree_sum hprod
    c.degree_first_congruence c.degree_second_congruence

/-- Nonnegative actual degrees resolve the three odd-degree signs. -/
public theorem signs_of_product
    (hprod : c.signedDegree 0 * c.signedDegree 1 = 9 * c.signedDegree 2) :
    c.sign = ![-1, -1, 1] := by
  have hv := c.signedDegree_alternatives hprod
  have h0 : c.sign 0 = -1 := by
    rcases c.sign_unit 0 with hs | hs
    · simp only [signedDegree, hs, one_mul] at hv
      rcases hv with hv | hv <;> omega
    · exact hs
  have h1 : c.sign 1 = -1 := by
    rcases c.sign_unit 1 with hs | hs
    · simp only [signedDegree, hs, one_mul] at hv
      rcases hv with hv | hv <;> omega
    · exact hs
  have h2 : c.sign 2 = 1 := by
    rcases c.sign_unit 2 with hs | hs
    · exact hs
    · simp only [signedDegree, hs, neg_one_mul] at hv
      rcases hv with hv | hv <;> omega
  funext i
  fin_cases i <;> simp [h0, h1, h2]

/-- Assemble the original public interface after proving the degree product.
The block, row bijection, local character, generator, and root are retained. -/
public def toPrincipalData
    (hprod : c.signedDegree 0 * c.signedDegree 1 = 9 * c.signedDegree 2) :
    ThreePrincipalData G x := by
  have hs := c.signs_of_product hprod
  refine {
    blockData := c.blockData
    row := c.row
    principal := c.principal
    degree := c.degree
    degree_value := c.degree_value
    rational := c.rational
    localRow := c.localRow
    local_mem := c.local_mem
    local_degree := c.local_degree
    involution_section := ?_
    generator := c.generator
    generator_order := c.generator_order
    generator_four := c.generator_four
    root := c.root
    root_primitive := c.root_primitive
    cyclic_section := ?_
    odd_relations := ?_
    odd_fourth := ?_
    odd_exceptional := ?_
    degree_product := ?_
    degree_first_congruence := ?_
    degree_second_congruence := ?_ }
  · intro r hr i
    rw [c.involution_section r hr i, hs]
    fin_cases i <;> simp [threeSignedPrincipalInvolutionSection, threePrincipalInvolutionSection]
  · intro h hh r hr i
    rw [c.cyclic_section h hh r hr i, hs]
    fin_cases i <;> simp [threeSignedPrincipalCyclicSection, threePrincipalCyclicSection]
  · intro r hr
    have h := c.odd_relations r hr
    simp only [hs, Matrix.cons_val, Int.cast_neg, Int.cast_one, neg_one_mul, one_mul] at h
    linear_combination h
  · intro r hr
    have h := c.odd_fourth r hr
    simp only [hs, Matrix.cons_val, Int.cast_neg, Int.cast_one] at h
    linear_combination h
  · intro r hr j
    have h := c.odd_exceptional r hr j
    simp only [hs, Matrix.cons_val, Int.cast_neg, Int.cast_one] at h
    linear_combination h
  · simp only [signedDegree, hs, Matrix.cons_val, neg_one_mul, one_mul, neg_mul_neg] at hprod
    exact_mod_cast hprod
  · have h := c.degree_first_congruence
    simp only [hs, Matrix.cons_val, neg_one_mul] at h
    omega
  · have h := c.degree_second_congruence
    simp only [hs, Matrix.cons_val, neg_one_mul] at h
    omega

end ThreePrincipalSectionData

end
end ABG
