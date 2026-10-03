module

public import Theory.Character.ModularBlock.LocalColumnNorm
public import ABG.ChapterIII.Section8.PrincipalDegreeArithmetic

/-!
# Principal-block data for a semidihedral Sylow subgroup of order sixteen

This interface retains eight actual irreducible characters in one constructed
principal two-block: the principal character, χ₁ through χ₄, and the exceptional
characters indexed by `2, 1, -1`. It includes the compatible local character ψ
of degree three and both kinds of two-singular restrictions from III.2.

The structure is an input interface, not an existence assertion. The degree
alternatives and involution values below are proved from its character
identities. Constructing this data from the local group hypotheses remains
the separate principal-block theorem.

Source: Alperin--Brauer--Gorenstein, III.2 Propositions 1--7 and Corollary 2,
article pp.67--70; the proofs are in III.5--7. The signs here are the resolved
characteristic-three signs `δ₁ = δ₂ = -1`, `δ₃ = 1`, `ε = -1`.
-/

namespace ABG
open ModularBlock.PrincipalBlockConstruction ModularBlock.CompatibleBrauerBlock
open scoped BigOperators
noncomputable section

/-- Values on the involution section, with `v = ψ(r)` for an odd-order `r`. -/
@[expose] public def threePrincipalInvolutionSection (v : ℂ) : Fin 8 → ℂ :=
  ![1, v, -v, -1, v + 1, v - 1, 1 - v, 1 - v]

/-- Values on the sections of elements of order four or eight. The last
three indices correspond to the source exceptional indices `2, 1, -1`. -/
@[expose] public def threePrincipalCyclicSection (ζ : ℂ) (h : ℤ) : Fin 8 → ℂ :=
  ![1, -1, (-1)^h, -((-1)^h), 0,
    -(ζ^(2*h) + (-ζ)^(-(2*h))),
    -(ζ^h + (-ζ)^(-h)), -(ζ^(-h) + (-ζ)^h)]

/-- Actual principal-block characters and the identities preceding the
numerical calculation. Existence is deliberately not a field or an axiom. -/
public structure ThreePrincipalData (G : Type*) [Group G] [Finite G] (x : G) where
  blockData : PrincipalCongruenceBlockData G
  row : Fin 8 ≃ {i : blockData.I // i ∈ blockData.block}
  principal : (row 0).val = blockData.principal
  degree : Fin 5 → ℕ
  degree_value : ∀ i : Fin 8, blockData.chi (row i).val (ConjClasses.mk 1) =
    ((![1, degree 0, degree 1, degree 2, degree 3,
      degree 4, degree 4, degree 4] i : ℕ) : ℂ)
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
        threePrincipalInvolutionSection
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
          threePrincipalCyclicSection root h i
  odd_relations : ∀ (r : G), Odd (orderOf r) →
    1 + blockData.chi (row 3).val (ConjClasses.mk r) =
      blockData.chi (row 1).val (ConjClasses.mk r) +
        blockData.chi (row 2).val (ConjClasses.mk r)
  odd_fourth : ∀ (r : G), Odd (orderOf r) →
    blockData.chi (row 4).val (ConjClasses.mk r) + 1 =
      blockData.chi (row 2).val (ConjClasses.mk r)
  odd_exceptional : ∀ (r : G), Odd (orderOf r) → ∀ j : Fin 3,
    blockData.chi (row ⟨j.val + 5, by omega⟩).val (ConjClasses.mk r) + 1 =
      blockData.chi (row 1).val (ConjClasses.mk r)
  degree_product : degree 0 * degree 1 = 9 * degree 2
  degree_first_congruence : degree 0 % 16 = 11
  degree_second_congruence : degree 1 % 16 = 13

namespace ThreePrincipalData
variable {G : Type*} [Group G] [Finite G] {x : G} (c : ThreePrincipalData G x)

/-- The retained characters as class functions. -/
@[expose] public def χ (i : Fin 8) : ConjClassFunction G := c.blockData.chi (c.row i).val

/-- Each row is an actual irreducible character. -/
public theorem irreducible (i : Fin 8) : IsIrreducibleConjCharacter (c.χ i) :=
  c.blockData.complete.1 _

/-- The rows are distinct as characters, not merely as labels. -/
public theorem injective : Function.Injective c.χ := by
  intro i j h
  exact c.row.injective (Subtype.ext (c.blockData.complete.2.2 h))

/-- Every retained character belongs to the actual principal congruence block. -/
public theorem mem_block (i : Fin 8) : (c.row i).val ∈ c.blockData.block := (c.row i).property

/-- The zero row is the principal character. -/
public theorem principal_eq : c.χ 0 = ordinaryPrincipalCharacter G := by
  change c.blockData.chi (c.row 0).val = _
  rw [c.principal, c.blockData.principal_eq]

/-- The degree identities follow by evaluating the odd-order restrictions at one. -/
public theorem degree_identities :
    1 + c.degree 2 = c.degree 0 + c.degree 1 ∧
      c.degree 3 + 1 = c.degree 1 ∧ c.degree 4 + 1 = c.degree 0 := by
  have ho : Odd (orderOf (1 : G)) := by simp
  have hs := c.odd_relations 1 ho
  have hfour := c.odd_fourth 1 ho
  have he := c.odd_exceptional 1 ho 0
  simp only [c.degree_value, Matrix.cons_val] at hs hfour he
  exact ⟨by exact_mod_cast hs, by exact_mod_cast hfour, by exact_mod_cast he⟩

/-- The two lists are consequences of the character identities. -/
public theorem degree_alternatives :
    (c.degree 0 = 11 ∧ c.degree 1 = 45 ∧ c.degree 2 = 55 ∧
      c.degree 3 = 44 ∧ c.degree 4 = 10) ∨
    (c.degree 0 = 27 ∧ c.degree 1 = 13 ∧ c.degree 2 = 39 ∧
      c.degree 3 = 12 ∧ c.degree 4 = 26) :=
  three_principal_degrees _ _ _ _ _ c.degree_identities.1 c.degree_product
    c.degree_first_congruence c.degree_second_congruence
    c.degree_identities.2.1 c.degree_identities.2.2

/-- Evaluation at the involution, retaining all exceptional rows as well. -/
public theorem involution_values (i : Fin 8) :
    c.χ i (ConjClasses.mk x) = (![1, 3, -3, -1, 4, 2, -2, -2] i : ℂ) := by
  have h := c.involution_section 1 (by simp) i
  simp only [OneMemClass.coe_one, mul_one, c.local_degree] at h
  change c.χ i (ConjClasses.mk x) = threePrincipalInvolutionSection 3 i at h
  rw [h]
  fin_cases i <;> norm_num [threePrincipalInvolutionSection]

/-- The eight retained rows account for the whole principal-block column. -/
public theorem involution_column_norm :
    ∑ i ∈ c.blockData.block, c.blockData.chi i (ConjClasses.mk x) *
      star (c.blockData.chi i (ConjClasses.mk x)) = 48 := by
  classical
  rw [← Finset.sum_coe_sort]
  rw [← c.row.sum_comp]
  change ∑ i : Fin 8, c.χ i (ConjClasses.mk x) * star (c.χ i (ConjClasses.mk x)) = 48
  simp only [c.involution_values]
  norm_num [Fin.sum_univ_succ, map_ofNat]

/-- Compatibility with the proved local column norm theorem fixes the
sum of squared local principal-block degrees, without a core-free hypothesis. -/
public theorem local_degree_square_sum (hx : orderOf x = 2) :
    ∑ j ∈ (localData c.blockData (Subgroup.centralizer ({x} : Set G))).block,
      (localData c.blockData (Subgroup.centralizer ({x} : Set G))).chi j
        (ConjClasses.mk 1)^2 = 48 := by
  have hpow : x ^ (2^1) = 1 := by
    simpa only [pow_one, hx] using pow_orderOf_eq_one x
  rw [← ModularBlock.LocalColumnNorm.principalBlock_local_column_norm
    c.blockData x ⟨1, hpow⟩]
  exact c.involution_column_norm

end ThreePrincipalData
end
end ABG
