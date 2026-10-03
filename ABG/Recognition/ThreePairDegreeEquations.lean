module
public import ABG.Recognition.ThreeSignedDegrees
public import ABG.Recognition.ThreeInducedCharacters
public import Theory.Character.InvolutionSum

/-!
# Wong's two degree equations from actual involution pairs

Involution fusion and orbit–stabilizer evaluate the global character sums.
The actual GL₂(3) table evaluates the local sums and the pairings with Φ₁ and
Φ₄ as 2 and 4. Induction on roots preserves these pairings. Substituting the
signed degrees of the same seven-character decomposition and clearing their
nonzero denominators gives Wong's two integer equations.

Source: Wong (1964), Lemma 4(iii), pp.98–100, equations (9)–(10),
DOI 10.1017/S1446788700022771.
-/

namespace ABG
open BenderGlauberman Matrix Matrix.GeneralLinearGroup Theory.Character
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

/-- The actual local involution sums in Wong's row ordering. -/
public theorem glTwoThreeCharacter_involutionSum (i : Fin 8) :
    involutionSum (glTwoThreeCharacter i) = (![13,-11,2,-9,15,-4,-2,-2] i : ℂ) := by
  rw [involutionSum_eq_sum_ite, three_sum_classFunction _ (by
    intro a g
    have ho : orderOf (g * a * g⁻¹) = orderOf a :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
    simp only [ho, irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible i) a g])]
  simp_rw [three_conjugacy_data.2.1, glTwoThreeCharacter_values]
  fin_cases i <;> norm_num [Fin.sum_univ_succ, glTwoThreeCharacterTable]

variable {G : Type*} [Group G] [Finite G] (t : G)
  (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)

include e in
omit [Finite G] in
/-- The centralizer has its actual order, as supplied by its matrix equivalence. -/
public theorem threeCentralizer_card :
    Nat.card (Subgroup.centralizer ({t} : Set G)) = 48 := by
  change Nat.card (Subgroup.centralizer (Set.singleton t)) = 48
  rw [Nat.card_congr (threeCentralizerEquiv t e).toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_two]

/-- Transporting the local character table also transports its involution sums. -/
public theorem threeCentralizerCharacter_involutionSum (i : Fin 8) :
    involutionSum (threeCentralizerCharacter t e i) =
      (![13,-11,2,-9,15,-4,-2,-2] i : ℂ) :=
  (involutionSum_comp_mulEquiv (threeCentralizerEquiv t e) _).trans
    (glTwoThreeCharacter_involutionSum i)

private theorem local_irreducible_pairing (i : Fin 8) :
    scalarProduct (Subgroup.centralizer ({t} : Set G))
      (threeCentralizerCharacter t e i) (fun a => (involutionPairCount a : ℂ)) =
      (48 : ℂ)⁻¹ * (![13,-11,2,-9,15,-4,-2,-2] i : ℂ)^2 /
        (![1,1,2,3,3,4,2,2] i : ℂ) := by
  change scalarProduct (Subgroup.centralizer (Set.singleton t))
    (threeCentralizerCharacter t e i) (fun a => (involutionPairCount a : ℂ)) = _
  refine (scalarProduct_irreducible_involutionPairCount _
    (threeCentralizerCharacter_irreducible t e i)).trans ?_
  erw [threeCentralizer_card t e, threeCentralizerCharacter_involutionSum t e]
  have hd := threeCentralizerCharacter_values t e i 0
  change threeCentralizerCharacter t e i ((threeCentralizerEquiv t e).symm 1) = _ at hd
  rw [map_one] at hd
  rw [hd]
  congr 1
  fin_cases i <;> rfl

/-- The local Φ₁ pairing counts actual ordered pairs of involutions. -/
public theorem threeCentralizer_first_pairing :
    scalarProduct (Subgroup.centralizer ({t} : Set G))
      (threeCentralizerGenerator t e 0) (fun a => (involutionPairCount a : ℂ)) = 2 := by
  change scalarProduct _
    (threeCentralizerCharacter t e 0 + threeCentralizerCharacter t e 2 -
      threeCentralizerCharacter t e 4) _ = _
  rw [_root_.scalarProduct_sub_left, scalarProduct_add_left]
  erw [local_irreducible_pairing, local_irreducible_pairing, local_irreducible_pairing]
  change (48 : ℂ)⁻¹ * 13^2 / 1 + 48⁻¹ * 2^2 / 2 - 48⁻¹ * 15^2 / 3 = 2
  norm_num

/-- The local Φ₄ pairing counts actual ordered pairs of involutions. -/
public theorem threeCentralizer_fourth_pairing :
    scalarProduct (Subgroup.centralizer ({t} : Set G))
      (threeCentralizerGenerator t e 3) (fun a => (involutionPairCount a : ℂ)) = 4 := by
  change scalarProduct _
    (threeCentralizerCharacter t e 1 + threeCentralizerCharacter t e 4 -
      threeCentralizerCharacter t e 5) _ = _
  rw [_root_.scalarProduct_sub_left, scalarProduct_add_left]
  erw [local_irreducible_pairing, local_irreducible_pairing, local_irreducible_pairing]
  change (48 : ℂ)⁻¹ * (-11)^2 / 1 + 48⁻¹ * 15^2 / 3 - 48⁻¹ * (-4)^2 / 4 = 4
  norm_num

include e in
private theorem global_irreducible_pairing (ht : orderOf t = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u t)
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) :
    scalarProduct G χ (fun a => (involutionPairCount a : ℂ)) =
      (Nat.card G : ℂ) / 2304 * χ t ^ 2 / χ 1 := by
  refine (scalarProduct_irreducible_involutionPairCount χ hχ).trans ?_
  erw [involutionSum_of_fusion t ht hfuse χ (irreducibleCharacter_isClassFunction hχ),
    threeCentralizer_card t e]
  have hg : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  field_simp
  ring

private theorem global_signed_pairing (ht : orderOf t = 2)
    (hfuse : ∀ u : G, orderOf u = 2 → IsConj u t)
    (d : ThreeCharacterDecomposition (threeInducedGenerator t e)) (i : Fin 7) :
    scalarProduct G ((d.degreeSign i : ℂ) • d.χ i)
      (fun a => (involutionPairCount a : ℂ)) =
      (Nat.card G : ℂ) / 2304 * (![2,3,-2,-2,1,4,-3] i : ℂ)^2 /
        (d.signedDegree i : ℂ) := by
  rw [scalarProduct_smul_left]
  erw [global_irreducible_pairing t e ht hfuse _ (d.irreducible i)]
  rw [d.signedDegree_eq, ← threeInduced_signed_involution_vector t ht e d i]
  rcases d.degreeSign_unit i with h | h <;> simp only [h, Int.cast_one, Int.cast_neg]
  · ring
  · simp only [neg_one_mul, neg_sq, div_neg]

private theorem involution_fusion [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (ht : orderOf t = 2) (u : G) (hu : orderOf u = 2) : IsConj u t := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hcov⟩ := hclass
  obtain ⟨i, hi⟩ := hcov u hu
  obtain ⟨j, hj⟩ := hcov t ht
  exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)

/-- Wong's two rational identities, derived from Φ₁ and Φ₄ and actual
involution-pair counts, for the supplied seven-character decomposition. -/
public theorem threeInduced_pairing_degree_identities [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (ht : orderOf t = 2)
    (d : ThreeCharacterDecomposition (threeInducedGenerator t e)) :
    let x : ℂ := d.signedDegree 0
    let y : ℂ := d.signedDegree 5
    (Nat.card G : ℂ) / 2304 * (1 + 4 / x - 9 / (x + 1)) = 2 ∧
    (Nat.card G : ℂ) / 2304 * (9 / (x + 1) - 1 / (x + y + 1) + 16 / y) = 4 := by
  dsimp only
  have hfuse := involution_fusion t S hS ht
  have h0 := scalarProduct_induced_involutionPairCount t ht
    (threeCentralizerGenerator t e 0) (threeCentralizerGenerator_supported t ht e 0)
  have h3 := scalarProduct_induced_involutionPairCount t ht
    (threeCentralizerGenerator t e 3) (threeCentralizerGenerator_supported t ht e 3)
  change scalarProduct G (threeInducedGenerator t e 0) _ = _ at h0
  change scalarProduct G (threeInducedGenerator t e 3) _ = _ at h3
  erw [threeCentralizer_first_pairing t e] at h0
  erw [threeCentralizer_fourth_pairing t e] at h3
  rw [d.first, smul_sub, scalarProduct_add_left, _root_.scalarProduct_sub_left] at h0
  rw [d.fourth, scalarProduct_add_left, scalarProduct_add_left] at h3
  have htriv := global_irreducible_pairing t e ht hfuse 1 isLinearCharacter_one.1
  have hp (i : Fin 7) := global_signed_pairing t e ht hfuse d i
  have hp0 := hp 0
  have hp1 := hp 1
  have hp4 := hp 4
  have hp5 := hp 5
  simp only [ThreeCharacterDecomposition.degreeSign, Matrix.cons_val] at hp0 hp1 hp4 hp5
  rw [htriv, hp0, hp1] at h0
  rw [hp1, hp4, hp5] at h3
  have hd1 := congrFun (threeInduced_signed_degree_vector t ht e d) 1
  have hd4 := congrFun (threeInduced_signed_degree_vector t ht e d) 4
  simp only [Matrix.cons_val] at hd1 hd4
  rw [hd1] at h0 h3
  rw [hd4] at h3
  push_cast at h0 h3
  norm_num only [Pi.one_apply, one_pow, div_one, Matrix.cons_val, pow_one,
    show (2 : ℂ)^2 = 4 by norm_num, show (3 : ℂ)^2 = 9 by norm_num,
    show (4 : ℂ)^2 = 16 by norm_num] at h0 h3
  constructor
  · linear_combination h0
  · have hn : (-(d.signedDegree 0 : ℂ) - d.signedDegree 5 - 1) =
        -((d.signedDegree 0 : ℂ) + d.signedDegree 5 + 1) := by ring
    rw [hn, div_neg] at h3
    linear_combination h3

private theorem pairing_identities_polynomial (g x y : ℂ)
    (hg : g ≠ 0) (hx : x ≠ 0) (hxp : x + 1 ≠ 0)
    (hy : y ≠ 0) (hz : x + y + 1 ≠ 0)
    (hA : g / 2304 * (1 + 4 / x - 9 / (x + 1)) = 2)
    (hB : g / 2304 * (9 / (x + 1) - 1 / (x + y + 1) + 16 / y) = 4) :
    g * (x - 2)^2 = 4608*x*(x+1) ∧
    y^2*(2*x-1)*(x-8) + 2*y*(x+1)*(x^2-16*x+4) - 16*x*(x+1)^2 = 0 := by
  have hrel : (9 / (x + 1) - 1 / (x + y + 1) + 16 / y) =
      2 * (1 + 4 / x - 9 / (x + 1)) := by
    apply mul_left_cancel₀ (div_ne_zero hg (by norm_num : (2304 : ℂ) ≠ 0))
    linear_combination hB - 2 * hA
  constructor
  · field_simp at hA
    linear_combination hA
  · field_simp at hrel
    linear_combination -hrel

/-- Both of Wong's integer degree equations concern the same actual character
catalog. Nonzero denominators follow from its positive natural degrees; every
character and counting input is derived above. The argument applies in
particular to the original Sylow-order-16 hypotheses. -/
public theorem threeInduced_pair_degree_equations [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (ht : orderOf t = 2)
    (d : ThreeCharacterDecomposition (threeInducedGenerator t e)) :
    let x : ℤ := d.signedDegree 0
    let y : ℤ := d.signedDegree 5
    (Nat.card G : ℤ) * (x - 2)^2 = 4608*x*(x+1) ∧
    y^2*(2*x-1)*(x-8) + 2*y*(x+1)*(x^2-16*x+4) - 16*x*(x+1)^2 = 0 := by
  dsimp only
  have hd1 := congrFun (threeInduced_signed_degree_vector t ht e d) 1
  have hd4 := congrFun (threeInduced_signed_degree_vector t ht e d) 4
  change d.signedDegree 1 = d.signedDegree 0 + 1 at hd1
  change d.signedDegree 4 = -d.signedDegree 0 - d.signedDegree 5 - 1 at hd4
  have hg : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hx : (d.signedDegree 0 : ℂ) ≠ 0 := by exact_mod_cast d.signedDegree_ne_zero 0
  have hy : (d.signedDegree 5 : ℂ) ≠ 0 := by exact_mod_cast d.signedDegree_ne_zero 5
  have hxp : (d.signedDegree 0 : ℂ) + 1 ≠ 0 := by
    have hh : d.signedDegree 0 + 1 ≠ 0 := hd1 ▸ d.signedDegree_ne_zero 1
    exact_mod_cast hh
  have hz : (d.signedDegree 0 : ℂ) + d.signedDegree 5 + 1 ≠ 0 := by
    have hh : d.signedDegree 0 + d.signedDegree 5 + 1 ≠ 0 := by
      have hn := d.signedDegree_ne_zero 4
      rw [hd4] at hn
      omega
    exact_mod_cast hh
  obtain ⟨hA, hB⟩ := threeInduced_pairing_degree_identities t e S hS ht d
  obtain ⟨heq, hpoly⟩ := pairing_identities_polynomial (Nat.card G)
    (d.signedDegree 0) (d.signedDegree 5) hg hx hxp hy hz hA hB
  constructor
  · exact_mod_cast heq
  · exact_mod_cast hpoly

/-- Wong's equation (9), with `x` the first actual signed degree. -/
public theorem threeInduced_first_degree_equation [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (ht : orderOf t = 2)
    (d : ThreeCharacterDecomposition (threeInducedGenerator t e)) :
    (Nat.card G : ℤ) * (d.signedDegree 0 - 2)^2 =
      4608*d.signedDegree 0*(d.signedDegree 0+1) :=
  (threeInduced_pair_degree_equations t e S hS ht d).1

/-- Eliminating the group order gives Wong's equation for the sixth signed degree. -/
public theorem threeInduced_second_degree_equation [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (ht : orderOf t = 2)
    (d : ThreeCharacterDecomposition (threeInducedGenerator t e)) :
    let x : ℤ := d.signedDegree 0
    let y : ℤ := d.signedDegree 5
    y^2*(2*x-1)*(x-8) + 2*y*(x+1)*(x^2-16*x+4) - 16*x*(x+1)^2 = 0 :=
  (threeInduced_pair_degree_equations t e S hS ht d).2

end
end ABG
