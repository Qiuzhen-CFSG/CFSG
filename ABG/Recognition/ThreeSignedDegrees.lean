module
public import ABG.Recognition.ThreeCharacterRestrictions

/-!
# The actual degrees in Wong's seven-character catalog

The degree witnesses are natural numbers evaluating the same irreducible
characters that occur in the five induction identities. Evaluation at the
identity gives their signed degree vector in terms of its first and sixth
entries. The first signed degree is congruent to 2 modulo 8, using the integral
ordinary restriction to GL₂(3) and the two order-eight columns.

Source: Wong (1964), pp.100–101 and Appendix p.106.
-/

namespace ABG
open BenderGlauberman Matrix.GeneralLinearGroup
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace ThreeCharacterDecomposition
variable {G : Type*} [Group G] {Ψ : Fin 5 → ClassFunction G}

/-- The natural degree of each of the seven actual irreducible characters. -/
public def degree (d : ThreeCharacterDecomposition Ψ) (i : Fin 7) : ℕ :=
  Classical.choose (d.irreducible i)

public theorem degree_eq (d : ThreeCharacterDecomposition Ψ) (i : Fin 7) :
    d.χ i 1 = (d.degree i : ℂ) := by
  obtain ⟨ρ, _, hρ⟩ := Classical.choose_spec (d.irreducible i)
  simp [hρ, Representation.char_one, degree]

public theorem degree_pos (d : ThreeCharacterDecomposition Ψ) (i : Fin 7) :
    0 < d.degree i := by
  have h := irreducible_degree_ge_one (d.irreducible i)
  rw [d.degree_eq i] at h
  have : 1 ≤ d.degree i := by exact_mod_cast h
  omega

/-- Wong's signs attached to the seven entries, in the original indexing. -/
@[expose] public def degreeSign (d : ThreeCharacterDecomposition Ψ) (i : Fin 7) : ℤ :=
  d.sign (![0,0,0,0,1,2,3] i)

public theorem degreeSign_unit (d : ThreeCharacterDecomposition Ψ) (i : Fin 7) :
    d.degreeSign i = 1 ∨ d.degreeSign i = -1 := d.sign_unit _

/-- The signed degree, explicitly tied to the actual character and sign. -/
@[expose] public def signedDegree (d : ThreeCharacterDecomposition Ψ) (i : Fin 7) : ℤ :=
  d.degreeSign i * (d.degree i : ℤ)

public theorem signedDegree_eq (d : ThreeCharacterDecomposition Ψ) (i : Fin 7) :
    (d.signedDegree i : ℂ) = (d.degreeSign i : ℂ) * d.χ i 1 := by
  simp [signedDegree, d.degree_eq]

public theorem signedDegree_ne_zero (d : ThreeCharacterDecomposition Ψ) (i : Fin 7) :
    d.signedDegree i ≠ 0 := by
  rcases d.degreeSign_unit i with he | he <;> simp [signedDegree, he, (d.degree_pos i).ne']

end ThreeCharacterDecomposition

variable {G : Type*} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
  (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
  (d : ThreeCharacterDecomposition (threeInducedGenerator t e))

include ht in
/-- The signed degree vector follows by evaluating the five actual induced
characters at the identity. No degree equations are assumed. -/
public theorem threeInduced_signed_degree_vector :
    d.signedDegree =
      ![d.signedDegree 0, d.signedDegree 0 + 1, d.signedDegree 0,
        d.signedDegree 0, -d.signedDegree 0 - d.signedDegree 5 - 1,
        d.signedDegree 5, d.signedDegree 5 + 1] := by
  have h0 := congrFun d.first 1
  have h1 := congrFun d.second 1
  have h2 := congrFun d.third 1
  have h3 := congrFun d.fourth 1
  have h4 := congrFun d.fifth 1
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
    threeInducedGenerator_one t ht e] at h0 h1 h2 h3 h4
  have hs (i : Fin 7) := d.signedDegree_eq i
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hs3 := hs 3
  have hs4 := hs 4
  have hs5 := hs 5
  have hs6 := hs 6
  simp only [ThreeCharacterDecomposition.degreeSign, Matrix.cons_val]
    at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  have hv1 : (d.signedDegree 1 : ℂ) = d.signedDegree 0 + 1 := by
    linear_combination h0 + hs1 - hs0
  have hv2 : (d.signedDegree 2 : ℂ) = d.signedDegree 0 := by
    linear_combination h1 + hs2 - hs0
  have hv3 : (d.signedDegree 3 : ℂ) = d.signedDegree 0 := by
    linear_combination h1 + h2 + hs3 - hs0
  have hv4 : (d.signedDegree 4 : ℂ) = -d.signedDegree 0 - d.signedDegree 5 - 1 := by
    linear_combination -h3 - h0 + hs4 + hs5 + hs0
  have hv6 : (d.signedDegree 6 : ℂ) = d.signedDegree 5 + 1 := by
    linear_combination -h4 + h3 + h0 + hs6 - hs5
  have hv1' : d.signedDegree 1 = d.signedDegree 0 + 1 := by exact_mod_cast hv1
  have hv2' : d.signedDegree 2 = d.signedDegree 0 := by exact_mod_cast hv2
  have hv3' : d.signedDegree 3 = d.signedDegree 0 := by exact_mod_cast hv3
  have hv4' : d.signedDegree 4 = -d.signedDegree 0 - d.signedDegree 5 - 1 := by
    exact_mod_cast hv4
  have hv6' : d.signedDegree 6 = d.signedDegree 5 + 1 := by exact_mod_cast hv6
  funext i
  fin_cases i <;> simp [Matrix.cons_val, Fin.reduceFinMk, hv1', hv2', hv3', hv4', hv6']

private theorem local_degree_congruence
    {f : ClassFunction (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))}
    (hf : IsGeneralizedCharacter f) (n s : ℤ)
    (hn : f 1 = (n : ℂ)) (ht : f threeCentral = (2 * s : ℤ))
    (h6 : f (threeClassRepr 6) = 0) (h7 : f (threeClassRepr 7) = 0) :
    8 ∣ n - 2 * s := by
  obtain ⟨m, hm⟩ := glTwoThreeCharacter_integral_expansion hf
  have hv (j : Fin 8) := congrFun hm (threeClassRepr j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, glTwoThreeCharacter_values] at hv
  have h0 := hv 0
  have h1 := hv 1
  have ha := hv 6
  have hb := hv 7
  rw [h6] at ha
  rw [h7] at hb
  change f 1 = _ at h0
  change f threeCentral = _ at h1
  rw [hn] at h0
  rw [ht] at h1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h0 h1 ha hb
  change (n : ℂ) = m 0 * 1 + (m 1 * 1 + (m 2 * 2 + (m 3 * 3 +
    (m 4 * 3 + (m 5 * 4 + (m 6 * 2 + m 7 * 2)))))) at h0
  change ((2 * s : ℤ) : ℂ) = m 0 * 1 + (m 1 * 1 + (m 2 * 2 + (m 3 * 3 +
    (m 4 * 3 + (m 5 * (-4) + (m 6 * (-2) + m 7 * (-2))))))) at h1
  change (0 : ℂ) = m 0 * 1 + (m 1 * (-1) + (m 2 * 0 + (m 3 * 1 +
    (m 4 * (-1) + (m 5 * 0 + (m 6 * glTwoThreeOmega + m 7 * (-glTwoThreeOmega))))))) at ha
  change (0 : ℂ) = m 0 * 1 + (m 1 * (-1) + (m 2 * 0 + (m 3 * 1 +
    (m 4 * (-1) + (m 5 * 0 + (m 6 * (-glTwoThreeOmega) + m 7 * glTwoThreeOmega)))))) at hb
  have hw : glTwoThreeOmega ≠ 0 := by
    intro h
    have := glTwoThreeOmega_sq
    norm_num [h] at this
  have hm67 : (m 6 : ℂ) = m 7 := by
    have hh : ((m 6 : ℂ) - m 7) * (2 * glTwoThreeOmega) = 0 := by
      linear_combination hb - ha
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (mul_ne_zero (by norm_num) hw))
  have he : (n : ℂ) - 2 * s = 8 * ((m 5 : ℂ) + m 6) := by
    push_cast at h1
    linear_combination h0 - h1 - 4 * hm67
  have he' : n - 2 * s = 8 * (m 5 + m 6) := by exact_mod_cast he
  exact ⟨m 5 + m 6, he'⟩

include ht in
/-- The order-eight columns of the ordinary restriction give the required
congruence for the signed degree of the first actual character. -/
public theorem threeInduced_signed_degree_congruence : 8 ∣ d.signedDegree 0 - 2 := by
  let f : ClassFunction (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    fun a => d.χ 0 ((threeCentralizerEquiv t e).symm a)
  have hf : IsCharacter f := isCharacter_comp_hom
    (((Subgroup.centralizer ({t} : Set G)).subtype).comp
      (threeCentralizerEquiv t e).symm.toMonoidHom)
      (isCharacter_of_isIrreducibleCharacter (d.irreducible 0))
  have hg : IsGeneralizedCharacter f := ⟨f, 0, hf, isCharacter_zero, by simp⟩
  have h0 : f 1 = (d.degree 0 : ℂ) := by
    simpa only [f, map_one, Subgroup.coe_one] using d.degree_eq 0
  have h1 := threeInduced_first_root_values t ht e d 1 (Or.inl rfl)
  have h6 := threeInduced_first_root_values t ht e d 6 (by simp)
  have h7 := threeInduced_first_root_values t ht e d 7 (by simp)
  change (d.sign 0 : ℂ) * f threeCentral = 2 at h1
  change (d.sign 0 : ℂ) * f (threeClassRepr 6) = 0 at h6
  change (d.sign 0 : ℂ) * f (threeClassRepr 7) = 0 at h7
  have hs : (d.sign 0 : ℂ) ≠ 0 := by
    rcases d.sign_unit 0 with h | h <;> simp [h]
  have ha := (mul_eq_zero.mp h6).resolve_left hs
  have hb := (mul_eq_zero.mp h7).resolve_left hs
  have htval : f threeCentral = ((2 * d.sign 0 : ℤ) : ℂ) := by
    rcases d.sign_unit 0 with h | h
    · simpa only [h, Int.cast_one, one_mul, mul_one, Int.cast_ofNat] using h1
    · simp only [h, Int.cast_neg, Int.cast_one, neg_one_mul] at h1
      norm_num only [h, mul_neg, mul_one, Int.cast_neg, Int.cast_ofNat]
      linear_combination -h1
  have hd := local_degree_congruence hg (d.degree 0) (d.sign 0) h0 htval ha hb
  rcases d.sign_unit 0 with h | h
  · simpa [ThreeCharacterDecomposition.signedDegree, ThreeCharacterDecomposition.degreeSign,
      h] using hd
  · have hh := dvd_neg.mpr hd
    simpa [ThreeCharacterDecomposition.signedDegree, ThreeCharacterDecomposition.degreeSign,
      h, sub_eq_add_neg, add_comm] using hh

include ht in
/-- All seven signed involution values belong to the same character catalog. -/
public theorem threeInduced_signed_involution_vector (i : Fin 7) :
    (d.degreeSign i : ℂ) * d.χ i t = (![2,3,-2,-2,1,4,-3] i : ℂ) := by
  obtain ⟨hv0, hv5⟩ := threeInduced_distinguished_involution_values t ht e d
  let a : Subgroup.centralizer ({t} : Set G) :=
    ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hg (k : Fin 5) : threeInducedGenerator t e k t = (![0,4,0,8,0] k : ℂ) := by
    have h := threeInducedGenerator_apply_root t ht e k a (Subgroup.mem_zpowers t)
    change threeInducedGenerator t e k t = _ at h
    rw [h]
    change glTwoThreeSupportedGenerator k (threeCentralizerEquiv t e a) = _
    rw [threeCentralizerEquiv_involution t ht e]
    have hh := glTwoThreeSupportedGenerator_values k 1
    change glTwoThreeSupportedGenerator k threeCentral = _ at hh
    rw [hh]
    fin_cases k <;> rfl
  have h0 := congrFun d.first t
  have h1 := congrFun d.second t
  have h2 := congrFun d.third t
  have h3 := congrFun d.fourth t
  have h4 := congrFun d.fifth t
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, hg]
    at h0 h1 h2 h3 h4
  change (0 : ℂ) = 1 + (d.sign 0 : ℂ) * (d.χ 0 t - d.χ 1 t) at h0
  change (4 : ℂ) = (d.sign 0 : ℂ) * (d.χ 0 t - d.χ 2 t) at h1
  change (0 : ℂ) = (d.sign 0 : ℂ) * (d.χ 2 t - d.χ 3 t) at h2
  change (8 : ℂ) = (d.sign 0 : ℂ) * d.χ 1 t + (d.sign 1 : ℂ) * d.χ 4 t +
    (d.sign 2 : ℂ) * d.χ 5 t at h3
  change (0 : ℂ) = (d.sign 0 : ℂ) * d.χ 0 t + (d.sign 1 : ℂ) * d.χ 4 t +
    (d.sign 3 : ℂ) * d.χ 6 t at h4
  have hv1 : (d.sign 0 : ℂ) * d.χ 1 t = 3 := by
    linear_combination h0 + hv0
  have hv2 : (d.sign 0 : ℂ) * d.χ 2 t = -2 := by
    linear_combination h1 + hv0
  have hv3 : (d.sign 0 : ℂ) * d.χ 3 t = -2 := by
    linear_combination h2 + hv2
  have hv4 : (d.sign 1 : ℂ) * d.χ 4 t = 1 := by
    linear_combination -h3 - hv1 - hv5
  have hv6 : (d.sign 3 : ℂ) * d.χ 6 t = -3 := by
    linear_combination -h4 - hv0 - hv4
  fin_cases i
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3
  · exact hv4
  · exact hv5
  · exact hv6

end
end ABG
