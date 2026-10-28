module
public import ABG.Recognition.ThreeCentralizerCharacters
public import ABG.Recognition.ThreeCharacterDecomposition

/-!
# Ordinary restrictions of Wong's distinguished characters

Frobenius reciprocity determines the scalar products of the restrictions with
the five supported generators. Their orthogonal complement vanishes on roots
of the central involution. Thus the signed restrictions of the first and sixth
characters are determined on that support, before resolving any signs or
degrees. In particular their values on the involution are 2ε and 4ε₂.

Source: Wong (1964), Appendix, p.106, equation (12). This argument uses only
ordinary characters and applies to the same witnesses as the induction data.
-/

namespace ABG
open BenderGlauberman Matrix.GeneralLinearGroup
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Group G] [Finite G] (t : G) (ht : orderOf t = 2)
  (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
  (d : ThreeCharacterDecomposition (threeInducedGenerator t e))

private theorem centralizer_orthonormal (i j : Fin 8) :
    scalarProduct (Subgroup.centralizer ({t} : Set G))
      (threeCentralizerCharacter t e i) (threeCentralizerCharacter t e j) =
      if i = j then 1 else 0 :=
  (scalarProduct_comp_mulEquiv (threeCentralizerEquiv t e) _ _).trans
    (glTwoThreeCharacter_orthonormal i j)

omit [Finite G] in
private theorem generator_eq (k : Fin 5) :
    threeCentralizerGenerator t e k =
      ![threeCentralizerCharacter t e 0 + threeCentralizerCharacter t e 2 -
          threeCentralizerCharacter t e 4,
        threeCentralizerCharacter t e 2 - threeCentralizerCharacter t e 6,
        threeCentralizerCharacter t e 6 - threeCentralizerCharacter t e 7,
        threeCentralizerCharacter t e 1 + threeCentralizerCharacter t e 4 -
          threeCentralizerCharacter t e 5,
        threeCentralizerCharacter t e 1 + threeCentralizerCharacter t e 2 -
          threeCentralizerCharacter t e 3] k := by
  fin_cases k <;> rfl

include ht in
/-- Equality of the five ordinary restriction coefficients determines the
restriction on the roots of the distinguished involution. -/
public theorem threeInduced_restriction_eq_of_coefficients
    {χ : ClassFunction G} (hχ : IsClassFunction χ)
    {f : ClassFunction (Subgroup.centralizer ({t} : Set G))} (hf : IsClassFunction f)
    (hcoeff : ∀ k : Fin 5, scalarProduct G χ (threeInducedGenerator t e k) =
      scalarProduct (Subgroup.centralizer ({t} : Set G)) f (threeCentralizerGenerator t e k))
    (a : Subgroup.centralizer ({t} : Set G)) (ha : t ∈ Subgroup.zpowers (a : G)) :
    χ a = f a := by
  apply sub_eq_zero.mp
  apply threeCentralizer_orthogonal_vanishes t ht e
    (show IsClassFunction ((fun a : Subgroup.centralizer ({t} : Set G) => χ (a : G)) - f) from
      fun x g => by simp only [Pi.sub_apply, Subgroup.coe_mul, Subgroup.coe_inv, hχ (x : G) (g : G), hf x g])
    (fun k => ?_) a ha
  rw [_root_.scalarProduct_sub_left]
  apply sub_eq_zero.mpr
  exact (scalarProduct_restrict_induced (Subgroup.centralizer ({t} : Set G)) hχ _).trans
    (hcoeff k)

private theorem signed_first_coeff (k : Fin 5) :
    scalarProduct G ((d.sign 0 : ℂ) • d.χ 0) (threeInducedGenerator t e k) =
      ![1,1,0,0,1] k := by
  have ho (j : Fin 7) : scalarProduct G (d.χ 0) (d.χ j) = if j = 0 then 1 else 0 := by
    by_cases h : j = 0
    · subst j; simp [irreducible_scalarProduct_self (d.irreducible 0)]
    · rw [if_neg h]
      exact irreducible_scalarProduct_of_ne (d.irreducible 0) (d.irreducible j)
        (fun hh => h (d.distinct hh).symm)
  have h1 : scalarProduct G (d.χ 0) 1 = 0 :=
    irreducible_scalarProduct_of_ne (d.irreducible 0) isLinearCharacter_one.1 (d.nontrivial 0)
  fin_cases k <;> rcases d.sign_unit 0 with hs | hs <;>
    simp [d.first, d.second, d.third, d.fourth, d.fifth,
      scalarProduct_smul_right, scalarProduct_add_right,
      scalarProduct_sub_right, scalarProduct_neg_left, scalarProduct_neg_right, star_intCast, ho, h1, hs]

private theorem signed_sixth_coeff (k : Fin 5) :
    scalarProduct G ((d.sign 2 : ℂ) • d.χ 5) (threeInducedGenerator t e k) =
      ![0,0,0,1,0] k := by
  have ho (j : Fin 7) : scalarProduct G (d.χ 5) (d.χ j) = if j = 5 then 1 else 0 := by
    by_cases h : j = 5
    · subst j; simp [irreducible_scalarProduct_self (d.irreducible 5)]
    · rw [if_neg h]
      exact irreducible_scalarProduct_of_ne (d.irreducible 5) (d.irreducible j)
        (fun hh => h (d.distinct hh).symm)
  have h1 : scalarProduct G (d.χ 5) 1 = 0 :=
    irreducible_scalarProduct_of_ne (d.irreducible 5) isLinearCharacter_one.1 (d.nontrivial 5)
  fin_cases k <;> rcases d.sign_unit 2 with hs | hs <;>
    simp [d.first, d.second, d.third, d.fourth, d.fifth,
      scalarProduct_smul_right, scalarProduct_add_right,
      scalarProduct_sub_right, scalarProduct_neg_left, scalarProduct_neg_right, star_intCast, ho, h1, hs]

include ht in
/-- Equation (12) for the first character, with its original sign retained. -/
public theorem threeInduced_first_restriction
    (a : Subgroup.centralizer ({t} : Set G)) (ha : t ∈ Subgroup.zpowers (a : G)) :
    (d.sign 0 : ℂ) * d.χ 0 a = threeCentralizerCharacter t e 0 a -
      threeCentralizerCharacter t e 3 a - threeCentralizerCharacter t e 6 a -
      threeCentralizerCharacter t e 7 a := by
  have hc (i : Fin 8) := irreducibleCharacter_isClassFunction (threeCentralizerCharacter_irreducible t e i)
  apply threeInduced_restriction_eq_of_coefficients t ht e
    (χ := (d.sign 0 : ℂ) • d.χ 0)
    (f := threeCentralizerCharacter t e 0 - threeCentralizerCharacter t e 3 -
      threeCentralizerCharacter t e 6 - threeCentralizerCharacter t e 7)
    (by intro x g; simp only [Pi.smul_apply, smul_eq_mul,
          irreducibleCharacter_isClassFunction (d.irreducible 0) x g])
    (by intro x g; simp only [Pi.sub_apply, hc 0 x g, hc 3 x g, hc 6 x g, hc 7 x g]) _ a ha
  intro k
  rw [signed_first_coeff t e d]
  fin_cases k <;>
    simp [generator_eq, _root_.scalarProduct_sub_left, scalarProduct_add_right,
      scalarProduct_sub_right, centralizer_orthonormal, Matrix.cons_val, Fin.reduceFinMk]

include ht in
/-- Equation (12) for the sixth character, with its original sign retained. -/
public theorem threeInduced_sixth_restriction
    (a : Subgroup.centralizer ({t} : Set G)) (ha : t ∈ Subgroup.zpowers (a : G)) :
    (d.sign 2 : ℂ) * d.χ 5 a = -threeCentralizerCharacter t e 5 a := by
  apply threeInduced_restriction_eq_of_coefficients t ht e
    (χ := (d.sign 2 : ℂ) • d.χ 5) (f := -threeCentralizerCharacter t e 5)
    (by intro x g; simp only [Pi.smul_apply, smul_eq_mul,
          irreducibleCharacter_isClassFunction (d.irreducible 5) x g])
    (by intro x g; simp only [Pi.neg_apply,
          irreducibleCharacter_isClassFunction (threeCentralizerCharacter_irreducible t e 5) x g]) _ a ha
  intro k
  rw [signed_sixth_coeff t e d]
  fin_cases k <;>
    simp [generator_eq, scalarProduct_neg_left, scalarProduct_add_right,
      scalarProduct_sub_right, centralizer_orthonormal, Matrix.cons_val, Fin.reduceFinMk]

include ht in
/-- The signed first character at each of the five root classes. -/
public theorem threeInduced_first_root_values (j : Fin 8)
    (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7) :
    (d.sign 0 : ℂ) * d.χ 0
      ((threeCentralizerEquiv t e).symm (threeClassRepr j)) =
        (![0,2,2,0,-1,0,0,0] j : ℂ) := by
  have ha := (threeCentralizerEquiv_root_iff t ht e
    ((threeCentralizerEquiv t e).symm (threeClassRepr j))).mp
      (by simpa only [MulEquiv.apply_symm_apply, glTwoThreeRootSupport_class] using hj)
  rw [threeInduced_first_restriction t ht e d _ ha]
  simp only [threeCentralizerCharacter_values]
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · change (1 : ℂ) - 3 - (-2) - (-2) = 2; norm_num
  · change (1 : ℂ) - (-1) - 0 - 0 = 2; norm_num
  · change (1 : ℂ) - 0 - 1 - 1 = -1; norm_num
  · change (1 : ℂ) - 1 - glTwoThreeOmega - (-glTwoThreeOmega) = 0; ring
  · change (1 : ℂ) - 1 - (-glTwoThreeOmega) - glTwoThreeOmega = 0; ring

include ht in
/-- The signed sixth character at each of the five root classes. -/
public theorem threeInduced_sixth_root_values (j : Fin 8)
    (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7) :
    (d.sign 2 : ℂ) * d.χ 5
      ((threeCentralizerEquiv t e).symm (threeClassRepr j)) =
        (![0,4,0,0,1,0,0,0] j : ℂ) := by
  have ha := (threeCentralizerEquiv_root_iff t ht e
    ((threeCentralizerEquiv t e).symm (threeClassRepr j))).mp
      (by simpa only [MulEquiv.apply_symm_apply, glTwoThreeRootSupport_class] using hj)
  rw [threeInduced_sixth_restriction t ht e d _ ha]
  simp only [threeCentralizerCharacter_values]
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · change -(-4 : ℂ) = 4; norm_num
  · change -(0 : ℂ) = 0; norm_num
  · change -(-1 : ℂ) = 1; norm_num
  · change -(0 : ℂ) = 0; norm_num
  · change -(0 : ℂ) = 0; norm_num

include ht in
/-- The two distinguished signed involution values, derived from ordinary
restriction coefficients rather than modular decomposition numbers. -/
public theorem threeInduced_distinguished_involution_values :
    (d.sign 0 : ℂ) * d.χ 0 t = 2 ∧ (d.sign 2 : ℂ) * d.χ 5 t = 4 := by
  have ht' : (threeCentralizerEquiv t e).symm (threeClassRepr 1) =
      ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
    apply (threeCentralizerEquiv t e).injective
    rw [MulEquiv.apply_symm_apply, threeCentralizerEquiv_involution t ht e]
    rfl
  have h1 := threeInduced_first_root_values t ht e d 1 (Or.inl rfl)
  have h6 := threeInduced_sixth_root_values t ht e d 1 (Or.inl rfl)
  rw [ht'] at h1 h6
  exact ⟨h1, h6⟩

end
end ABG
